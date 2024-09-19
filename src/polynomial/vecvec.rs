use std::cmp::min;
use std::fmt::{Debug, Formatter, Write};
use std::iter::repeat;
use std::ops::{Add, AddAssign, Mul, Sub, SubAssign};
use std::process::Output;
use std::sync::Arc;
use ark_ff::{Field, PrimeField};
use ark_std::rand::{Rng, RngCore};
use itertools::{repeat_n, Either, Itertools};
use rayon::prelude::*;

pub struct VecVecPolynomial<F, const N_POLYS: usize> {
    pub data: Vec<Vec<F>>,  // Actually Vec<Vec<[F; N_POLYS]>>
    /// Each row is padded to 1 << *row_logsize* by corresponding *row_pad*
    pub row_pad: [F; N_POLYS],
    /// Concatenation of padded rows padded to 1 << *col_logsize* by *col_pad* represents *N_POLYS* polynomials interleaved with each other.
    pub col_pad: F,
    /// the least significant *row_logsize* coordinates are thought as index in bucket; these are coordinates we will run sumcheck over
    pub row_logsize: usize,
    /// the most significant *col_logsize* coordinates are thought as bucket indexes; It is impossible to sumcheck by them
    pub col_logsize: usize,
}

impl<F: Clone + Debug, const N_POLYS: usize> Debug for VecVecPolynomial<F, N_POLYS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut res = vec![];
        let vecs = self.vec();
        for r in 0..(1 << self.col_logsize) {
            let mut row = vec![];
            for c in 0..(1 << self.row_logsize) {
                let mut bundle = vec![];
                for v in &vecs {
                    bundle.push(v[r * (1 << self.row_logsize) + c].clone());
                }
                row.push(bundle);
            }
            res.push(row);
        }
        f.write_str(&format!("{:?}", res))
    }
}


impl<F: Clone, const N_POLYS: usize> VecVecPolynomial<F, N_POLYS> {
    pub fn new(mut data: Vec<Vec<F>>, row_pad: [F; N_POLYS], col_pad: F, row_logsize: usize, col_logsize: usize) -> Self {
        assert!(data.len() <= (1 << col_logsize));
        data.iter_mut().map(|p| {
            assert_eq!(p.len() % N_POLYS, 0);
            assert!(p.len() / N_POLYS <= 1 << row_logsize);
            if (p.len() / N_POLYS) % 2 == 1 {
                p.extend(row_pad.clone());
            }
        }).count();

        Self {data, row_pad, col_pad, row_logsize, col_logsize }
    }
    pub fn new_unchecked(data: Vec<Vec<F>>, row_pad: [F; N_POLYS], col_pad: F, inner_exp: usize, total_exp: usize) -> Self {
        Self {data, row_pad, col_pad, row_logsize: inner_exp, col_logsize: total_exp }
    }

    pub fn num_vars(&self) -> usize {
        self.col_logsize + self.row_logsize
    }
}

impl<F: From<u64> + Clone, const N_POLYS: usize> VecVecPolynomial<F, N_POLYS> {
    pub fn rand<RNG: Rng>(rng: &mut RNG, row_logsize: usize, col_logsize: usize) -> Self {
        let data = (0..(rng.next_u64() as usize % (1 << col_logsize))).map(|_| {
            (0..N_POLYS * (rng.next_u64() as usize % (1 << row_logsize))).map(|_| F::from(rng.next_u64())).collect_vec()
        }).collect_vec();


        Self::new(
            data,
            (0..N_POLYS).map(|_| F::from(rng.next_u64())).collect_vec().try_into().unwrap_or_else(|_| panic!()),
            F::from(rng.next_u64()),
            row_logsize,
            col_logsize,
        )
    }
}

// Bind
impl<F: Field, const N_POLYS: usize> VecVecPolynomial<F, N_POLYS> {

    /// Example with N_POLYS = 1, col_logsize = 0
    /// transform p_00, p_01, p_10, p_11
    /// into      p_02, p_01, p_12, p_11
    ///
    /// Where p_*2 = 2 * p_*1 - p_*0
    pub fn make_21(&mut self) {
        // #[cfg(not(feature = "multicore"))]
        let iter = self.data.iter_mut();
        // #[cfg(feature = "multicore")]
        // let iter = self.data.par_iter_mut();

        iter
            .map(|r| {
                for i in 0..(r.len() / N_POLYS / 2) {
                    for j in 0..N_POLYS {
                        r[2 * i * N_POLYS + j] = r[(2 * i + 1) * N_POLYS + j].double() - r[2 * i * N_POLYS + j];
                    }
                }
            })
            .count();
    }

    /// Example with N_POLYS = 1, col_logsize = 0
    /// transform p_02, p_01, p_12, p_11
    /// into p_00 + t(p_01 - p_00), p_10 + t(p_11 - p_10)
    ///
    /// Where p_*2 = 2 * p_*1 - p_*0
    pub fn bind_21(&mut self, tm1: &F) {
        let iter = self.data.par_iter_mut();
        
        iter
            .map(|r| {
                for i in 0..(r.len() / N_POLYS / 2) {
                    for j in 0..N_POLYS {
                        r[i * N_POLYS + j] = F::add(
                            r[(2 * i + 1) * N_POLYS + j],
                            *tm1 * F::sub(
                                r[2 * i * N_POLYS + j],
                                r[(2 * i + 1) * N_POLYS + j]
                            )
                        );
                    }
                }
                let mut i = r.len() / N_POLYS / 2;
                if i > 1 && i % 2 == 1 {
                    r.extend(self.row_pad.clone());
                    i += 1;
                }
                r.truncate(i * N_POLYS);
            })
            .count();
        self.row_logsize -= 1;
    }
}

// Vec
impl<F: Clone, const N_POLYS: usize> VecVecPolynomial<F, N_POLYS> {
    pub fn vec(&self) -> [Vec<F>; N_POLYS] {
        let mut ret: Vec<Vec<F>> = vec![];
        for i in 0..N_POLYS {
            ret.push(vec![]);
        }
        for r in 0..(1 << self.col_logsize) {
            for c in 0..(1 << self.row_logsize) {
                for i in 0..N_POLYS {
                    if r >= self.data.len() {
                        ret[i].push(self.col_pad.clone());
                    } else if c * N_POLYS + i >= self.data[r].len() {
                        ret[i].push(self.row_pad[i].clone());
                    } else {
                        ret[i].push(self.data[r][c * N_POLYS + i].clone())
                    }
                }
            }
        }
        ret.try_into().unwrap_or_else(|_| panic!())
    }
}

impl<F, const N_POLYS: usize> VecVecPolynomial<F, N_POLYS> {

}

#[cfg(test)]
mod tests {
    // use ark_ed_on_bls12_381_bandersnatch::Fr;
    use ark_std::rand::Error;
    use ark_std::test_rng;
    use liblasso::poly::dense_mlpoly::DensePolynomial;
    use super::*;

    use ark_ff::fields::{MontConfig};
    use ark_ff::{Fp, MontBackend};

    #[derive(MontConfig)]
    #[modulus = "17"]
    #[generator = "3"]
    pub struct FqConfig;
    pub type Fq = Fp<MontBackend<FqConfig, 1>, 1>;

    #[test]
    fn bind() {
        // let x = <u64 as Field>::extension_degree();
        let gen = &mut test_rng();

        // let mut v = VecVecPolynomial::<Fq, 2>::rand(gen, 3, 2);
        let mut v = VecVecPolynomial::<Fq, 2>::new(
            vec![
                vec![Fq::from(1), Fq::from(2), Fq::from(3), Fq::from(4)],
                vec![Fq::from(5), Fq::from(6)],
            ],
            [Fq::from(7), Fq::from(8)],
            Fq::from(0),
            2,
            2,
        );
        // let t = Fq::from(gen.next_u64());
        let t = Fq::from(10);
        let [d1, d2] = v.vec();
        let [mut e1, mut e2] = [vec![], vec![]];
        v.make_21();
        v.bind_21(&(t - Fq::from(1)));
        for i in 0..(d1.len() / 2) {
            e1.push(d1[2 * i] + t * (d1[2 * i + 1] - d1[2 * i]));
            e2.push(d2[2 * i] + t * (d2[2 * i + 1] - d2[2 * i]));
        }
        let [b1, b2] = v.vec();
        assert_eq!(e1, b1);
        assert_eq!(e2, b2);
    }
}