use std::fmt::{Debug, Formatter, Write};
use std::ops::{Add, AddAssign, Mul, Range, Sub, SubAssign};
use std::slice::from_ref;
use ark_ec::twisted_edwards::{TECurveConfig, Projective};
use ark_ff::{Field, PrimeField};
use ark_std::rand::{Rng, RngCore};
use ark_std::UniformRand;
use itertools::Itertools;
use liblasso::utils::math::Math;
use num_traits::Zero;
use rayon::prelude::*;

use crate::utils::{eq_poly_sequence_from_multiplier, eq_poly_sequence_last};

pub struct EQPolyPointParts {
    pub padded_vars_idx: usize,
    pub segment_vars_idx: usize,
    pub binding_var_idx: usize
}

impl EQPolyPointParts {
    fn new<F>(point: &[F], col_logsize: usize, max_segment_logsize: usize) -> Self {
        let padded_vars_idx = col_logsize;
        let segment_vars_idx = point.len() - max_segment_logsize;
        let binding_var_idx = point.len() - 1;

        Self {
            padded_vars_idx,
            segment_vars_idx,
            binding_var_idx,
        }
    }

    fn bind(&mut self) {
        self.binding_var_idx -= 1
    }

    fn vertical_vars_range(&self) -> Range<usize> {
        0..self.padded_vars_idx
    }

    fn padded_vars_range(&self) -> Range<usize> {
        self.padded_vars_idx..self.segment_vars_idx.min(self.binding_var_idx)
    }

    fn segment_vars_range(&self) -> Range<usize> {
        self.segment_vars_idx..self.segment_vars_idx.max(self.binding_var_idx)
    }
}

pub struct EQPolyData<F> {
    // Some point parts accounting
    pub point_parts: EQPolyPointParts,
    pub point: Vec<F>,
    // Bound variables multiplier
    pub multiplier: F,
    // Coefficients for each row of matrix (corresponding to the most significant variables)
    pub row_eq_coefs: Vec<F>,
    // Evals in 0-point of EQ poly already bounded by some
    pub pad_multipliers: Vec<F>,
    // EQ polys materialized for the longest segment in each fold
    pub row_eq_poly_seq: Vec<Vec<F>>,
    // EQ polys prefix sums to multiply
    pub row_eq_poly_prefix_seq: Vec<Vec<F>>,
    // how many vars are already bound
    pub already_bound_vars: usize,
}

impl<F: PrimeField> EQPolyData<F> {
    fn new(point: &[F], col_logsize: usize, max_row_len: usize) -> Self {
        let max_segment_logsize = 1 << max_row_len.log_2();

        // variable parts
        let point_parts = EQPolyPointParts::new(point, col_logsize, max_segment_logsize);
        let point = point.to_vec();

        // this use-case can probably be optimised
        let row_eq_coefs = eq_poly_sequence_last(&point[point_parts.vertical_vars_range()]).unwrap();

        let mut pad_multipliers = point[point_parts.padded_vars_range()].to_vec();
        let total_multiplier = pad_multipliers.iter_mut().fold(F::one(), |mut acc, val| {
            acc *= F::one() - *val;
            *val = acc;
            acc
        });

        let row_eq_poly_seq = eq_poly_sequence_from_multiplier(total_multiplier, &point[point_parts.segment_vars_range()]);

        let mut row_eq_poly_prefix_seq = Vec::with_capacity(row_eq_poly_seq.len());
        for v in &row_eq_poly_seq {
            let mut acc = Vec::with_capacity(v.len());
            acc.push(v[0]);
            for idx in 1..v.len() {
                acc[idx] = acc[idx - 1] + v[idx];
            }
            row_eq_poly_prefix_seq.push(acc);
        }

        Self {
            point_parts,
            point,
            multiplier: F::one(),
            row_eq_coefs,
            row_eq_poly_seq,
            row_eq_poly_prefix_seq,
            already_bound_vars: 0,
            pad_multipliers,
        }
    }

    pub fn bind(&mut self, t: F) {
        self.multiplier *= F::one() - self.point[self.point_parts.binding_var_idx] - t + (self.point[self.point_parts.binding_var_idx] * t).double();

        self.already_bound_vars += 1;
    }

    pub fn get_segment_evals(&self, segment_len: usize) -> &[F] {
        if self.already_bound_vars < self.row_eq_poly_seq.len() {
            &self.row_eq_poly_seq[self.row_eq_poly_seq.len() - 1 - self.already_bound_vars][0..segment_len]
        } else {
            // additional -1 is because of duplication of last pad_multiplier as first in row_eq_poly_seq
            from_ref(&self.pad_multipliers[self.pad_multipliers.len() - 1 - 1 - (self.already_bound_vars - self.row_eq_poly_seq.len())])
        }
    }

    pub fn get_segment_sum(&self, segment_len: usize) -> &F {
        if self.already_bound_vars < self.row_eq_poly_seq.len() {
            &self.row_eq_poly_prefix_seq[self.row_eq_poly_prefix_seq.len() - 1 - self.already_bound_vars][segment_len]
        } else {
            // additional -1 is because of duplication of last pad_multiplier as first in row_eq_poly_seq
            &self.pad_multipliers[self.pad_multipliers.len() - 1 - 1 - (self.already_bound_vars - self.row_eq_poly_seq.len())]
        }
    }

    pub fn get_trailing_sum(&self, segment_len: usize) -> F {
        F::one() - self.get_segment_sum(segment_len)
    }
}

#[derive(Clone)]
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

    pub fn max_segment_len(&self) -> usize {
        self.data.iter().map(|p| p.len()).max().unwrap_or(0)
    }

    pub fn min_segment_len(&self) -> usize {
        self.data.iter().map(|p| p.len()).min().unwrap_or(0)
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

impl<F: PrimeField> VecVecPolynomial<F, 3> {
    pub fn rand_points<
        CC: TECurveConfig<BaseField=F>,
        RNG: Rng,
    >(rng: &mut RNG, row_logsize: usize, col_logsize: usize) -> Self {
        let data = (0..(rng.next_u64() as usize % (1 << col_logsize))).map(|_| {
            (0..(rng.next_u64() as usize % (1 << row_logsize))).map(|_| {
                let p = Projective::<CC>::rand(rng);
                [p.x, p.y, p.z].into_iter()
            }).flatten().collect_vec()
        }).collect_vec();
        
        Self::new(
            data,
            [F::zero(), F::zero(), F::one()],
            F::zero(),
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
    pub fn bind_21(&mut self, tm1: F) {
        let iter = self.data.par_iter_mut();
        
        iter
            .map(|r| {
                for i in 0..(r.len() / N_POLYS / 2) {
                    for j in 0..N_POLYS {
                        r[i * N_POLYS + j] = F::add(
                            r[(2 * i + 1) * N_POLYS + j],
                            tm1 * F::sub(
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

// #[cfg(test)]
// mod tests {
//     // use ark_ed_on_bls12_381_bandersnatch::Fr;
//     use ark_std::rand::Error;
//     use ark_std::test_rng;
//     use liblasso::poly::dense_mlpoly::DensePolynomial;
//     use super::*;

//     use ark_ff::fields::MontConfig;
//     use ark_ff::{Fp, MontBackend};

//     #[derive(MontConfig)]
//     #[modulus = "17"]
//     #[generator = "3"]
//     pub struct FqConfig;
//     pub type Fq = Fp<MontBackend<FqConfig, 1>, 1>;

//     #[test]
//     fn bind() {
//         // let x = <u64 as Field>::extension_degree();
//         let gen = &mut test_rng();

//         // let mut v = VecVecPolynomial::<Fq, 2>::rand(gen, 3, 2);
//         let mut v = VecVecPolynomial::<Fq, 2>::new(
//             vec![
//                 vec![Fq::from(1), Fq::from(2), Fq::from(3), Fq::from(4)],
//                 vec![Fq::from(5), Fq::from(6)],
//             ],
//             [Fq::from(7), Fq::from(8)],
//             Fq::from(0),
//             2,
//             2,
//         );
//         // let t = Fq::from(gen.next_u64());
//         let t = Fq::from(10);
//         let [d1, d2] = v.vec();
//         let [mut e1, mut e2] = [vec![], vec![]];
//         v.make_21();
//         v.bind_21(&(t - Fq::from(1)));
//         for i in 0..(d1.len() / 2) {
//             e1.push(d1[2 * i] + t * (d1[2 * i + 1] - d1[2 * i]));
//             e2.push(d2[2 * i] + t * (d2[2 * i + 1] - d2[2 * i]));
//         }
//         let [b1, b2] = v.vec();
//         assert_eq!(e1, b1);
//         assert_eq!(e2, b2);
//     }
// }