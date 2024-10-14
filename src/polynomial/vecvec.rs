use std::fmt::{Debug, Formatter, Write};
use std::ops::{Add, AddAssign, Mul, Range, Sub, SubAssign};
use std::slice::from_ref;
use ark_ec::twisted_edwards::{TECurveConfig, Projective};
use ark_ff::{Field, PrimeField};
use ark_std::rand::{Rng, RngCore};
use ark_std::UniformRand;
use itertools::Itertools;
use liblasso::poly::eq_poly::EqPolynomial;
use liblasso::utils::math::Math;
use num_traits::Zero;
use rayon::prelude::*;

use crate::utils::{eq_poly_sequence_from_multiplier, eq_poly_sequence_last, padded_eq_poly_sequence};

#[derive(Debug)]
pub struct EQPolyPointParts {
    pub padded_vars_idx: usize,
    pub segment_vars_idx: usize,
    pub binding_var_idx: Option<usize>,
}

impl EQPolyPointParts {
    fn new<F>(point: &[F], col_logsize: usize, max_segment_logsize: usize) -> Self {
        let padded_vars_idx = col_logsize;
        let segment_vars_idx = point.len() - max_segment_logsize;
        let binding_var_idx = point.len() - 1;

        Self {
            padded_vars_idx,
            segment_vars_idx,
            binding_var_idx: Some(binding_var_idx),
        }
    }

    fn bind(&mut self) {
        match &mut self.binding_var_idx {
            None => {}
            Some(0) => {
                self.binding_var_idx = None;
            }
            Some(x) => {
                *x -= 1;
            }
        }
    }

    pub fn vertical_vars_range(&self) -> Range<usize> {
        0..self.padded_vars_idx
    }

    pub fn padded_vars_range(&self) -> Range<usize> {
        self.padded_vars_idx..self.segment_vars_idx.min(self.binding_var_idx.unwrap())
    }

    pub fn segment_vars_range(&self) -> Range<usize> {
        self.segment_vars_idx..self.segment_vars_idx.max(self.binding_var_idx.unwrap())
    }

    pub fn row_vars_range(&self) -> Range<usize> {
        self.padded_vars_idx..self.segment_vars_idx.max(self.binding_var_idx.unwrap())
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
    // EQ polys materialized for the longest segment in each fold
    pub row_eq_poly_seq: Vec<Vec<F>>,
    // EQ polys prefix sums to multiply
    pub row_eq_poly_prefix_seq: Vec<Vec<F>>,
    // how many vars are already bound
    pub already_bound_vars: usize,
}

impl<F: PrimeField> EQPolyData<F> {
    pub fn new(point: &[F], col_logsize: usize, max_row_len: usize) -> Self {
        let max_segment_logsize = max_row_len.log_2();

        // variable parts
        let point_parts = EQPolyPointParts::new(point, col_logsize, max_segment_logsize);
        let point = point.to_vec();

        // this use-case can probably be optimised
        let row_eq_coefs = eq_poly_sequence_last(&point[point_parts.vertical_vars_range()]).unwrap();


        let row_eq_poly_seq = padded_eq_poly_sequence(point_parts.padded_vars_range().len(), &point[point_parts.row_vars_range()]);

        let mut row_eq_poly_prefix_seq = Vec::with_capacity(row_eq_poly_seq.len());
        for v in &row_eq_poly_seq {
            let mut acc = Vec::with_capacity(v.len() + 1);
            acc.push(F::zero());
            for idx in 0..v.len() {
                acc.push(acc[idx] + v[idx]);
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
        }
    }

    pub fn bind(&mut self, t: F) {
        self.multiplier *= F::one() - self.point[self.point_parts.binding_var_idx.unwrap()] - t + (self.point[self.point_parts.binding_var_idx.unwrap()] * t).double();
        self.point_parts.bind();
        self.already_bound_vars += 1;
    }

    pub fn get_segment_evals(&self, segment_len: usize) -> &[F] {
        &self.row_eq_poly_seq[self.row_eq_poly_seq.len() - 1 - self.already_bound_vars][0..segment_len]
    }

    pub fn get_current_evals(&self) -> &[F] {
        &self.row_eq_poly_seq[self.row_eq_poly_seq.len() - 1 - self.already_bound_vars]
    }

    pub fn get_segment_sum(&self, segment_len: usize) -> &F {
        &self.row_eq_poly_prefix_seq[self.row_eq_poly_prefix_seq.len() - 1 - self.already_bound_vars][segment_len]
    }

    pub fn get_trailing_sum(&self, segment_len: usize) -> F {
        F::one() - self.get_segment_sum(segment_len)
    }
}

#[derive(Clone)]
pub struct VecVecPolynomial<F> {
    pub data: Vec<Vec<F>>,
    /// Each row is padded to 1 << *row_logsize* by corresponding *row_pad*
    pub row_pad: F,
    /// Concatenation of padded rows padded to 1 << *col_logsize* by *col_pad*.
    pub col_pad: F,
    /// the least significant *row_logsize* coordinates are thought as index in bucket; these are coordinates we will run sumcheck over
    pub row_logsize: usize,
    /// the most significant *col_logsize* coordinates are thought as bucket indexes; It is impossible to sumcheck by them
    pub col_logsize: usize,
}

impl<F: Clone + Debug> Debug for VecVecPolynomial<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut res = vec![];
        let data_vecs = self.vec();
        for r in 0..(1 << self.col_logsize) {
            let mut row = vec![];
            for c in 0..(1 << self.row_logsize) {
                let mut bundle = vec![];
                bundle.push(data_vecs[r * (1 << self.row_logsize) + c].clone());
                row.push(bundle);
            }
            res.push(row);
        }
        f.write_str(&format!("{:?}", res))
    }
}


impl<F: Clone> VecVecPolynomial<F> {
    pub fn new(mut data: Vec<Vec<F>>, row_pad: F, col_pad: F, row_logsize: usize, col_logsize: usize) -> Self {
        assert!(data.len() <= (1 << col_logsize));
        data.iter_mut().map(|p| {
            assert!(p.len() <= 1 << row_logsize);
            if p.len() % 2 == 1 {
                p.push(row_pad.clone());
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

    pub fn new_unchecked(data: Vec<Vec<F>>, row_pad: F, col_pad: F, inner_exp: usize, total_exp: usize) -> Self {
        Self {data, row_pad, col_pad, row_logsize: inner_exp, col_logsize: total_exp }
    }

    pub fn num_vars(&self) -> usize {
        self.col_logsize + self.row_logsize
    }
}

impl<F: From<u64> + Clone> VecVecPolynomial<F> {
    pub fn rand<RNG: Rng>(rng: &mut RNG, row_logsize: usize, col_logsize: usize) -> Self {
        let data = (0..(rng.next_u64() as usize % (1 << col_logsize))).map(|_| {
            (0..(rng.next_u64() as usize % (1 << row_logsize))).map(|_| F::from(rng.next_u64())).collect_vec()
        }).collect_vec();


        Self::new(
            data,
            F::from(rng.next_u64()),
            F::from(rng.next_u64()),
            row_logsize,
            col_logsize,
        )
    }
}

impl<F: PrimeField> VecVecPolynomial<F> {
    pub fn rand_points_dense_rows<
        CC: TECurveConfig<BaseField=F>,
        RNG: Rng,
    >(rng: &mut RNG, row_logsize: usize, col_logsize: usize) -> [Self; 3] {
        let data = (0..(1 << col_logsize)).map(|_| {
            (0..(1 << row_logsize)).map(|_| {
                let p = Projective::<CC>::rand(rng);
                [p.x, p.y, p.z]
            }).collect_vec()
        }).collect_vec();

        let mut data = (0..3).map(|i| {
            Some(data.iter().map(|r| r.iter().map(|p| p[i].clone()).collect_vec()).collect_vec())
        }).collect_vec();

        [
            Self::new(
                data[0].take().unwrap(),
                F::zero(),
                F::zero(),
                row_logsize,
                col_logsize,
            ),
            Self::new(
                data[1].take().unwrap(),
                F::one(),
                F::zero(),
                row_logsize,
                col_logsize,
            ),
            Self::new(
                data[2].take().unwrap(),
                F::one(),
                F::zero(),
                row_logsize,
                col_logsize,
            )
        ]
    }


    pub fn rand_points_dense<
        CC: TECurveConfig<BaseField=F>,
        RNG: Rng,
    >(rng: &mut RNG, row_logsize: usize, col_logsize: usize) -> [Self; 3] {
        let data = (0..(1 << col_logsize)).map(|_| {
            (0..(1 << row_logsize)).map(|_| {
                let p = Projective::<CC>::rand(rng);
                [p.x, p.y, p.z]
            }).collect_vec()
        }).collect_vec();

        let mut data = (0..3).map(|i| {
            Some(data.iter().map(|r| r.iter().map(|p| p[i].clone()).collect_vec()).collect_vec())
        }).collect_vec();

        [
            Self::new(
                data[0].take().unwrap(),
                F::zero(),
                F::zero(),
                row_logsize,
                col_logsize,
            ),
            Self::new(
                data[1].take().unwrap(),
                F::one(),
                F::zero(),
                row_logsize,
                col_logsize,
            ),
            Self::new(
                data[2].take().unwrap(),
                F::one(),
                F::zero(),
                row_logsize,
                col_logsize,
            )
        ]
    }


    pub fn rand_points<
        CC: TECurveConfig<BaseField=F>,
        RNG: Rng,
    >(rng: &mut RNG, row_logsize: usize, col_logsize: usize) -> [Self; 3] {
        let data = (0..=(rng.next_u64() as usize % (1 << col_logsize))).map(|_| {
            (0..=(rng.next_u64() as usize % (1 << row_logsize))).map(|_| {
                let p = Projective::<CC>::rand(rng);
                [p.x, p.y, p.z]
            }).collect_vec()
        }).collect_vec();

        let mut data = (0..3).map(|i| {
            Some(data.iter().map(|r| r.iter().map(|p| p[i].clone()).collect_vec()).collect_vec())
        }).collect_vec();

        [
            Self::new(
                data[0].take().unwrap(),
                F::zero(),
                F::zero(),
                row_logsize,
                col_logsize,
            ),
            Self::new(
                data[1].take().unwrap(),
                F::one(),
                F::zero(),
                row_logsize,
                col_logsize,
            ),
            Self::new(
                data[2].take().unwrap(),
                F::one(),
                F::zero(),
                row_logsize,
                col_logsize,
            )
        ]
    }

    pub fn fill_padding(&mut self) {
        for row in &mut self.data {
            while row.len() < 1 << self.row_logsize {
                row.push(self.row_pad)
            }
        }
        while self.data.len() < 1 << self.col_logsize {
            self.data.push(vec![self.col_pad; 1 << self.row_logsize]);
        }
    }
}

// Bind
impl<F: Field> VecVecPolynomial<F> {

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
                for i in 0..(r.len() / 2) {
                    r[2 * i] = r[2 * i + 1].double() - r[2 * i];
                }
            })
            .count();
    }

    /// Example with N_POLYS = 1, col_logsize = 0
    /// transform p_02, p_01, p_12, p_11
    /// into p_00 + t(p_01 - p_00), p_10 + t(p_11 - p_10)
    ///
    /// Where p_*2 = 2 * p_*1 - p_*0
    pub fn bind_21(&mut self, t: F) {
        let tm1 = t - F::one();
        let iter = self.data.par_iter_mut();
        
        iter
            .map(|r| {
                for i in 0..(r.len() / 2) {
                    r[i] = r[2 * i + 1] + tm1 * (r[2 * i] - r[2 * i + 1]);
                }
                let mut i = r.len() / 2;
                if i % 2 == 1 {
                    r[i] = self.row_pad;
                    i += 1;
                }
                r.truncate(i);
            })
            .count();
        self.row_logsize -= 1;
    }
}

// Vec
impl<F: Clone> VecVecPolynomial<F> {
    pub fn vec(&self) -> Vec<F> {
        let mut ret: Vec<F> = vec![];

        for r in 0..(1 << self.col_logsize) {
            for c in 0..(1 << self.row_logsize) {
                if r >= self.data.len() {
                    ret.push(self.col_pad.clone());
                } else if c >= self.data[r].len() {
                    ret.push(self.row_pad.clone());
                } else {
                    ret.push(self.data[r][c].clone())
                }
            }
        }
        ret
    }
}

pub fn map<const N_INS: usize, const N_OUT: usize, F: Clone, Fnc: Fn(&[&F; N_INS]) -> [F; N_OUT] + Sync + Send>(polys: &[VecVecPolynomial<F>; N_INS]) -> [VecVecPolynomial<F>; N_OUT] {
    todo!()   
}

pub fn map_split<const N_INS: usize, const N_OUT: usize, F: Clone, Fnc: Fn(&[&F; N_INS]) -> [F; N_OUT] + Sync + Send>(polys: &[VecVecPolynomial<F>; N_INS]) -> [[VecVecPolynomial<F>; N_OUT]; 2] {
    todo!()
}

#[cfg(test)]
mod tests {
    use rstest::*;
    // use ark_ed_on_bls12_381_bandersnatch::Fr;
    use ark_std::rand::Error;
    use ark_std::test_rng;
    use liblasso::poly::dense_mlpoly::DensePolynomial;
    use super::*;

    use ark_ff::fields::MontConfig;
    use ark_ff::{Fp, MontBackend};
    use num_traits::One;

    #[derive(MontConfig)]
    #[modulus = "179"]
    #[generator = "1"]
    pub struct FqConfig;
    pub type Fq = Fp<MontBackend<FqConfig, 1>, 1>;

    #[test]
    fn bind() {
        let gen = &mut test_rng();
        let num_vars = 8;
        let vertical_vars = 2;
        let mut v1 = VecVecPolynomial::<Fq>::rand(gen, num_vars - vertical_vars, vertical_vars);
        dbg!(&v1.data.iter().map(|r| r.len()).collect_vec());

        let t = Fq::from(gen.next_u64());

        for i in 0..(num_vars - vertical_vars) {
            let d1 = v1.vec();
            let mut e1 = vec![];
            v1.make_21();
            v1.bind_21(t);
            for i in 0..(d1.len() / 2) {
                e1.push(d1[2 * i] + t * (d1[2 * i + 1] - d1[2 * i]));
            }
            let b1 = v1.vec();
            e1.iter().zip_eq(b1.iter()).enumerate().map(|(idx, (e, b))| {
                assert_eq!(e, b, "{}", idx)
            }).count();
        }
    }

    #[rstest]
    fn eq_prefixes(
        #[values(0, 1, 2)]
        num_vertical_vars: usize,
        #[values(2, 3, 7)]
        max_row_len: usize,
    ) {
        let gen = &mut test_rng();
        let num_vars = 6;

        let mut eq = EQPolyData::new(
            &(0..num_vars).map(|_| Fq::rand(gen)).collect_vec(),
            num_vertical_vars,
            max_row_len,
        );
        let mut segment_size = 1 << (max_row_len.log_2() - 1);

        for i in 0..(num_vars - num_vertical_vars) {
            let eq_evals = eq.get_segment_evals(segment_size);
            for i in 0..segment_size {
                assert_eq!(
                    eq_evals[0..i].iter().sum::<Fq>() + eq.get_trailing_sum(i),
                    Fq::one(),
                )
            }
            eq.bind(Fq::rand(gen));
            segment_size = 1.max(segment_size / 2);
        }
        match eq.point_parts.binding_var_idx {
            None => {assert_eq!(eq.point_parts.padded_vars_idx, 0)}
            Some(i) => {assert_eq!(i, eq.point_parts.padded_vars_idx - 1)}
        }
    }
}