use std::fmt::{Debug, Formatter, Write};
use std::ops::{Add, AddAssign, Mul, Range, Sub, SubAssign};
use std::slice::from_ref;
use std::sync::Arc;
use ark_ec::twisted_edwards::{TECurveConfig, Projective, Affine};
use ark_ff::{Field, PrimeField};
use ark_std::iterable::Iterable;
use ark_std::rand::{Rng, RngCore};
use ark_std::UniformRand;
use itertools::{repeat_n, Itertools};
use liblasso::poly::eq_poly::EqPolynomial;
use liblasso::utils::math::Math;
use num_traits::Zero;
use rayon::prelude::*;
use crate::cleanup::protocols::splits::SplitIdx;
use crate::cleanup::utils::algfn::AlgFn;
use crate::utils::{eq_poly_sequence_from_multiplier, eq_poly_sequence_last, padded_eq_poly_sequence, Densify};

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
                row.push(data_vecs[r * (1 << self.row_logsize) + c].clone());
            }
            res.push(row);
        }
        f.write_str(&format!("{:?}", res))
    }
}


impl<F: Clone + Debug> VecVecPolynomial<F> {
    pub fn new(mut data: Vec<Vec<F>>, row_pad: F, col_pad: F, row_logsize: usize, col_logsize: usize) -> Self {
        assert!(data.len() <= (1 << col_logsize), "{} {}", data.len(), col_logsize);
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

    pub fn new_unchecked(data: Vec<Vec<F>>, row_pad: F, col_pad: F, row_logsize: usize, col_logsize: usize) -> Self {
        Self {data, row_pad, col_pad, row_logsize, col_logsize }
    }

    pub fn num_vars(&self) -> usize {
        self.col_logsize + self.row_logsize
    }
}

impl<F: From<u64> + Clone + Debug> VecVecPolynomial<F> {
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
                F::one(),
                row_logsize,
                col_logsize,
            ),
            Self::new(
                data[2].take().unwrap(),
                F::one(),
                F::one(),
                row_logsize,
                col_logsize,
            )
        ]
    }

    pub fn rand_points_affine<
        CC: TECurveConfig<BaseField=F>,
        RNG: Rng,
    >(rng: &mut RNG, row_logsize: usize, col_logsize: usize) -> [Self; 2] {
        let data = (0..=(rng.next_u64() as usize % (1 << col_logsize))).map(|_| {
            (0..=(rng.next_u64() as usize % (1 << row_logsize))).map(|_| {
                let p = Affine::<CC>::rand(rng);
                [p.x, p.y]
            }).collect_vec()
        }).collect_vec();

        let mut data = (0..2).map(|i| {
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
                F::one(),
                row_logsize,
                col_logsize,
            ),
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

impl<F: Clone> Densify<F> for VecVecPolynomial<F> {
    type Hint = ();

    fn to_dense(&self, hint: Self::Hint) -> Vec<F> {
        self.vec()
    }
}

impl<F: Clone> Densify<Vec<F>> for Vec<VecVecPolynomial<F>> {
    type Hint = ();

    fn to_dense(&self, hint: Self::Hint) -> Vec<Vec<F>> {
        self.iter().map(|r| r.to_dense(hint)).collect_vec()
    }
}

pub fn vecvec_map<F: PrimeField, Fnc: AlgFn<F>>(
    polys: &[VecVecPolynomial<F>],
    func: Fnc
) -> Vec<VecVecPolynomial<F>> {
    let row_logsize = polys[0].row_logsize;
    let col_logsize = polys[0].col_logsize;
    let mut outs = (0..func.n_outs()).map(|_| (Vec::with_capacity(polys[0].data.len()), None, None)).collect_vec();

    let mut inputs = polys.iter().map(|p| p.row_pad).collect_vec();
    for ((_, rp, _), ret) in outs.iter_mut().zip_eq(func.exec(&inputs)) {
        *rp = Some(ret)
    }

    inputs = polys.iter().map(|p| p.col_pad).collect_vec();
    for ((.., cp), ret) in outs.iter_mut().zip_eq(func.exec(&inputs)) {
        *cp = Some(ret)
    }

    for row in &polys[0].data {
        for (v, ..) in &mut outs {
            v.push(Vec::with_capacity(row.len()));
        }
    }

    for row_idx in 0..polys[0].data.len() {
        for idx in 0..polys[0].data[row_idx].len() {
            inputs = polys.iter().map(|p| p.data[row_idx][idx]).collect_vec();
            for ((data, ..), ret) in outs.iter_mut().zip_eq(func.exec(&inputs)) {
                data[row_idx].push(ret)
            }
        }
    }

    outs.into_iter().map(|(data, row_pad, col_pad)| {
        VecVecPolynomial::new(
            data,
            row_pad.unwrap(),
            col_pad.unwrap(),
            row_logsize,
            col_logsize,
        )
    }).collect_vec()
}

pub fn vecvec_map_split<F: PrimeField, Fnc: AlgFn<F>>(
    polys: &[VecVecPolynomial<F>],
    func: Fnc,
    var_idx: SplitIdx,
    bundle_size: usize,
) -> Vec<VecVecPolynomial<F>> {
    let num_vars = polys[0].num_vars();
    let row_logsize = polys[0].row_logsize;
    let col_logsize = polys[0].col_logsize;
    let mut outs = [0; 2].map(|_| {(0..func.n_outs()).map(|_| (Vec::with_capacity(polys[0].data.len()), None, None)).collect_vec()});

    let mut inputs = polys.iter().map(|p| p.row_pad).collect_vec();
    let row_pad = func.exec(&inputs).collect_vec();

    inputs = polys.iter().map(|p| p.col_pad).collect_vec();
    let col_pad = func.exec(&inputs).collect_vec();

    for oi in 0..2 {
        for ((_, rp, _), ret) in outs[oi].iter_mut().zip_eq(row_pad.iter()) {
            *rp = Some(ret);
        }
        for ((.., cp), ret) in outs[oi].iter_mut().zip_eq(col_pad.iter()) {
            *cp = Some(ret);
        }

        for row in &polys[0].data {
            for (v, ..) in outs[oi].iter_mut() {
                v.push(Vec::with_capacity(((row.len() / 2 + 1) / 2) * 2));
            }
        }
    }
    let segment_size = 1 << (match var_idx {
        SplitIdx::LO(var_idx) => {var_idx}
        SplitIdx::HI(var_idx) => {num_vars - 1 - var_idx}
    });
    for row_idx in 0..polys[0].data.len() {
        for idx in 0..polys[0].data[row_idx].len() {
            inputs = polys.iter().map(|p| p.data[row_idx][idx]).collect_vec().try_into().unwrap_or_else(|_| panic!());
            for ((data, ..), ret) in outs[(idx / segment_size) % 2].iter_mut().zip_eq(func.exec(&inputs)) {
                data[row_idx].push(ret)
            }
        }
        if outs[0][0].0[row_idx].len() % 2 == 1 {
            for oi in 0..2 {
                for i in 0..outs[oi].len() {
                    let row_pad = *outs[oi][i].1.unwrap();
                    outs[oi][i].0[row_idx].push(row_pad);
                }
            }
        }
    }

    let [l, r] = outs;
    l.into_iter().chunks(bundle_size).into_iter().interleave(r.into_iter().chunks(bundle_size).into_iter()).flatten().map(|(data, row_pad, col_pad)| {
        VecVecPolynomial::new_unchecked(
            data,
            *row_pad.unwrap(),
            *col_pad.unwrap(),
            row_logsize - 1,
            col_logsize,
        )
    }).collect_vec()
}

pub fn vecvec_map_split_to_dense<F: PrimeField, Fnc: AlgFn<F>>(
    polys: &[VecVecPolynomial<F>],
    func: Fnc,
    var_idx: SplitIdx,
    bundle_size: usize,
) -> Vec<Vec<F>> {
    let num_vars = polys[0].num_vars();
    let row_logsize = polys[0].row_logsize;
    assert_eq!(row_logsize, 1);
    let col_logsize = polys[0].col_logsize;
    let mut outs = [0, 2].map(|_| {(0..func.n_outs()).map(|_| Vec::with_capacity(1 << polys[0].col_logsize)).collect_vec()});

    let mut inputs = polys.iter().map(|p| p.row_pad).collect_vec();
    let row_pad = func.exec(&inputs).collect_vec();

    inputs = polys.iter().map(|p| p.col_pad).collect_vec();
    let col_pad = func.exec(&inputs).collect_vec();

    let segment_size = 1 << (match var_idx {
        SplitIdx::LO(var_idx) => {var_idx}
        SplitIdx::HI(var_idx) => {num_vars - 1 - var_idx}
    });

    for row_idx in 0..polys[0].data.len() {
        for idx in 0..polys[0].data[row_idx].len() {
            inputs = polys.iter().map(|p| p.data[row_idx][idx]).collect_vec().try_into().unwrap_or_else(|_| panic!());
            for (data, ret) in outs[(idx / segment_size) % 2].iter_mut().zip_eq(func.exec(&inputs)) {
                data.push(ret)
            }
        }
        if outs[0][0].len() < row_idx + 1 {
            for oi in 0..2 {
                for i in 0..outs[oi].len() {
                    outs[oi][i].push(row_pad[i]);
                }
            }
        }
    }

    let [l, r] = outs;
    l.into_iter().enumerate().chunks(bundle_size).into_iter().interleave(r.into_iter().enumerate().chunks(bundle_size).into_iter()).flatten().map(|(idx, mut data)| {
        data.extend(repeat_n(col_pad[idx], (1 << col_logsize) - data.len()));
        data
    }).collect_vec()
}

#[cfg(test)]
mod tests {
    use ark_ec::CurveConfig;
    use rstest::*;
    use ark_ed_on_bls12_381_bandersnatch::{BandersnatchConfig, Fr};
    use ark_std::test_rng;
    use super::*;

    use ark_ff::fields::MontConfig;
    use num_traits::One;
    use crate::cleanup::utils::algfn::ArcedAlgFn;
    use crate::protocol::protocol::PolynomialMapping;
    use crate::utils::map_over_poly;
    type F = <BandersnatchConfig as CurveConfig>::BaseField;


    #[test]
    fn bind() {
        let gen = &mut test_rng();
        let num_vars = 8;
        let vertical_vars = 2;
        let mut v1 = VecVecPolynomial::<Fr>::rand(gen, num_vars - vertical_vars, vertical_vars);
        dbg!(&v1.data.iter().map(|r| r.len()).collect_vec());

        let t = Fr::from(gen.next_u64());

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
            &(0..num_vars).map(|_| Fr::rand(gen)).collect_vec(),
            num_vertical_vars,
            max_row_len,
        );
        let mut segment_size = 1 << (max_row_len.log_2() - 1);

        for i in 0..(num_vars - num_vertical_vars) {
            let eq_evals = eq.get_segment_evals(segment_size);
            for i in 0..segment_size {
                assert_eq!(
                    eq_evals[0..i].iter().sum::<Fr>() + eq.get_trailing_sum(i),
                    Fr::one(),
                )
            }
            eq.bind(Fr::rand(gen));
            segment_size = 1.max(segment_size / 2);
        }
        match eq.point_parts.binding_var_idx {
            None => {assert_eq!(eq.point_parts.padded_vars_idx, 0)}
            Some(i) => {assert_eq!(i, eq.point_parts.padded_vars_idx - 1)}
        }
    }

    fn foo(ins: &[&F]) -> Vec<F> {
        vec![
            ins[0] + ins[1],
            ins[1] + ins[2],
        ]
    }
    fn blah(ins: &[F]) -> Vec<F> {
        let tmp = ins.iter().collect_vec();
        let tmp = tmp.as_slice();
        foo(&tmp)
    }

    #[test]
    fn map() {
        let gen = &mut test_rng();
        let n_args = 3;

        let data = VecVecPolynomial::rand_points::<BandersnatchConfig, _>(gen, 3, 3);
        let dense_data = data.iter().map(|p| p.vec()).collect_vec();

        let out = vecvec_map(data.as_slice().try_into().unwrap(), ArcedAlgFn::new(Arc::new(foo), 3, 2, 1));
        let expected_out = map_over_poly(&dense_data.iter().map(|p| p.as_slice()).collect_vec().as_slice(), PolynomialMapping {
            exec: Arc::new(blah),
            degree: 1,
            num_i: 3,
            num_o: 2,
        });

        let dense_out = out.into_iter().map(|p| p.vec()).collect_vec();

        assert_eq!(dense_out, expected_out)
    }

    #[test]
    fn map_split() {
        let gen = &mut test_rng();
        for i in 0..100 {
            let n_args = 3;

            let data = VecVecPolynomial::rand_points::<BandersnatchConfig, _>(gen, 3, 3);
            let dense_data = data.iter().map(|p| p.vec()).collect_vec();

            let out = vecvec_map_split(data.as_slice().try_into().unwrap(), ArcedAlgFn::new(Arc::new(foo), 3, 2, 1), SplitIdx::LO(0), 1);
            let expected_out = map_over_poly(&dense_data.iter().map(|p| p.as_slice()).collect_vec().as_slice(), PolynomialMapping {
                exec: Arc::new(blah),
                degree: 1,
                num_i: 3,
                num_o: 2,
            });
            let (out0, out1) = out.iter().tee();
            let out0 = out0.step_by(2);
            let out1 = out1.skip(1).step_by(2);

            let dense_out = out0.zip_eq(out1).map(|(l, r)| {
                l.vec().into_iter().interleave(r.vec().into_iter()).collect_vec()
            }).collect_vec();

            assert_eq!(dense_out, expected_out);
        }
    }

    #[test]
    fn map_split_to_dense() {
        let gen = &mut test_rng();
        let n_args = 3;

        let data = VecVecPolynomial::rand_points::<BandersnatchConfig, _>(gen, 1, 3);
        let dense_data = data.iter().map(|p| p.vec()).collect_vec();

        let out = vecvec_map_split_to_dense(data.as_slice().try_into().unwrap(), ArcedAlgFn::new(Arc::new(foo), 3, 2, 1), SplitIdx::LO(0), 1);
        let expected_out = map_over_poly(&dense_data.iter().map(|p| p.as_slice()).collect_vec().as_slice(), PolynomialMapping {
            exec: Arc::new(blah),
            degree: 1,
            num_i: 3,
            num_o: 2,
        });
        let (out0, out1) = out.into_iter().tee();
        let out0 = out0.step_by(2);
        let out1 = out1.skip(1).step_by(2);

        let dense_out = out0.zip_eq(out1).map(|(l, r)| {
            l.into_iter().interleave(r.into_iter()).collect_vec()
        }).collect_vec();

        assert_eq!(dense_out, expected_out);
        
    }
}