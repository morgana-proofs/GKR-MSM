use std::collections::HashMap;
use std::iter::repeat_n;
use std::marker::PhantomData;
use std::ops::{Add, Index, Mul, Sub};
use ark_bls12_381::Fr;
use ark_ec::twisted_edwards::{Projective, TECurveConfig};
use ark_ff::{BigInt, Field, PrimeField};
use ark_std::iterable::Iterable;
use ark_std::rand::Rng;
use ark_std::UniformRand;
use hashcaster::ptr_utils::{AsSharedMUMutPtr, UninitArr, UnsafeIndexRawMut};
use itertools::Itertools;
use liblasso::poly::dense_mlpoly::DensePolynomial;
use liblasso::utils::math::Math;
use num_traits::PrimInt;
#[cfg(feature = "prof")]
use profi::prof;
use rayon::prelude::*;
use crate::protocol::protocol::{MultiEvalClaim, PolynomialMapping};
use crate::cleanup::utils::algfn::{AlgFn, AlgFnSO};

pub trait TwistedEdwardsConfig {

    const COEFF_D: Self;

    fn mul_by_a(&self) -> Self;

    fn mul_by_d(&self) -> Self;
}


impl TwistedEdwardsConfig for Fr {

    const COEFF_D: Self = Self {
        0: BigInt([12167860994669987632, 4043113551995129031, 6052647550941614584, 3904213385886034240]),
        1: PhantomData
    };

    #[inline(always)]
    fn mul_by_a(&self) -> Self {
        let t = (*self).double().double();
        -(t + *self)
    }

    #[inline(always)]
    fn mul_by_d(&self) -> Self {
        *self * Self::COEFF_D
    }
}


pub fn map_over_poly_legacy<F: PrimeField>(
    ins: &[DensePolynomial<F>],
    f: impl Fn(&[F]) -> Vec<F> + Send + Sync
) -> Vec<DensePolynomial<F>> {
    #[cfg(feature = "prof")]
    prof!("map_over_poly");

    let applications: Vec<Vec<F>> = (0..ins[0].len()).into_par_iter()
        .map(|idx| {
            f(&ins.iter().map(|p| p[idx]).collect_vec())
        }).collect();

    (0..applications.first().unwrap().len()).into_par_iter()
        .map(|idx| {
            DensePolynomial::new(applications.par_iter().map(|v| v[idx]).collect())
        }).collect::<Vec<DensePolynomial::<F>>>().try_into().unwrap()
}

pub fn map_over_poly<F: Field>(
    ins: &[&[F]],
    f: PolynomialMapping<F>,
) -> Vec<Vec<F>> {
    #[cfg(feature = "prof")]
    prof!("map_over_poly");
    let applications: Vec<Vec<F>> = (0..ins[0].len()).into_par_iter()
        .map(|idx| {
            (f.exec)(&ins.iter().map(|p| p[idx]).collect_vec())
        }).collect();

    (0..f.num_o).into_par_iter()
        .map(|idx| {
            applications.iter().map(|v| v[idx]).collect()
        })
        .collect::<Vec<Vec<F>>>()
}

pub fn scale<F: Field + TwistedEdwardsConfig, T: Fn (&[F]) -> Vec<F>>(f: T) -> impl Fn (&[F]) -> Vec<F> {
    move |data: &[F]| -> Vec<F> {
        let (pts, factor) = data.split_at(data.len() - 1);
        f(&pts.to_vec()).par_iter().map(|p| *p * factor[0]).collect()
    }
}

pub fn fold_with_coef<F: Field>(evals: &[F], layer_coef: F) -> Vec<F> {
    assert_eq!(evals.len() % 2, 0);
    let half = evals.len() / 2;
    (0..half)
        .map(|i| evals[i] + layer_coef * (evals[half + i] - evals[i]))
        .collect()
}


pub fn make_gamma_pows_legacy<F: PrimeField>(claims: &MultiEvalClaim<F>, gamma: F) -> Vec<F> {
    let num_claims = claims.evs.iter().fold(0, |acc, upd| acc + upd.len());

    let mut gamma_pows = vec![F::one(), gamma];
    for i in 2..num_claims {
        let tmp = gamma_pows[i-1];
        gamma_pows.push(tmp * gamma);
    }
    gamma_pows
}

pub fn make_gamma_pows_static<F: PrimeField, const N_POWS: usize>(gamma: F) -> [F; N_POWS] {
    let mut gamma_pows = Vec::with_capacity(N_POWS);
    gamma_pows.push(F::one());
    gamma_pows.push(gamma);
    for i in 2..N_POWS {
        let tmp = gamma_pows[i - 1];
        gamma_pows.push(tmp * gamma);
    };
    gamma_pows.try_into().unwrap_or_else(|v: Vec<F>| panic!("Expected a Vec of length {} but it was {}", N_POWS, v.len()))
}

pub fn make_gamma_pows<F: PrimeField>(gamma: F, count: usize) -> Vec<F> {
    let mut gamma_pows = Vec::with_capacity(count);
    gamma_pows.push(F::one());
    gamma_pows.push(gamma);
    for i in 2..count {
        let tmp = gamma_pows[i - 1];
        gamma_pows.push(tmp * gamma);
    };
    gamma_pows
}

pub fn zip_with_gamma<F: PrimeField>(gamma: F, vals: &[F]) -> F {
    let l = vals.len();
    if l == 0 {
        return F::zero();
    }
    let mut ret = vals[l - 1];
    for i in 0 .. (l - 1) {
        ret *= gamma;
        ret += vals[l - i - 2];
    };
    ret
}

pub fn eq_eval<F: PrimeField>(p1: &[F], p2: &[F]) -> F {
    p1.iter().zip_eq(p2.iter()).map(|(x1, x2)| {
        F::one() - x1 - x2 + (*x1 * x2).double()
    }).product()
}

pub fn split_into_chunks_balanced<T>(arr: &[T], num_threads: usize) -> impl Iterator<Item = &[T]> + '_ {
    let l = arr.len();
    let base_size = l / num_threads;
    let num_large_chunks = l - base_size * num_threads;

    let (m_hi, m_lo) = arr.split_at(num_large_chunks * num_threads);
    let chunks_hi = m_hi.chunks(base_size + 1);
    let chunks_lo = m_lo.chunks(base_size);
    chunks_hi.chain(chunks_lo)
}

pub fn fix_var_top<F>(vec: &mut Vec<F>, v: F) {
    vec.push(v);
}

pub fn fix_var_bot<F>(vec: &mut Vec<F>, v: F) {
    vec.insert(0, v);
}

pub fn random_point<F: UniformRand>(gen: &mut impl Rng, num_vars: usize) -> Vec<F> {
    (0..num_vars).map(|_| F::rand(gen)).collect_vec()
}

#[cfg(feature = "parallel")]
pub trait CfgParallel: Send + Sync {}
#[cfg(not(feature = "parallel"))]
pub trait CfgParallel {}
#[cfg(feature = "parallel")]
impl<F: Send + Sync> CfgParallel for F {}
#[cfg(not(feature = "parallel"))]
impl<F> CfgParallel for F {}


pub fn padded_eq_poly_sequence<F: PrimeField>(padding_size: usize, pt: &[F]) -> Vec<Vec<F>> {
    let l = pt.len();
    let mut ret = Vec::with_capacity(l + 1);
    ret.push(vec![F::one()]);
    for i in 1..=padding_size {
        ret.push(vec![ret[i - 1][0] * (F::one() - pt[i - 1])]);
    }

    for i in (padding_size + 1)..=l {
        let last = &ret[i - 1];
        let multiplier = &pt[i - 1];
        let mut incoming = UninitArr::<F>::new(1 << (i - padding_size));
        unsafe {
            let ptr = incoming.as_shared_mut_ptr();
            #[cfg(not(feature = "parallel"))]
            let iter = (0 .. (1 << (i - 1 - padding_size))).into_iter();

            #[cfg(feature = "parallel")]
            let iter = (0 .. (1 << (i - 1 - padding_size))).into_par_iter();

            iter.map(|j|{
                let w = &last[j];
                let m = *multiplier * w;
                *ptr.get_mut(2 * j) = *w - m;
                *ptr.get_mut(2 * j + 1) = m;
            }).count();
            ret.push(incoming.assume_init());
        }
    }

    ret
}

pub fn eq_poly_sequence_from_multiplier<F: PrimeField>(multiplier: F, pt: &[F]) -> Vec<Vec<F>> {
    let l = pt.len();
    let mut ret = Vec::with_capacity(l + 1);
    ret.push(vec![multiplier]);

    for i in 1..=l {
        let last = &ret[i - 1];
        let multiplier = &pt[i - 1];
        let mut incoming = UninitArr::<F>::new(1 << i);
        unsafe {
            let ptr = incoming.as_shared_mut_ptr();
            #[cfg(not(feature = "parallel"))]
            let iter = (0 .. (1 << (i - 1))).into_iter();

            #[cfg(feature = "parallel")]
            let iter = (0 .. 1 << (i - 1)).into_par_iter();

            iter.map(|j|{
                let w = &last[j];
                let m = *multiplier * w;
                *ptr.get_mut(2 * j) = *w - m;
                *ptr.get_mut(2 * j + 1) = m;
            }).count();
            ret.push(incoming.assume_init());
        }
    }

    ret
}

pub fn eq_poly_sequence<F: PrimeField>(pt: &[F]) -> Vec<Vec<F>> {
    eq_poly_sequence_from_multiplier(F::one(), pt)
}

pub fn eq_poly_sequence_last<F: PrimeField>(pt: &[F]) -> Option<Vec<F>> {
    eq_poly_sequence(pt).pop()
}

pub fn eq_poly_sequence_from_multiplier_last<F: PrimeField>(mul: F, pt: &[F]) -> Option<Vec<F>> {
    eq_poly_sequence_from_multiplier(mul, pt).pop()
}

/// Computes sum of eq(pt, i) for i in (0..k)
pub fn eq_sum<F: PrimeField>(pt: &[F], mut k: usize) -> F {    
    let mut multiplier = F::one();
    let mut acc = F::zero();

    if k >= (1 << pt.len()) {
        if k == 1 << pt.len() {
            return F::one();
        } else {
            panic!();
        }
    }

    for i in 0..pt.len() {
        let left_bit = k >> (pt.len() - i - 1);

        let _multiplier = multiplier;
        if left_bit == 1 {
            multiplier *= pt[i];
            acc += (_multiplier - multiplier);         
        } else {
            multiplier *= (F::one() - pt[i]);
        }
        k -= left_bit << (pt.len() - i - 1);
    }

    acc
}


pub fn prettify_points<F: PrimeField, CC: TECurveConfig<BaseField=F>>(point_map: &HashMap<Projective<CC>, usize>, v: &Vec<Projective<CC>>) -> String {
    v.iter().map(|p| point_map.get(p).map(|v| format!("{}", v).to_string()).unwrap_or("Unknown".to_string())).join(", ")
}

pub fn build_points_from_chunk<F: PrimeField, CC: TECurveConfig<BaseField=F>>(chunk: &[Vec<F>]) -> Vec<Projective<CC>> {
    (0..chunk[0].len())
        .map(|i| {
            Projective::<CC>::new_unchecked(
                chunk[0][i],
                chunk[1][i],
                chunk[0][i] * chunk[1][i] / chunk[2][i],
                chunk[2][i],
            )
        })
        .collect_vec()
}

pub fn prettify_coords_chunk<F: PrimeField, CC: TECurveConfig<BaseField=F>>(point_map: &HashMap<Projective<CC>, usize>, chunk: &[Vec<F>]) -> String {
    prettify_points(
        point_map,
        &build_points_from_chunk(chunk)
    )
}

pub fn build_points<F: PrimeField, CC: TECurveConfig<BaseField=F>>(coords: &[Vec<F>]) -> Vec<Vec<Projective<CC>>> {
    coords.chunks(3).map(|chunk| {
        build_points_from_chunk(chunk)
    }).collect_vec()
}

pub fn pad_vector<T: Clone>(v: &mut Vec<T>, up_to_logsize: usize, with: T) {
    assert!(v.len() <= 1 << up_to_logsize);
    let n = (1 << up_to_logsize) - v.len();
    v.reserve(n);
    v.extend(repeat_n(with, n));
}

pub fn prettify_coords<F: PrimeField, CC: TECurveConfig<BaseField=F>>(point_map: &HashMap<Projective<CC>, usize>, coords: &[Vec<F>]) -> String {
    coords.chunks(3).map(|chunk| {
        prettify_coords_chunk(point_map, chunk)
    }).join(" || ")
}

#[cfg(feature = "memprof")]
pub fn memprof(l: &str) {
    use jemalloc_ctl::{epoch, stats};
    epoch::advance().unwrap();
    let allocated = stats::allocated::read().unwrap();
    let resident = stats::resident::read().unwrap();
    println!("{}: {:.3}Gb ({} bytes) allocated / {:.3}Gb ({} bytes) resident", l, allocated as f64 / 1024f64 / 1024f64 / 1024f64, allocated, resident as f64 / 1024f64 / 1024f64 / 1024f64, resident);
}


#[cfg(test)]
mod test {
    use std::sync::Arc;
    use ark_ec::CurveConfig;
    use ark_ed_on_bls12_381_bandersnatch::{BandersnatchConfig, Fr};
    use ark_std::{test_rng, UniformRand, Zero};
    use itertools::Itertools;
    use num_traits::One;
    use rstest::rstest;
    use crate::cleanup::polys::common::{BindVar21, Densify, Make21, MapSplit, RandomlyGeneratedPoly};
    use crate::cleanup::protocols::splits::SplitIdx;
    use crate::cleanup::utils::algfn::ArcedAlgFn;
    use crate::protocol::protocol::PolynomialMapping;
    use crate::utils::{eq_poly_sequence_from_multiplier, eq_sum, map_over_poly, padded_eq_poly_sequence};
    use crate::cleanup::polys::dense::{bind_21_single_thread, DensePolyRndConfig};

    use super::eq_poly_sequence;

    #[test]
    fn eq_poly_seq() {
        let gen = &mut test_rng();
        let num_vars = 8;
        let num_padded = 3;

        let point = (0..num_vars).map(|_| Fr::rand(gen)).collect_vec();

        let mut pad_multipliers = point[0..num_padded].to_vec();
        let total_multiplier = pad_multipliers.iter_mut().fold(Fr::one(), |mut acc, val| {
            acc *= Fr::one() - *val;
            *val = acc;
            acc
        });

        let row_eq_poly_seq = eq_poly_sequence_from_multiplier(total_multiplier, &point[num_padded..num_vars]);

        let padded_eq_poly_seq = padded_eq_poly_sequence(num_padded, &point);
        for i in 0..num_padded {
            assert_eq!(padded_eq_poly_seq[i + 1][0], pad_multipliers[i]);
        }
        for i in (num_padded - 1)..num_vars {
            assert_eq!(padded_eq_poly_seq[i + 1], row_eq_poly_seq[i + 1 - num_padded]);
        }
    }
    type F = <BandersnatchConfig as CurveConfig>::BaseField;

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
    fn eq_sum_works() {
        let rng = &mut test_rng();
        let nvars = 7;
        let point = (0..nvars).map(|_| Fr::rand(rng)).collect_vec();

        let eq_evals = eq_poly_sequence(&point).pop().unwrap();
        assert!(eq_evals.len() == 1 << nvars);

        let mut expected_sum = vec![Fr::zero()];

        for i in 0..eq_evals.len() {
            expected_sum.push(
                expected_sum[i] + eq_evals[i]
            )
        }

        for i in 0..eq_evals.len() + 1 {
            assert!(expected_sum[i] == eq_sum(&point, i), "{}", i)
        }

    }

    #[test]
    fn vec_algfn_map() {
        let gen = &mut test_rng();
        let n_args = 3;
        let num_vars = 8;

        let data = Vec::rand_points::<BandersnatchConfig, _>(gen, DensePolyRndConfig {
            num_vars,
        });
        let dense_data = data.iter().map(|p| p.to_dense(num_vars)).collect_vec();

        let out = Vec::algfn_map(data.as_slice().try_into().unwrap(), ArcedAlgFn::new(Arc::new(foo), 3, 2, 1));
        let expected_out = map_over_poly(&dense_data.iter().map(|p| p.as_slice()).collect_vec().as_slice(), PolynomialMapping {
            exec: Arc::new(blah),
            degree: 1,
            num_i: 3,
            num_o: 2,
        });

        let dense_out = out.into_iter().map(|p| p.to_dense(num_vars)).collect_vec();

        assert_eq!(dense_out, expected_out)
    }

    #[test]
    fn vec_make21() {
        let gen = &mut test_rng();

        let num_vars = 8;
        let mut data = (0..(1 << num_vars)).map(|_| F::rand(gen)).collect_vec();
        let t = F::rand(gen);
        data.make_21();
        let mut expected = data.clone();
        bind_21_single_thread(&mut expected, t);
        data.bind_21(t);
        assert_eq!(expected, data);
    }

    #[test]
    fn map_split_lo() {
        let gen = &mut test_rng();
        let num_vars = 5; 
        for i in 0..100 {
            let n_args = 3;

            let data = Vec::rand_points::<BandersnatchConfig, _>(gen, DensePolyRndConfig {num_vars});
            let dense_data = data.iter().map(|p| p.to_dense(num_vars)).collect_vec();

            let out = Vec::algfn_map_split(data.as_slice().try_into().unwrap(), ArcedAlgFn::new(Arc::new(foo), 3, 2, 1), SplitIdx::LO(0), 1);
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
                l.to_dense(num_vars - 1).into_iter().interleave(r.to_dense(num_vars - 1).into_iter()).collect_vec()
            }).collect_vec();

            assert_eq!(dense_out, expected_out);
        }
    }
    
    #[rstest]
    fn map_split(
        #[values(
            SplitIdx::LO(0), 
            SplitIdx::LO(1),
            SplitIdx::LO(2),
            SplitIdx::HI(0), 
            SplitIdx::HI(1),
            SplitIdx::HI(2),
        )]
        split_idx: SplitIdx
    ) {
        let gen = &mut test_rng();
        let num_vars = 5; 
        for i in 0..100 {
            let n_args = 3;
            let split_idx = SplitIdx::HI(0);

            let data = Vec::rand_points::<BandersnatchConfig, _>(gen, DensePolyRndConfig {num_vars});
            let dense_data = data.iter().map(|p| p.to_dense(num_vars)).collect_vec();

            let out = Vec::algfn_map_split(data.as_slice().try_into().unwrap(), ArcedAlgFn::new(Arc::new(foo), 3, 2, 1), SplitIdx::HI(0), 1);
            let expected_out = map_over_poly(&dense_data.iter().map(|p| p.as_slice()).collect_vec().as_slice(), PolynomialMapping {
                exec: Arc::new(blah),
                degree: 1,
                num_i: 3,
                num_o: 2,
            });
            let (out0, out1) = out.iter().tee();
            let out0 = out0.step_by(2);
            let out1 = out1.skip(1).step_by(2);

            let segment_size = 1 << (match split_idx {
                SplitIdx::LO(var_idx) => { var_idx }
                SplitIdx::HI(var_idx) => { num_vars - 1 - var_idx }
            });
            
            let dense_out = out0.zip_eq(out1).map(|(l, r)| {
                l.to_dense(num_vars - 1).into_iter().chunks(segment_size).into_iter()
                    .interleave(r.to_dense(num_vars - 1).into_iter().chunks(segment_size).into_iter())
                    .flatten()
                    .collect_vec()
            }).collect_vec();

            assert_eq!(dense_out, expected_out);
        }
    }
}