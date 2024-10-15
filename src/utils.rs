use std::marker::PhantomData;
use std::mem::{transmute, MaybeUninit};
use std::ops::{Add, Mul, Sub};
use std::ptr::read;

use ark_bls12_381::Fr;
use ark_ff::{BigInt, Field, PrimeField};
use ark_std::rand::Rng;
use ark_std::UniformRand;
use hashcaster::ptr_utils::{AsSharedMUMutPtr, UninitArr, UnsafeIndexRawMut};
use itertools::Itertools;
use liblasso::poly::dense_mlpoly::DensePolynomial;
#[cfg(feature = "prof")]
use profi::prof;
use rayon::prelude::*;
use crate::protocol::protocol::{MultiEvalClaim, PolynomialMapping};

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


pub fn make_gamma_pows<F: PrimeField>(claims: &MultiEvalClaim<F>, gamma: F) -> Vec<F> {
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
    use ark_ed_on_bls12_381_bandersnatch::Fr;
    use ark_std::{test_rng, UniformRand};
    use itertools::Itertools;
    use num_traits::One;
    use crate::utils::{eq_poly_sequence_from_multiplier, padded_eq_poly_sequence};

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
}