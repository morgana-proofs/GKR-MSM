use std::marker::PhantomData;

use ark_bls12_381::Fr;
use ark_ff::{BigInt, Field, PrimeField};
use itertools::Itertools;
use liblasso::poly::dense_mlpoly::DensePolynomial;
#[cfg(feature = "prof")]
use profi::prof;
use rayon::prelude::*;

use crate::protocol::protocol::MultiEvalClaim;

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


pub fn map_over_poly<F: PrimeField>(
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
            DensePolynomial::new(applications.iter().map(|v| v[idx]).collect())
        }).collect::<Vec<DensePolynomial::<F>>>().try_into().unwrap()
}


pub fn scale<F: Field + TwistedEdwardsConfig, T: Fn (&[F]) -> Vec<F>>(f: T) -> impl Fn (&[F]) -> Vec<F> {
    move |data: &[F]| -> Vec<F> {
        let (pts, factor) = data.split_at(data.len() - 1);
        f(&pts.to_vec()).iter().map(|p| *p * factor[0]).collect()
    }
}

pub fn fold_with_coef<F: Field>(evals: &[F], layer_coef: F) -> Vec<F> {
    assert_eq!(evals.len() % 2, 0);
    let half = evals.len() / 2;
    (0..half)
        .map(|i| evals[i] + layer_coef * (evals[half + i] - evals[i]))
        .collect()
}

pub fn split_vecs<F: PrimeField>(ins: &[DensePolynomial<F>]) -> Vec<DensePolynomial<F>> {
    let mut res = Vec::<DensePolynomial::<F>>::with_capacity(ins.len() * 2);
    for _i in 0..(ins.len() * 2) {
        res.push(DensePolynomial::new(vec![F::zero()]))
    }

    ins.iter().enumerate().map(|(idx, poly)| (res[idx], res[ins.len() + idx]) = poly.split(poly.len() / 2)).count();
    res
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

pub fn split_into_chunks_balanced<T>(arr: &[T], num_threads: usize) -> impl Iterator<Item = &[T]> + '_ {
    let l = arr.len();
    let base_size = l / num_threads;
    let num_large_chunks = l - base_size * num_threads;

    let (m_hi, m_lo) = arr.split_at(num_large_chunks * num_threads);
    let chunks_hi = m_hi.chunks(base_size + 1);
    let chunks_lo = m_lo.chunks(base_size);
    chunks_hi.chain(chunks_lo)
}

#[cfg(feature = "memprof")]
pub fn memprof(l: &str) {
    use jemalloc_ctl::{epoch, stats};
    epoch::advance().unwrap();
    let allocated = stats::allocated::read().unwrap();
    let resident = stats::resident::read().unwrap();
    println!("{}: {:.3}Gb ({} bytes) allocated / {:.3}Gb ({} bytes) resident", l, allocated as f64 / 1024f64 / 1024f64 / 1024f64, allocated, resident as f64 / 1024f64 / 1024f64 / 1024f64, resident);
}
