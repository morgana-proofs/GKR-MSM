// Implements partial inner products of dense vector-arranged and matrix arranged polynomials.

use std::marker::PhantomData;

use ark_ff::PrimeField;
use itertools::Itertools;
use rayon::{current_num_threads, iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator}, join, scope, slice::ParallelSlice};

use crate::{cleanup::{proof_transcript::{TProverTranscript, TVerifierTranscript}, protocol2::Protocol2, protocols::sumcheck::{PointClaim, SinglePointClaims}}, protocol::protocol::EvalClaim};


/// Splits large vector of length n into chunks of small size (length m) and computes inner products, arranging them in a vector of size n/m.
/// If n is not divisible by m, the function will panic. 
pub fn inner_prod_lo<F: PrimeField>(large: &[F], small: &[F]) -> Vec<F> {
    let m = small.len();
    let n = large.len();
    assert!(m > 0);
    assert!(n % m == 0);
    large.par_chunks(m).map(|chunk| {
        let mut acc = chunk[0] * small[0];
        for i in 1..m {
            acc += chunk[i] * small[i]
        }
        acc
    }).collect()
}

fn inner_prod_hi_nonpar<F: PrimeField>(large: &[F], small: &[F]) -> Vec<F> {
    let m = small.len();
    let n = large.len();
    let (first, large) = large.split_at(n/m);
    let mut ret = first.iter().map(|x| *x * small[0]).collect_vec();
    large.chunks(n / m).enumerate().map(|(i, chunk)| for j in 0..(n / m) {ret[j] += chunk[j] * small[i + 1]}).count();
    ret
}

/// For large vector of length n and small vector of length m, such that m | n,
/// splits it into m chunks, multiplies i-th chunk by small[i], and adds them together
pub fn inner_prod_hi<F: PrimeField>(large: &[F], small: &[F]) -> Vec<F> {
    let m = small.len();
    let n = large.len();
    assert!(m > 0);
    assert!(n % m == 0);
    if n == 0 {return vec![]}
    
    let factor = 8 * current_num_threads(); // somewhat ad hoc, chunks a bit finer than num_threads to improve load balancing in case m is not divisible by num_threads
    
    let by = (m + factor - 1) / factor;

    let mut results: Vec<Vec<F>> = small.par_chunks(by).zip(large.par_chunks(by * (n / m))).map(|(small, large)| inner_prod_hi_nonpar(large, small)).collect();

    let mut acc = results.pop().unwrap();

    for i in 0..results.len() {
        results[i].par_iter().zip(acc.par_iter_mut()).map(|(res, acc)| *acc += res).count();
    }

    acc
}

/// Matrix-arranged polynomial.
/// Columns are little-end, i.e. each column is a chunk of length y_size.
/// x_logsize and y_logsize are "true" log-dimensions of this polynomial, which is assumed to be formally appended with zeroes.
pub struct MatrixPoly<F> {
    pub x_size: usize,
    pub y_size: usize,
    pub x_logsize: usize,
    pub y_logsize: usize,

    pub values: Vec<F>,
}

impl<F> MatrixPoly<F> {
    pub fn new(x_size: usize, y_size: usize, x_logsize: usize, y_logsize: usize, values: Vec<F>) -> Self {
        assert!(1 << x_logsize >= x_size);
        assert!(1 << y_logsize >= y_size);
        assert!(values.len() == x_size * y_size);
        Self { x_size, y_size, x_logsize, y_logsize, values }
    }
}

fn log2(mut x: usize) -> usize {
    assert!(x > 0);
    x -= 1;
    
    let is_power_of_2 = (x.leading_zeros() + x.trailing_zeros()) == 1usize.leading_zeros();

    if is_power_of_2 {
        x.trailing_zeros() as usize + 1
    } else {
        (0usize.leading_zeros() - x.leading_zeros()) as usize
    }
}

pub struct NNOProtocol<F: PrimeField, NNF: PrimeField> {
    pub x_logsize: usize,
    pub y_size: usize, // (NF_bitsize + 63) / 64, i.e. amount of 64-bit limbs that is enough to fit NF element
    pub y_logsize: usize,
    _marker: PhantomData<(F, NNF)>,
}

impl<F: PrimeField, NNF: PrimeField> NNOProtocol<F, NNF> {
    pub fn new(x_logsize: usize) -> Self {
        let y_size = (NNF::MODULUS_BIT_SIZE as usize + 63) / 64;
        let y_logsize = log2(y_size);
        Self { x_logsize, y_size, y_logsize, _marker: PhantomData }
    }
}

/// Output claim of non native opening protocol.
pub struct NNOOutputClaim<F: PrimeField, NNF: PrimeField> {
    pub nn_point_lo: Vec<NNF>, //
    pub nn_point_hi: Vec<NNF>, // point in which our original polynomial was evaluated, split into 2 parts
    pub r_x: Vec<F>, //
    pub r_y: Vec<F>, // evaluation point

    pub native_repr_eval: F, // evaluation of native representation P(r_x, r_y)

    pub native_repr_nn_eq_lo_eval: F, // evaluation of eq_{nn_point_lo}(r_x[.. (x_logsize+1)/2], r_y)
    pub native_repr_nn_eq_hi_eval: F, // evaluation of eq_{nn_point_hi}(r_x[(x_logsize+1)/2 ..], r_y)
}

impl<F: PrimeField, NNF: PrimeField> Protocol2 for NNOProtocol<F, NNF> {
    type ProverInput = MatrixPoly<u64>;

    type ProverOutput = ();

    type ClaimsBefore = PointClaim<NNF>;

    type ClaimsAfter = NNOOutputClaim<F, NNF>;

    fn prove<PT: TProverTranscript>(&self, transcript: &mut PT, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        todo!()
    }

    fn verify<PT: TVerifierTranscript>(&self, transcript: &mut PT, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        todo!()
    }
}


#[cfg(test)]
mod tests {
    use ark_bls12_381::{G1Affine, G1Projective, g1::Config};
    use ark_ec::{CurveConfig, Group};
    use ark_std::{test_rng, UniformRand, Zero, One};
    use ark_ff::Field;
    use liblasso::poly::eq_poly::{self, EqPolynomial};
    use crate::cleanup::proof_transcript::ProofTranscript2;
    use super::*;
    type Fr = <Config as CurveConfig>::ScalarField;

    #[test]
    fn ips_work() {
        let rng = &mut test_rng();

        let m = 439;
        let n = m * 384;
        let large = (0..n).map(|_|Fr::rand(rng)).collect_vec();
        let small = (0..m).map(|_|Fr::rand(rng)).collect_vec();

        let mut expected_ip_lo = vec![Fr::zero(); n / m];
        for i in 0..n {
            expected_ip_lo[i / m] += large[i] * small[i % m]
        }
        let ip_lo = inner_prod_lo(&large, &small);
        assert_eq!(expected_ip_lo, ip_lo);

        let mut expected_ip_hi = vec![Fr::zero(); n / m];
        for i in 0..n {
            expected_ip_hi[i % (n / m)] += large[i] * small[i / (n / m)]
        }
        let ip_hi = inner_prod_hi(&large, &small);
        assert_eq!(expected_ip_hi, ip_hi);
    }

}