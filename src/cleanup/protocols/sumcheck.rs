use std::{marker::PhantomData, ptr};

use ark_ff::PrimeField;
use itertools::Itertools;
use liblasso::poly::unipoly::UniPoly;
use crate::{cleanup::{proof_transcript::{TProverTranscript, TVerifierTranscript}, protocol2::Protocol2}, protocol::sumcheckv2::Sumcheckable};


/// Given polynomial in coefficient form with linear term skipped, and sum P(0) + P(1), recovers full polynomial.
pub fn decompress_coefficients<F: PrimeField>(coeffs_wo_lin_term: &[F], sum: F) -> Vec<F> {
    let l = coeffs_wo_lin_term.len();
    let mut sum_minus_lterm = coeffs_wo_lin_term[0].double();
    for i in 1..l {
        sum_minus_lterm += coeffs_wo_lin_term[i];
    }
    let mut ret = Vec::with_capacity(l+1);
    ret.push(coeffs_wo_lin_term[0]);
    ret.push(sum - sum_minus_lterm);
    ret.extend_from_slice(&coeffs_wo_lin_term[1..]);
    ret
}

pub fn compress_coefficients<F: PrimeField>(coeffs: &[F]) -> Vec<F> {
    let mut ret = coeffs.to_vec();
    ret.remove(1);
    ret
}

pub fn evaluate_poly<F: PrimeField>(coeffs: &[F], x: F) -> F {
    let l = coeffs.len();
    if l == 0 {return F::zero()}
    let mut ret = coeffs[l-1];

    for i in 0..l-1 {
        ret *= x;
        ret += coeffs[l-2-i];
    }

    ret
}


/// A standard sumcheck verifier. To obtain real verifier, one needs to append it with combinator, and prepend (potentially) with folding round.
pub struct SumcheckVerifierConfig<I: ExactSizeIterator<Item = usize> + Clone + Send + Sync> {
    pub degrees: I,
}

impl<I: ExactSizeIterator<Item = usize> + Clone + Send + Sync> SumcheckVerifierConfig<I> {
    
    pub fn new(degrees: impl IntoIterator<IntoIter = I>) -> Self {
        Self { degrees : degrees.into_iter() }
    }

    pub fn num_vars(&self) -> usize {
        self.degrees.len()
    }

    pub fn bare_sumcheck_verifier<PT: TVerifierTranscript, F: PrimeField>(&self, pt: &mut PT, sum_claim: F) -> F {
        let degrees = self.degrees.clone().into_iter();
        let mut claim = sum_claim;
        for d in degrees {
            let msg = pt.read_scalars(d); // polynomial of degree d has d+1 coefficient, but linear term is ignored
            let poly = decompress_coefficients(&msg, claim);
            
            let x = pt.challenge(128);
            claim = evaluate_poly(&poly, x);
        }
        claim
    }
}

pub struct GenericSumcheckProtocol<F: PrimeField, I: ExactSizeIterator<Item = usize> + Clone + Send + Sync, S: Sumcheckable<F>> {
    pub config: SumcheckVerifierConfig<I>,
    pub _marker: PhantomData<(F, S)>
}

impl<F: PrimeField, I: ExactSizeIterator<Item = usize> + Clone + Send + Sync, S: Sumcheckable<F>> GenericSumcheckProtocol<F, I, S> {
    pub fn new(degrees: impl IntoIterator<IntoIter = I>) -> Self {
        Self { config: SumcheckVerifierConfig::new(degrees), _marker: PhantomData }
    }

    pub fn num_vars(&self) -> usize {
        self.config.num_vars()
    }
}

impl<F: PrimeField, I: ExactSizeIterator<Item = usize> + Clone + Send + Sync, S: Sumcheckable<F>> Protocol2 for GenericSumcheckProtocol<F, I, S> {
    type ProverInput = S;
    type ProverOutput = Vec<F>;
    type ClaimsBefore = F;
    type ClaimsAfter = F;

    fn prove<PT: TProverTranscript>(&self, pt: &mut PT, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let degrees = self.config.degrees.clone().into_iter();
        let mut claim = claims;
        let mut sumcheck_object = advice;

        for d in degrees {
            let poly = sumcheck_object.unipoly().as_vec(); // we should get our own type for compressed polys, or just switch to vectors
            let msg = compress_coefficients(&poly);
            assert!(msg.len() == d);
            pt.write_scalars(&msg);
            let x = pt.challenge(128);
            sumcheck_object.bind(x);
            claim = evaluate_poly(&poly, x);
        }
        (claim, sumcheck_object.final_evals())

    }

    fn verify<PT: TVerifierTranscript>(&self, pt: &mut PT, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        self.config.bare_sumcheck_verifier(pt, claims)
    }
}



pub trait AlgFnSingleOutput<F: PrimeField> : Clone + Sync + Send {
    /// Executes function.
    fn exec(&self, args: &[F]) -> F;
    /// Declares the degree.
    fn deg(&self) -> usize;
    /// Declares expected number of inputs.
    fn n_args(&self) -> usize;
}

/// A simple sumcheck object.
/// Not parallelized right now.
pub struct DenseSumcheckObject<F: PrimeField, Fun: AlgFnSingleOutput<F>> {
    polys: Vec<Vec<F>>,
    f: Fun,
    num_vars: usize,
    round_idx: usize,
    cached_unipoly: Option<UniPoly<F>>,
}

impl<F: PrimeField, Fun: AlgFnSingleOutput<F>> DenseSumcheckObject<F, Fun> {
    pub fn new(polys: Vec<Vec<F>>, f: Fun, num_vars: usize) -> Self {
        let l = polys.len();
        assert!(l == f.n_args());
        for i in 0..l {
            assert!(polys[i].len() == 1 << num_vars);
        }
        Self { polys, f, num_vars, round_idx: 0, cached_unipoly: None }
    }
}

pub fn bind_dense_poly<F: PrimeField>(poly: &mut Vec<F>, t: F) {
    let half = poly.len() / 2;
    for i in 0..half {
        poly[i] = poly[2*i] + t * (poly[2*i + 1] - poly[2*i]);
    }
    poly.truncate(half);
}

impl<F: PrimeField, Fun: AlgFnSingleOutput<F>> Sumcheckable<F> for DenseSumcheckObject<F, Fun> {
    fn bind(&mut self, t: F) {
        assert!(self.round_idx < self.num_vars, "the protocol has already ended");
        for poly in &mut self.polys {
            bind_dense_poly(poly, t);
        }
        self.round_idx += 1;
    }

    fn unipoly(&mut self) -> UniPoly<F> {
        assert!(self.round_idx < self.num_vars, "the protocol has already ended");
        match self.cached_unipoly.as_ref() {
            Some(p) => {return p.clone()},
            None => {
                let half = 1 << (self.num_vars - self.round_idx - 1);
                let n_polys = self.polys.len();
                
                let mut difs = vec![F::zero(); n_polys];
                let mut args = vec![F::zero(); n_polys];

                let mut acc = vec![F::zero(); self.f.deg() + 1];

                for i in 0..half {
                    for j in 0..n_polys {
                        args[j] = self.polys[j][2 * i];
                    }

                    acc[0] += self.f.exec(&args);

                    for j in 0..n_polys {
                        args[j] = self.polys[j][2 * i + 1]
                    }

                    acc[1] += self.f.exec(&args);

                    for j in 0..n_polys {
                        difs[j] = self.polys[j][2 * i + 1] - self.polys[j][2 * i]
                    }

                    for s in 2..(self.f.deg() + 1) {
                        for j in 0..n_polys {
                            args[j] += difs[j];
                        }

                        acc[s] += self.f.exec(&args);
                    }
                }

                self.cached_unipoly = Some(UniPoly::from_evals(&acc));
            }
        }
        self.cached_unipoly.as_ref().unwrap().clone()
        
    }

    fn final_evals(&self) -> Vec<F> {
        assert!(self.round_idx == self.num_vars, "can only call final evals after last round");
        self.polys.iter().map(|poly| poly[0]).collect()
    }
}



#[cfg(test)]
mod tests {
    use ark_bls12_381::{G1Affine, G1Projective, g1::Config};
    use ark_ec::{CurveConfig, Group};
    use ark_std::{test_rng, UniformRand};
    use super::*;

    type Fr = <Config as CurveConfig>::ScalarField;

    #[test]
    fn protocol2_verifier_accepts_prover() {


    }
}