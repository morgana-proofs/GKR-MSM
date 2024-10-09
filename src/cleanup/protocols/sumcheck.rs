use std::marker::PhantomData;

use ark_ff::PrimeField;
use itertools::Itertools;
use crate::{cleanup::{proof_transcript::TVerifierTranscript, protocol2::Protocol2}, protocol::sumcheckv2::Sumcheckable};


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
pub struct SumcheckVerifierConfig<I: IntoIterator<Item = usize> + Clone + Send + Sync> {
    pub degrees: I,
    pub num_rounds: usize,
}

impl<I: IntoIterator<Item = usize> + Clone + Send + Sync> SumcheckVerifierConfig<I> {
    
    pub fn new(degrees: I, num_rounds: usize) -> Self {
        Self { degrees, num_rounds }
    }

    pub fn bare_sumcheck_verifier<PT: TVerifierTranscript, F: PrimeField>(&self, pt: &mut PT, sum_claim: F) -> F {
        let degrees = self.degrees.clone().into_iter();
        let mut claim = sum_claim;
        let mut ctr = 0;
        for d in degrees {
            let msg = pt.read_scalars(d); // polynomial of degree d has d+1 coefficient, but linear term is ignored
            let poly = decompress_coefficients(&msg, claim);
            
            let x = pt.challenge(128);
            claim = evaluate_poly(&poly, x);
            ctr += 1;
        }
        assert!(ctr == self.num_rounds);
        claim
    }
}

pub struct GenericSumcheckProtocol<F: PrimeField, I: IntoIterator<Item = usize> + Clone + Send + Sync, S: Sumcheckable<F>> {
    pub config: SumcheckVerifierConfig<I>,
    pub _marker: PhantomData<(F, S)>
}

impl<F: PrimeField, I: IntoIterator<Item = usize> + Clone + Send + Sync, S: Sumcheckable<F>> GenericSumcheckProtocol<F, I, S> {
    pub fn new(degrees: I, num_rounds: usize) -> Self {
        Self { config: SumcheckVerifierConfig::new(degrees, num_rounds), _marker: PhantomData }
    }
}

impl<F: PrimeField, I: IntoIterator<Item = usize> + Clone + Send + Sync, S: Sumcheckable<F>> Protocol2 for GenericSumcheckProtocol<F, I, S> {
    type ProverInput = S;

    type ProverOutput = Vec<F>;

    type ClaimsBefore = F;

    type ClaimsAfter = F;

    fn prove<PT: crate::cleanup::proof_transcript::TProverTranscript>(&self, pt: &mut PT, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let degrees = self.config.degrees.clone().into_iter();
        let mut claim = claims;
        let mut ctr = 0;
        let mut sumcheck_object = advice;

        for d in degrees {
            let poly = sumcheck_object.unipoly().as_vec(); // we should get our own type for compressed polys, or just switch to vectors
            let msg = compress_coefficients(&poly);
            assert!(msg.len() == d);
            pt.write_scalars(&msg);
            let x = pt.challenge(128);
            sumcheck_object.bind(&x);
            claim = evaluate_poly(&poly, x);
            ctr += 1;
        }
        assert!(ctr == self.config.num_rounds);
        (claim, sumcheck_object.final_evals())

    }

    fn verify<PT: TVerifierTranscript>(&self, pt: &mut PT, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        self.config.bare_sumcheck_verifier(pt, claims)
    }
}