#![allow(unused_imports)]

use std::sync::Arc;

use ark_ff::PrimeField;
use itertools::Itertools;
use liblasso::utils::math::Math;
#[cfg(feature = "prof")]
use profi::{prof, prof_guard};

use GKR_MSM::{
    non_native_opening, protocol::protocol::{PolynomialMapping, Protocol}, transcript::{self, TranscriptReceiver, TranscriptSender}
};
use GKR_MSM::nested_poly::NestedPolynomial;

use num_traits::{One, Zero};

use ark_bls12_381::Fr;
use ark_bls12_381::Fq;
use ark_bls12_381::G1Projective;
use ark_ff::{MontBackend};
use ark_std::{test_rng};
use GKR_MSM::nested_poly::NestedPoly;
use GKR_MSM::protocol::protocol::MultiEvalClaim;
use GKR_MSM::protocol::protocol::{ProtocolVerifier, ProtocolProver, EvalClaim};
use GKR_MSM::protocol::sumcheck::{*, SumcheckPolyMapVerifier, SumcheckPolyMapProver};
use GKR_MSM::transcript::Challenge;
use GKR_MSM::transcript::IndexedProofTranscript;
use liblasso::utils::test_lib::TestTranscript;

use ark_std::rand::seq::SliceRandom;

use crate::example_utils::*;

// To run this example, you need to provide the next 4 functions

// todo: add description of what it really does

// this function returns Vec<Vec<F>>
// this is your input table for the sumcheck
// the inputs should be 0 or 1
fn coeffs_bool(non_native_modulus_size_in_bits: usize) -> Vec<Vec<bool>>{
    let num_i = 5;
    (0..num_i).map(
        |i| 
        {
            (0..non_native_modulus_size_in_bits)
                .map(|j| (j as u64/2u64.pow(i)) % 2 != 0)
                .collect()
        }
    )
    .collect()
}

// points where you want to open the argument
fn points_to_check_claims_at<F: PrimeField>(num_vars: usize) -> Vec<Vec<F>> 
{
    let ans = (0..2).map(
        |j| 
        (0..(num_vars as u64)).map(|i| F::from(2*i + j)).collect()
    )
    .collect();
    ans
}


fn adding_challenges
    <F : PrimeField,
     T: TranscriptSender<F> + TranscriptReceiver<F>>
    (transcript: &mut T,
     label: &'static [u8]) -> Challenge<F> 
{
    // one option: add "random" challenges to the transcript the proper way
    // transcript.challenge_scalar(label)

    //another option: add your own "random" challenges
    Challenge{
        value: F::from(0u64)
    }
}


fn main(){
    let non_native_modulus_size_in_bits = Fq::MODULUS_BIT_SIZE as usize;

    let (polys, sumcheck_params, trace, multiclaim) = prepare_inputs(non_native_modulus_size_in_bits);

    // prover running
    let mut prover = SumcheckPolyMapProver::start(
        multiclaim.clone(),
        trace,
        &sumcheck_params,
    );
    
    let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
    let (EvalClaim{point: proof_point, evs}, proof) = run_prover(&mut prover, &mut p_transcript);

    assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());
    println!("Prover has finished");
    println!("Prover transcript log {:?}", p_transcript.transcript.log);

    // verifier running
    let mut verifier = SumcheckPolyMapVerifier::start(
        multiclaim,
        proof,
        &sumcheck_params,
    );

    let mut v_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));
    let EvalClaim{point: proof_point, evs} = run_verifier(&mut verifier, &mut v_transcript);
    
    assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());
    println!("Verifier has finished");
    println!("Verifier transcript log {:?}", v_transcript.transcript.log);
    println!("Hurray, you sumchecked!");
}

mod example_utils{
    use super::*;

    
    pub(crate) fn prepare_inputs
        <F : PrimeField>
            (non_native_modulus_size_in_bits: usize) -> (Vec<NestedPolynomial<F>>, SumcheckPolyMapParams<F>, Vec<Vec<NestedPolynomial<F>>>, MultiEvalClaim<F>)
        {
            
            let (polys, sumcheck_params) = prepare_input_polynomials::<F>(non_native_modulus_size_in_bits);
            let points = points_to_check_claims_at(sumcheck_params.num_vars);

            let (trace, image_polys) = SumcheckPolyMap::witness(polys.clone(), &sumcheck_params);
            let multiclaim = prepare_claims(points, image_polys);
            (polys, sumcheck_params, trace, multiclaim)
        }


    pub(crate) fn run_prover
        <F : PrimeField,
        T: TranscriptSender<F> + TranscriptReceiver<F>>
            (prover: &mut  SumcheckPolyMapProver<F>,
            p_transcript: &mut T) -> (EvalClaim<F>, SumcheckPolyMapProof<F>)
        {
            let gamma_c = adding_challenges(p_transcript, b"challenge_combine_outputs");
            let mut res = prover.round(gamma_c, p_transcript);
            while res.is_none() {
                let challenge = adding_challenges(p_transcript, b"challenge_nextround");
                res = prover.round(challenge, p_transcript);
            }

            res.unwrap()
        }

    
    pub(crate) fn run_verifier
        <F : PrimeField,
        T: TranscriptSender<F> + TranscriptReceiver<F>>
            (verifier: &mut  SumcheckPolyMapVerifier<F>,
            v_transcript: &mut T) -> EvalClaim<F>
        {
            let gamma_c = adding_challenges(v_transcript, b"challenge_combine_outputs");
            let mut res = verifier.round(gamma_c, v_transcript);
            while res.is_none() {
                let challenge = adding_challenges(v_transcript, b"challenge_nextround");
                res = verifier.round(challenge, v_transcript);
            }

            res.unwrap()
        }


    pub(crate) fn prepare_input_polynomials<F : PrimeField>(non_native_modulus_size_in_bits: usize) 
        -> (Vec<NestedPolynomial<F>>, SumcheckPolyMapParams<F>)
        {
        // here we compute the number of inputs and the number of variables needed for the data given
        let values_bool = coeffs_bool(non_native_modulus_size_in_bits);
        let values: Vec<Vec<_>> = values_bool.iter()
                                .map(|v| v.clone().iter().map(|&x| F::from(x as u64)).collect())
                                .collect();

        let num_i = values.len();
        let mut num_vars = 0;
        let polys: Vec<NestedPolynomial<F>> = values.iter()
            .map(|v| 
                {
                    num_vars = num_vars.max(v.len().log_2());
                    let my_nested_poly = NestedPoly::from_values(v.clone(), F::zero());
                    NestedPolynomial::new(my_nested_poly, vec![num_vars])
                })
            .collect();

        let degree = DEGREE_func_first_part;
        // this computes the number of outputs of func_first_part
        // and panics if not enough inputs
        let test_vec = vec![F::zero(); num_i];
        let num_o = func_first_part(&test_vec[..num_i]).len();

        (
            polys, 
            SumcheckPolyMapParams {
                f: PolynomialMapping {
                    exec: Arc::new(func_first_part::<F>),
                    degree,
                    num_i,
                    num_o,
                },
                num_vars,
            }
        )

    }


    pub(crate) fn prepare_claims<F: PrimeField>(
        points: Vec<Vec<F>>,
        image_polys: Vec<NestedPolynomial<F>>,
    ) -> MultiEvalClaim<F>{
        let mut claims: Vec<Vec<(usize, F)>> = vec![];
        points.iter()
            .map( |point|
                {
                    claims.push(
                        image_polys.iter().enumerate().map(|(i, p)| (i, p.evaluate(&point))).collect());
                    }
            )
            .count();
        
        MultiEvalClaim {
            points,
            evs: claims,
        }
    }

    pub(crate) fn func_first_part<F: PrimeField>(i: &[F], num_i: usize)-> Vec<F> {
        (0..num_i-1)
            .map(|j| i[j]*i[j] - i[j])
            .chain(
                (0..num_i-1)
                    .map(|j | i[j]*i[num_i])
                    )
            .collect()
    }

    // pub(crate) fn func_multiplication<F: PrimeField>(i: &[F], num_i: usize)-> Vec<F> {
    //     (0..num_i).map(|j| i[j]*i[num_i]).collect()
    // }

    // this is the degree of the func_first_part. 
    // if degree is wrong, it panics
    pub(crate) const DEGREE_func_first_part: usize = 2;


}


