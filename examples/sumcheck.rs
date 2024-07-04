#![allow(unused_imports)]

use std::sync::Arc;

use ark_ff::PrimeField;
use itertools::Itertools;
use liblasso::utils::math::Math;
#[cfg(feature = "prof")]
use profi::{prof, prof_guard};

use GKR_MSM::{
    protocol::protocol::{PolynomialMapping, Protocol},
    transcript::{self, TranscriptReceiver, TranscriptSender},
};
use GKR_MSM::nested_poly::NestedPolynomial;

use num_traits::{One, Zero};

use ark_bls12_381::Fr;
use ark_bls12_381::Fq;
use ark_bls12_381::G1Projective;
use ark_ff::{MontBackend};
use GKR_MSM::nested_poly::NestedPoly;
use GKR_MSM::protocol::protocol::MultiEvalClaim;
use GKR_MSM::protocol::protocol::{ProtocolVerifier, ProtocolProver, EvalClaim};
use GKR_MSM::protocol::sumcheck::{*, SumcheckPolyMapVerifier, SumcheckPolyMapProver};
use GKR_MSM::transcript::Challenge;
use GKR_MSM::transcript::IndexedProofTranscript;
use liblasso::utils::test_lib::TestTranscript;

use ark_std::{
    test_rng,
    rand::seq::SliceRandom,
};

use crate::example_utils::*;

// To run this example, you need to provide the next 4 functions

// todo: add description of what it really does

// this function returns Vec<Vec<F>>
// this is your input table for the sumcheck
fn data<F: PrimeField>() -> Vec<Vec<F>>{
    let gen = &mut test_rng();
    (0..4).map(
        |i| vec![F::from((i % 2) as u64), F::one(), F::zero(), F::one(), F::from((i % 2) as u64), F::zero(), F::one()]
    )
    .collect()
}

// this is the function(s) applied at the sumcheck
fn combfunc<F: PrimeField>(i: &[F],)-> Vec<F> {
    vec![i[0]*i[0] - i[0], i[0]*i[1]]
}

// this is the degree of the combfunc. 
// if degree is wrong, it panics
fn degree() -> usize{
    2
}

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
    let (polys, sumcheck_params, trace, multiclaim) = prepare_inputs();

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
    println!("Hurray, you sumchecked! num_i = {}", sumcheck_params.f.num_i);
}

mod example_utils{
    use super::*;

    
    pub(crate) fn prepare_inputs
        <F : PrimeField>
            () -> (Vec<NestedPolynomial<F>>, SumcheckPolyMapParams<F>, Vec<Vec<NestedPolynomial<F>>>, MultiEvalClaim<F>)
        {
            
            let (polys, sumcheck_params) = prepare_input_polynomials::<F>();
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


    pub(crate) fn prepare_input_polynomials<F : PrimeField>() 
        -> (Vec<NestedPolynomial<F>>, SumcheckPolyMapParams<F>)
        {
        // here we compute the number of inputs and the number of variables needed for the data given
        let values = data();

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

        let degree = degree();
        // this computes the number of outputs of combfunc
        // and panics if not enough inputs
        let test_vec = vec![F::zero(); num_i];
        let num_o = combfunc(&test_vec[..num_i]).len();

        (
            polys, 
            SumcheckPolyMapParams {
                f: PolynomialMapping {
                    exec: Arc::new(combfunc::<F>),
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

}


