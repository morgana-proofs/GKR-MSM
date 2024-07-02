#![allow(unused_imports)]

use std::sync::Arc;

use ark_ff::PrimeField;
use itertools::Itertools;
use liblasso::utils::math::Math;
#[cfg(feature = "prof")]
use profi::{prof, prof_guard};

use GKR_MSM::{
    protocol::protocol::{PolynomialMapping, Protocol},
    transcript::TranscriptSender,
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


use crate::example_utils::*;




// this function returns Vec<Vec<F>>
// this is your input table for the sumcheck
fn data<F: PrimeField>() -> Vec<Vec<F>>{
    (0..3).map(
        |i| vec![F::from((i % 2) as u64), F::one(), F::zero(), F::one(), F::from((i % 2) as u64), F::one(), F::zero(), F::one()]
    )
    .collect()
}

// this is the function(s) applied at the sumcheck
fn combfunc<F: PrimeField>(i: &[F],)-> Vec<F> {
    vec![i[0]*i[0] - i[0], i[0]*i[1]]
}

// this is the degree of the combfunc. 
// if degree is wrong, the answer will be wrong, but, probably, no panic?
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
println!("{:?}, {:?}, ", ans, num_vars);
ans
}


fn main(){
    let gen = &mut test_rng();
    let (polys, sumcheck_params) = prepare_input_polynomials::<Fr>();
    let points = points_to_check_claims_at(sumcheck_params.num_vars);

    let (trace, image_polys) = SumcheckPolyMap::witness(polys.clone(), &sumcheck_params);

    let multiclaim = prepare_claims(points, image_polys);

    let mut prover = SumcheckPolyMapProver::start(
        multiclaim.clone(),
        trace,
        &sumcheck_params,
    );

    let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
    let gamma_c = p_transcript.challenge_scalar(b"challenge_combine_outputs");
    let mut res = prover.round(gamma_c, &mut p_transcript);
    while res.is_none() {
        let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
        res = prover.round(challenge, &mut p_transcript);
    }


    let (EvalClaim{point: proof_point, evs}, proof) = res.unwrap();
    assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

    let mut verifier = SumcheckPolyMapVerifier::start(
        multiclaim,
        proof,
        &sumcheck_params,
    );

    let mut v_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));
    let gamma_c = v_transcript.challenge_scalar(b"challenge_combine_outputs");
    let mut res = verifier.round(gamma_c, &mut v_transcript);
    while res.is_none() {
        let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
        res = verifier.round(challenge, &mut v_transcript);
    }

    println!("{:?}", v_transcript.transcript.log);

    let EvalClaim{point: proof_point, evs} = res.unwrap();
    assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());
}

mod example_utils{
        
    // Suppose one wants to compute sum
    // sum_{y} P(x, y)C(y)
    // where P(x, y) is a multilinear function; x, y are multi-variables
    // 
    // Degree should be equal to the degree of combfunc

    use super::*;


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


    //evaluations of several polynomials in several points;
    //points : list of points
    //evs[k][_] = (i, y) means that i-th polynomial at points[k] is equal to y
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


