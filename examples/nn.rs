#![allow(unused_imports)]

// not finished

use std::{marker::PhantomData};
use std::ops::{AddAssign, Sub, SubAssign};

use ark_ff::{Field, PrimeField};
use ark_std::iterable::Iterable;

use itertools::Itertools;
use liblasso::{poly::{eq_poly::EqPolynomial, unipoly::{CompressedUniPoly, UniPoly}}};
use liblasso::poly::dense_mlpoly::DensePolynomial;
#[cfg(feature = "prof")]
use profi::{prof, prof_guard};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, once, ParallelIterator};

use GKR_MSM::transcript::TranscriptSender;
use GKR_MSM::{transcript::{Challenge, TranscriptReceiver}, utils::{make_gamma_pows, map_over_poly_legacy}};
use GKR_MSM::copoly::{CopolyData, Copolynomial, EqPoly};
use GKR_MSM::polynomial::fragmented::{FragmentedPoly, InterOp};
use GKR_MSM::utils::{fix_var_bot};

use GKR_MSM::protocol::protocol::{EvalClaim, MultiEvalClaim, PolynomialMapping, Protocol, ProtocolProver, ProtocolVerifier};
use GKR_MSM::protocol::sumcheck::{SumcheckPolyMap, Splits, FragmentedLincomb, SumcheckPolyMapParams, SumcheckPolyMapProver, SumcheckPolyMapProof, SumcheckPolyMapVerifier, Sumcheckable,};

use GKR_MSM::n_n_o::{*, prover::*, verifier::*};


use std::sync::{Arc, OnceLock};
use ark_bls12_381::G1Projective;
use ark_bls12_381::Fr;
use ark_std::{test_rng, UniformRand};

use liblasso::utils::test_lib::TestTranscript;
use merlin::Transcript;
use GKR_MSM::grand_add::affine_twisted_edwards_add_l1;
use GKR_MSM::polynomial::fragmented::{Fragment, FragmentContent, Shape};

use GKR_MSM::transcript::{IndexedProofTranscript};



fn combfunc<F: PrimeField>(i: &[F]) -> Vec<F> {
    vec![i[0], i[1], i[2] * i[2] * i[0], i[2] * i[2] * i[0]]
}

fn prepare_inputs<F: PrimeField>(){
    
    let gen = &mut test_rng();

    let num_vars: usize = 5;
    let shape = Arc::new(OnceLock::new());
    shape.get_or_init(||Shape::rand(gen, num_vars));
    let polys: Vec<FragmentedPoly<F>> = (0..3).map(|_| FragmentedPoly::rand_with_shape(gen, shape.clone())).collect();

    let params = SumcheckPolyMapParams {
        f: PolynomialMapping {
            exec: Arc::new(combfunc),
            degree: 3,
            num_i: 3,
            num_o: 4,
        },
        num_vars,
    };

    let (trace, image_polys) = SumcheckPolyMap::witness(polys.clone(), &params);


    let point: Vec<F> = (0..(num_vars as u64)).map(|i| F::from(i * 13)).collect();

}


// pub fn run_nn_opening<F: PrimeField, T>(
//     num_vars: usize,
//     polys: Vec<FragmentedPoly<F>>,
//     exec: Arc<dyn Fn(&[F]) -> Vec<F> + Send + Sync>,
//     degree: usize,
//     num_i: usize,
//     num_o: usize,
//     point: Vec<F>,
//     p_transcript: &mut T,
//     v_transcript: &mut T,
// )
// where T:  TranscriptReceiver<F> + TranscriptSender<F>,
// {

//     let params = NNSumcheckPolyMapParams {
//         f: PolynomialMapping {
//             exec,
//             degree,
//             num_i,
//             num_o,
//         },
//         num_vars,
//     };

//     let (trace, image_polys) = NNSumcheckPolyMap::witness(polys.clone(), &params);

//     let claims : Vec<_> = image_polys.par_iter().enumerate().map(|(i, p)| (i, p.evaluate(&point))).collect();

//     let _point = point.clone();

//     let multiclaim = MultiEvalClaim {
//         points: vec![point],
//         evs: vec![claims.clone()],
//     };


//     let mut prover = NNSumcheckPolyMapProver::start(
//         multiclaim.clone(),
//         trace,
//         &params,
//     );

//     let gamma_c = p_transcript.challenge_scalar(b"challenge_combine_outputs");
//     let mut res = prover.round(gamma_c, p_transcript);
//     while res.is_none() {
//         let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
//         res = prover.round(challenge, p_transcript);
//     }

//     //println!("{:?}", p_transcript.transcript.log);

//     let (EvalClaim{point: proof_point, evs}, proof) = res.unwrap();
//     assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

//     let mut verifier = NNSumcheckPolyMapVerifier::start(
//         multiclaim,
//         proof,
//         &params,
//     );

//     let gamma_c = v_transcript.challenge_scalar(b"challenge_combine_outputs");
//     let mut res = verifier.round(gamma_c, v_transcript);
//     while res.is_none() {
//         let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
//         res = verifier.round(challenge, v_transcript);
//     }

//     //println!("{:?}", v_transcript.transcript.log);

//     //v_transcript.transcript.assert_end();

//     let EvalClaim{point: proof_point, evs} = res.unwrap();
//     assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());


// }


fn main(){
    //prepare_inputs();

    
    let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
    let mut v_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));
    //run_nn_opening(num_vars, polys, exec, degree, num_i, num_o, point, p_transcript, v_transcript)
}