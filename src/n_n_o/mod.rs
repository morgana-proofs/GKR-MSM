#![allow(unused_imports)]

use std::{marker::PhantomData};
use std::ops::{AddAssign, Sub, SubAssign};
use std::sync::Arc;

use ark_ff::{Field, PrimeField};
use ark_std::iterable::Iterable;

use itertools::Itertools;
use liblasso::{poly::{eq_poly::EqPolynomial, unipoly::{CompressedUniPoly, UniPoly}}};
use liblasso::poly::dense_mlpoly::DensePolynomial;
#[cfg(feature = "prof")]
use profi::{prof, prof_guard};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, once, ParallelIterator};

use crate::transcript::TranscriptSender;
use crate::{transcript::{Challenge, TranscriptReceiver}, utils::{make_gamma_pows, map_over_poly_legacy}};
use crate::copoly::{CopolyData, Copolynomial, EqPoly};
use crate::polynomial::fragmented::{FragmentedPoly, InterOp};
use crate::utils::{fix_var_bot};

use crate::protocol::protocol::{EvalClaim, MultiEvalClaim, PolynomialMapping, Protocol, ProtocolProver, ProtocolVerifier};
use crate::protocol::sumcheck::{SumcheckPolyMap, Splits, FragmentedLincomb, SumcheckPolyMapParams, SumcheckPolyMapProver, SumcheckPolyMapProof, SumcheckPolyMapVerifier, Sumcheckable,};


pub mod prover;
pub mod verifier;
pub mod non_native_equalizer;
pub mod n_n_sumcheck;
pub mod polynomial_with_zeros;

#[cfg(test)]
mod tests;

use prover::*;
use verifier::*;

// pub struct NNSumcheckPolyMap<F: PrimeField> {
//     phantom_data: PhantomData<F>
// }

// pub struct NNSplits<F: PrimeField> {
//     pub lpolys: Vec<FragmentedPoly<F>>,
//     pub rpolys: Vec<FragmentedPoly<F>>,
// }

// pub struct NNFragmentedLincomb<F: PrimeField> {
//     polys: Vec<FragmentedPoly<F>>,
//     splits: Option<NNSplits<F>>,
//     folded_f: Option<Arc<dyn Fn(&[F]) -> F + Sync + Send>>,
//     degree: usize,
// }


// impl<F: PrimeField> Protocol<F> for NNSumcheckPolyMap<F> {
//     type Prover = NNSumcheckPolyMapProver<F>;
//     type Verifier = NNSumcheckPolyMapVerifier<F>;
//     type ClaimsToReduce = MultiEvalClaim<F>;
//     type ClaimsNew = EvalClaim<F>;
//     type WitnessInput = Vec<FragmentedPoly<F>>;
//     type Trace = Vec<Vec<FragmentedPoly<F>>>;
//     type WitnessOutput = Vec<FragmentedPoly<F>>;
//     type Proof = NNSumcheckPolyMapProof<F>;
//     type Params = NNSumcheckPolyMapParams<F>;

//     fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
//         let out = FragmentedPoly::map_over_poly(&args, params.f.clone());
//         (vec![args], out)
//     }
// }

// pub struct NNSumcheckPolyMapVerifier<F: PrimeField> {
//     f: PolynomialMapping<F>,
//     num_vars: usize,
//     proof: NNSumcheckPolyMapProof<F>,
//     claims_to_reduce: MultiEvalClaim<F>,

//     f_folded: Option<Arc<dyn Fn(&[F]) -> F + Sync + Send>>,
//     current_sum: Option<F>,
//     current_poly: Option<UniPoly<F>>,
//     rs: Vec<F>,
// }

// pub struct NNSumcheckPolyMapProof<F: PrimeField> {
//     round_polys : Vec<CompressedUniPoly<F>>,
//     final_evaluations: Vec<F>,
// }

// #[derive(Clone)]
// pub struct NNSumcheckPolyMapParams<F: PrimeField> {
//     pub f: PolynomialMapping<F>,
//     pub num_vars: usize,
// }

// pub fn to_multieval<F: PrimeField>(claim: EvalClaim<F>) -> MultiEvalClaim<F> {
//     let points = vec![claim.point];
//     let evs = vec![(0..).zip(claim.evs.into_iter()).collect()];
//     MultiEvalClaim{points, evs}
// }

// fn make_folded_claim<F: PrimeField>(claims: &MultiEvalClaim<F>, gamma_pows: &[F]) -> F {
//     let mut i = 0;
//     (claims.evs.iter().enumerate()).fold(
//         F::zero(),
//         |acc, (_, evs)| {
//             let mut _acc = F::zero();
//             for ev in evs {
//                 _acc += ev.1 * gamma_pows[i];
//                 i += 1;
//             }
//             acc + _acc
//         }
//     )
// }

// fn make_folded_f<F: PrimeField>(claims: &MultiEvalClaim<F>, gamma_pows: &[F], f: &PolynomialMapping<F>)
//         -> Arc<dyn Fn(&[F]) -> F + Send + Sync>
// {
//     let claims = claims.clone();
//     let gamma_pows = gamma_pows.to_vec();
//     let PolynomialMapping{exec, degree: _, num_i, num_o: _} = f.clone();
//     Arc::new(
//         move |args: &[F]| {
//             #[cfg(feature = "prof")]
//             prof!("SumcheckPolyMapProver::folded_f");

//             assert_eq!(args.len(), num_i);
//             let out = exec(args);
//             let mut i = 0;
//             claims.evs.iter().enumerate().fold(
//                 F::zero(),
//                 |acc, (j, evs)| {
//                     let mut _acc = F::zero();
//                     for ev in evs {
//                         _acc += out[ev.0] * gamma_pows[i];
//                         i += 1;
//                     }
//                     acc + _acc
//                 }
//             )
//         }
//     )
// }



// #[cfg(test)]
// mod test {
//     use std::sync::{Arc, OnceLock};
//     use ark_bls12_381::G1Projective;
//     use ark_bls12_381::Fr;
//     use ark_std::{test_rng, UniformRand};
//     use itertools::Itertools;

//     use liblasso::utils::test_lib::TestTranscript;
//     use merlin::Transcript;
//     use crate::grand_add::affine_twisted_edwards_add_l1;
//     use crate::polynomial::fragmented::{Fragment, FragmentContent, FragmentedPoly, Shape};

//     use crate::transcript::{IndexedProofTranscript, TranscriptSender};

//     use super::*;

//     #[test]
//     fn tost_sumcheck_lite_simple_shape() {
//         let gen = &mut test_rng();

//         let num_vars: usize = 5;
//         let shape = Arc::new(OnceLock::new());
//         shape.get_or_init(||Shape::new(vec![Fragment {
//             mem_idx: 0,
//             len: 1 << 5,
//             content: FragmentContent::Data,
//             start: 0,
//         }], 0));
//         let polys: Vec<FragmentedPoly<Fr>> = (0..3).map(|_| FragmentedPoly::rand_with_shape(gen, shape.clone())).collect();

//         fn combfunc(i: &[Fr]) -> Vec<Fr> {
//             vec![i[0], i[1], i[2] * i[2] * i[0], i[2] * i[2] * i[0]]
//         }

//         let params = NNSumcheckPolyMapParams {
//             f: PolynomialMapping {
//                 exec: Arc::new(combfunc),
//                 degree: 3,
//                 num_i: 3,
//                 num_o: 4,
//             },
//             num_vars,
//         };

//         let (trace, image_polys) = NNSumcheckPolyMap::witness(polys.clone(), &params);

//         let point: Vec<Fr> = (0..(num_vars as u64)).map(|i| Fr::from(i * 13)).collect();
//         let claims : Vec<_> = image_polys.par_iter().enumerate().map(|(i, p)| (i, p.evaluate(&point))).collect();

//         let _point = point.clone();

//         let multiclaim = MultiEvalClaim {
//             points: vec![point],
//             evs: vec![claims.clone()],
//         };


//         let mut prover = NNSumcheckPolyMapProver::start(
//             multiclaim.clone(),
//             trace,
//             &params,
//         );

//         let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
//         let gamma_c = p_transcript.challenge_scalar(b"challenge_combine_outputs");
//         let mut res = prover.round(gamma_c, &mut p_transcript);
//         while res.is_none() {
//             let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
//             res = prover.round(challenge, &mut p_transcript);
//         }

//         println!("{:?}", p_transcript.transcript.log);

//         let (EvalClaim{point: proof_point, evs}, proof) = res.unwrap();
//         assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

//         let mut verifier = NNSumcheckPolyMapVerifier::start(
//             multiclaim,
//             proof,
//             &params,
//         );

//         let mut v_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));
//         let gamma_c = v_transcript.challenge_scalar(b"challenge_combine_outputs");
//         let mut res = verifier.round(gamma_c, &mut v_transcript);
//         while res.is_none() {
//             let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
//             res = verifier.round(challenge, &mut v_transcript);
//         }

//         println!("{:?}", v_transcript.transcript.log);

//         v_transcript.transcript.assert_end();

//         let EvalClaim{point: proof_point, evs} = res.unwrap();
//         assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

//     }
//     #[test]
//     fn mest_sumcheck_lite() {
//         let gen = &mut test_rng();

//         let num_vars: usize = 5;
//         let shape = Arc::new(OnceLock::new());
//         shape.get_or_init(||Shape::rand(gen, num_vars));
//         let polys: Vec<FragmentedPoly<Fr>> = (0..3).map(|_| FragmentedPoly::rand_with_shape(gen, shape.clone())).collect();

//         fn combfunc(i: &[Fr]) -> Vec<Fr> {
//             vec![i[0], i[1], i[2] * i[2] * i[0], i[2] * i[2] * i[0]]
//         }

//         let params = NNSumcheckPolyMapParams {
//             f: PolynomialMapping {
//                 exec: Arc::new(combfunc),
//                 degree: 3,
//                 num_i: 3,
//                 num_o: 4,
//             },
//             num_vars,
//         };

//         let (trace, image_polys) = NNSumcheckPolyMap::witness(polys.clone(), &params);


//         let point: Vec<Fr> = (0..(num_vars as u64)).map(|i| Fr::from(i * 13)).collect();
//         let claims : Vec<_> = image_polys.iter().enumerate().map(|(i, p)| (i, p.evaluate(&point))).collect();

//         let _point = point.clone();

//         let multiclaim = MultiEvalClaim {
//             points: vec![point],
//             evs: vec![claims.clone()],
//         };



//         let mut prover = NNSumcheckPolyMapProver::start(
//             multiclaim.clone(),
//             trace,
//             &params,
//         );

//         let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
//         let gamma_c = p_transcript.challenge_scalar(b"challenge_combine_outputs");
//         let mut res = prover.round(gamma_c, &mut p_transcript);
//         while res.is_none() {
//             let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
//             res = prover.round(challenge, &mut p_transcript);
//         }

//         println!("{:?}", p_transcript.transcript.log);

//         let (EvalClaim{point: proof_point, evs}, proof) = res.unwrap();
//         assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

//         let mut verifier = NNSumcheckPolyMapVerifier::start(
//             multiclaim,
//             proof,
//             &params,
//         );

//         let mut v_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));
//         let gamma_c = v_transcript.challenge_scalar(b"challenge_combine_outputs");
//         let mut res = verifier.round(gamma_c, &mut v_transcript);
//         while res.is_none() {
//             let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
//             res = verifier.round(challenge, &mut v_transcript);
//         }

//         println!("{:?}", v_transcript.transcript.log);

//         v_transcript.transcript.assert_end();

//         let EvalClaim{point: proof_point, evs} = res.unwrap();
//         assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

//     }

//     #[test]
//     fn tost_sumcheck_multiclaim() {
//         let gen = &mut test_rng();

//         let num_vars: usize = 5;
//         let num_points: usize = 3;
//         let num_polys: usize = 4;
//         let poly_eval_matrix = vec![
//             vec![1, 1, 0, 1, 0],
//             vec![1, 0, 1, 1, 0],
//             vec![1, 1, 0, 0, 1],
//         ];
//         let shape = Arc::new(OnceLock::new());
//         shape.get_or_init(||Shape::rand(gen, num_vars));
//         let polys: Vec<FragmentedPoly<Fr>> = (0..num_polys).map(|j| FragmentedPoly::rand_with_shape(gen, shape.clone())).collect();

//         fn combfunc(i: &[Fr]) -> Vec<Fr> {
//             vec![
//                 i[0],
//                 i[1],
//                 i[2] * i[2] * i[0],
//                 i[2] * i[2] * i[0],
//                 i[3] * i[2]
//             ]
//         }

//         let params = NNSumcheckPolyMapParams {
//             f: PolynomialMapping {
//                 exec: Arc::new(combfunc),
//                 degree: 3,
//                 num_i: 4,
//                 num_o: 5,
//             },
//             num_vars,
//         };

//         let (trace, image_polys) = NNSumcheckPolyMap::witness(polys.clone(), &params);

//         let points: Vec<Vec<Fr>> = (0..(num_points as u64)).map(|j| (0..(num_vars as u64)).map(|i| Fr::from(i * i * 13 + i * j + j )).collect()).collect();
//         let claims = poly_eval_matrix.iter().zip_eq(points.iter()).map(
//             |(selector, point)| {
//                 image_polys.iter().enumerate().zip_eq(selector.iter()).filter(|(_, &y)| y == 1).map(
//                     |((i, poly), _)| {
//                         (i, poly.evaluate(point))
//                     }
//                 ).collect()
//             }
//         ).collect();

//         let multiclaim = MultiEvalClaim {
//             points,
//             evs: claims,
//         };

//         let mut prover = NNSumcheckPolyMapProver::start(
//             multiclaim.clone(),
//             trace,
//             &params,
//         );

//         let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
//         let gamma_c = p_transcript.challenge_scalar(b"challenge_combine_outputs");
//         let mut res = prover.round(gamma_c, &mut p_transcript);
//         while res.is_none() {
//             let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
//             res = prover.round(challenge, &mut p_transcript);
//         }

//         println!("{:?}", p_transcript.transcript.log);

//         let (EvalClaim{point: proof_point, evs}, proof) = res.unwrap();
//         assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

//         let mut verifier = NNSumcheckPolyMapVerifier::start(
//             multiclaim,
//             proof,
//             &params,
//         );

//         let mut v_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));
//         let gamma_c = v_transcript.challenge_scalar(b"challenge_combine_outputs");
//         let mut res = verifier.round(gamma_c, &mut v_transcript);
//         while res.is_none() {
//             let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
//             res = verifier.round(challenge, &mut v_transcript);
//         }

//         println!("{:?}", v_transcript.transcript.log);

//         v_transcript.transcript.assert_end();

//         let EvalClaim{point: proof_point, evs} = res.unwrap();
//         assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());
//     }
// }
