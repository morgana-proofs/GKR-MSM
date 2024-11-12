// use ark_ec::{CurveConfig, Group};
// use ark_ec::twisted_edwards::{Affine, Projective};
// use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
// use ark_ff::PrimeField;
// use ark_std::UniformRand;
// use itertools::{repeat_n, Itertools};
// use num_traits::Zero;
// use crate::cleanup::proof_transcript::{ProofTranscript2, TProofTranscript2};
// use crate::cleanup::protocol2::Protocol2;
// use crate::cleanup::protocols::gkrs::bintree::{VecVecBintreeAdd, VecVecBintreeAddWG};
// use crate::cleanup::protocols::gkrs::triangle_add::{TriangleAdd, TriangleAddWG};
// use crate::cleanup::protocols::splits::{SplitAt, SplitIdx};
// use crate::cleanup::protocols::sumcheck::SinglePointClaims;
// use crate::cleanup::utils::algfn::{IdAlgFn, RepeatedAlgFn};
// use crate::cleanup::utils::arith::evaluate_poly;
// use crate::polynomial::vecvec::{vecvec_map_split, VecVecPolynomial};
// use crate::utils::{build_points, Densify, MapSplit, TwistedEdwardsConfig};
// 
// 
// pub struct BintreeTriangleWG<F: PrimeField> {
//     triangle: TriangleAddWG<F>,
//     bintree: VecVecBintreeAddWG<F>,
// }
// 
// pub struct BintreeTriangle<F: PrimeField, Transcript: TProofTranscript2> {
//     pub multirow_vars: usize,
//     pub bucket_vars: usize,
//     pub horizontal_vars: usize,
//     pub bintree: VecVecBintreeAdd<F, Transcript>,
//     pub splits: SplitAt<F>,
//     pub triangle: TriangleAdd<F, Transcript>
// }
// 
// impl<F: PrimeField, Transcript: TProofTranscript2> BintreeTriangle<F, Transcript> {
//     pub fn new(multirow_vars: usize, bucket_vars: usize, horizontal_vars: usize) -> Self {
//         Self {
//             multirow_vars,
//             bucket_vars,
//             horizontal_vars,
//             bintree: VecVecBintreeAdd::new(
//                 horizontal_vars,
//                 multirow_vars + bucket_vars + horizontal_vars,
//                 horizontal_vars,
//                 false
//             ),
//             splits: SplitAt::new(
//                 SplitIdx::HI(multirow_vars),
//                 3,
//             ),
//             triangle: TriangleAdd::new(
//                 multirow_vars + bucket_vars - 2,
//                 SplitIdx::HI(multirow_vars),
//             ),
//         }
//     }
// }
// 
// impl<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2> Protocol2<Transcript> for BintreeTriangle<F, Transcript> {
//     type ProverInput = BintreeTriangleWG<F>;
//     type ProverOutput = ();
//     type ClaimsBefore = SinglePointClaims<F>;
//     type ClaimsAfter = SinglePointClaims<F>;
// 
//     fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
//         let (claims, _) = self.triangle.prove(transcript, claims, advice.triangle);
//         let (claims, _) = self.splits.prove(transcript, claims, ());
//         let (claims, _) = self.splits.prove(transcript, claims, ());
//         self.bintree.prove(transcript, claims, advice.bintree)
//     }
// 
//     fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
//         let claims = self.triangle.verify(transcript, claims);
//         let claims = self.splits.verify(transcript, claims);
//         let claims = self.splits.verify(transcript, claims);
//         self.bintree.verify(transcript, claims)
// 
//     }
// }
// 
// 
// #[cfg(test)]
// mod tests {
//     use super::*;
//     #[test]
//     fn integration() {
//         let rng = &mut rand::thread_rng();
//         let multirow_vars = 2;
//         let bucket_vars = 4;
//         let point_vars = 3;
//         let total_num_vars = multirow_vars + bucket_vars + point_vars;
// 
//         let pre_inputs = VecVecPolynomial::rand_points_affine::<BandersnatchConfig, _>(rng, point_vars, multirow_vars + bucket_vars).to_vec();
//         let inputs = vecvec_map_split(&pre_inputs, IdAlgFn::new(2), SplitIdx::LO(0), 2);
//         let dense_input = inputs.to_dense(());
// 
//         let mut bintree_wg = VecVecBintreeAddWG::new(
//             inputs,
//             point_vars,
//             point_vars,
//             false,
//         );
// 
//         let bt_out: Vec<Vec<_>> = bintree_wg.last.take().unwrap().into();
//         let split_l1 = Vec::algfn_map_split(
//             &bt_out,
//             IdAlgFn::new(3),
//             SplitIdx::HI(multirow_vars),
//             3,
//         );
// 
//         let split_l2 = Vec::algfn_map_split(
//             &split_l1,
//             RepeatedAlgFn::new(IdAlgFn::new(3), 2),
//             SplitIdx::HI(multirow_vars),
//             3,
//         );
// 
//         let mut triangle_wg = TriangleAddWG::new(
//             split_l2,
//             multirow_vars + bucket_vars - 2,
//             SplitIdx::HI(multirow_vars),
//         );
// 
//         let point = (0..multirow_vars).map(|_| <BandersnatchConfig as CurveConfig>::BaseField::rand(rng)).collect_vec();
//         let dense_output: Vec<Vec<_>> = triangle_wg.last.take().unwrap().into();
// 
//         let claims = SinglePointClaims {
//             point: point.clone(),
//             evs: dense_output.iter().map(|output| evaluate_poly(output, &point)).collect(),
//         };
// 
//         let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");
// 
//         let triangle_prover: TriangleAdd<_, ProofTranscript2> = TriangleAdd::new(multirow_vars + bucket_vars - 2, SplitIdx::HI(multirow_vars));
// 
//         #[cfg(debug_assertions)]
//         println!("{}", triangle_prover.describe());
// 
//         let (triangle_output_claims, _) = triangle_prover.prove(&mut transcript_p, claims.clone(), triangle_wg);
// 
//         let split_l2_prover = SplitAt::new(SplitIdx::HI(multirow_vars), 3);
//         let (split_l2_output_claims, _) = split_l2_prover.prove(&mut transcript_p, triangle_output_claims, ());
// 
//         let split_l1_prover = SplitAt::new(SplitIdx::HI(multirow_vars), 3);
//         let (split_l1_output_claims, _) = split_l1_prover.prove(&mut transcript_p, split_l2_output_claims, ());
// 
//         let bintree_prover = VecVecBintreeAdd::new(
//             point_vars,
//             total_num_vars,
//             point_vars,
//             false,
//         );
// 
//         #[cfg(debug_assertions)]
//         println!("{}", bintree_prover.describe());
// 
//         let (bintree_output_claims, _) = bintree_prover.prove(&mut transcript_p, split_l1_output_claims, bintree_wg);
// 
//         let proof = transcript_p.end();
// 
//         let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);
// 
//         let triangle_expected_claims = triangle_prover.verify(&mut transcript_v, claims.clone());
//         let l2_expected_claims = split_l2_prover.verify(&mut transcript_v, triangle_expected_claims);
//         let l1_expected_claims = split_l1_prover.verify(&mut transcript_v, l2_expected_claims);
//         let bintree_expected_claims = bintree_prover.verify(&mut transcript_v, l1_expected_claims);
// 
//         assert_eq!(bintree_output_claims, bintree_expected_claims);
// 
// 
//         // Claim vs hand computed claim of input
//         let result_point = bintree_expected_claims.point.clone();
//         let original_claims = SinglePointClaims {
//             point: result_point.clone(),
//             evs: dense_input.iter().map(|output| evaluate_poly(output, &result_point)).collect(),
//         };
//         assert_eq!(bintree_expected_claims, original_claims);
// 
//         // witness
// 
//         let point_inputs =
//             (0..pre_inputs[0].data.len()).map(|row_idx| {
//                 (0..pre_inputs[0].data[row_idx].len()).map(|col_idx| {
//                     Affine::<BandersnatchConfig>::new(pre_inputs[0].data[row_idx][col_idx], pre_inputs[1].data[row_idx][col_idx])
//                 }).collect_vec()
//             }).collect_vec();
// 
//         let expected_bucket_sums = point_inputs.iter().map(|row| {
//             row.iter().sum::<Projective<BandersnatchConfig>>()
//         })
//             .chain(repeat_n(Projective::zero(), (1 << (multirow_vars + bucket_vars)) - point_inputs.len()))
//             .collect_vec();
// 
//         let bintree_point_out: Vec<Projective<BandersnatchConfig>> = build_points(&bt_out).into_iter().flatten().collect_vec();
// 
//         assert_eq!(bintree_point_out.len(), expected_bucket_sums.len());
//         assert_eq!(bintree_point_out, expected_bucket_sums);
// 
//         let mut expected_multirow_sums = vec![Projective::zero(); 1 << multirow_vars];
// 
//         for multirow_idx in 0..(1 << multirow_vars) {
//             for bucket_idx in 0..(1 << bucket_vars) {
//                 expected_multirow_sums[multirow_idx] += expected_bucket_sums[multirow_idx * (1 << bucket_vars) + bucket_idx] * <BandersnatchConfig as CurveConfig>::ScalarField::from(bucket_idx as u64);
//             }
//         }
// 
//         let output_points = build_points(&dense_output);
// 
//         let mut output_multirow_sums = vec![Projective::zero(); 1 << multirow_vars];
//         for multirow_idx in 0..(1 << multirow_vars) {
//             let mut coef = 1u64;
//             for bucket_idx in 1..=bucket_vars {
//                 output_multirow_sums[multirow_idx] += output_points[bucket_idx][multirow_idx] * <BandersnatchConfig as CurveConfig>::ScalarField::from(coef);
//                 coef *= 2;
//             }
//         }
// 
//         assert_eq!(expected_multirow_sums, output_multirow_sums);
//     }
// 
// }