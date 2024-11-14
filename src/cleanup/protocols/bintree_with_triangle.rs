use ark_ec::{CurveConfig, Group};
use ark_ec::twisted_edwards::{Affine, Projective};
use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
use ark_ff::PrimeField;
use ark_std::UniformRand;
use itertools::{repeat_n, Itertools};
use num_traits::Zero;
use crate::cleanup::proof_transcript::{ProofTranscript2, TProofTranscript2};
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::gkrs::{bintree_add, triangle_add};
use crate::cleanup::protocols::gkrs::bintree_add::{VecVecBintreeAdd, VecVecBintreeAddWG};
use crate::cleanup::protocols::gkrs::gkr::{GKRLayer, SimpleGKR};
use crate::cleanup::protocols::gkrs::split_map_gkr::SplitVecVecMapGKRAdvice;
use crate::cleanup::protocols::gkrs::triangle_add::{TriangleAdd, TriangleAddWG};
use crate::cleanup::protocols::splits::{SplitAt, SplitIdx};
use crate::cleanup::protocols::sumcheck::SinglePointClaims;
use crate::cleanup::utils::algfn::{IdAlgFn, RepeatedAlgFn};
use crate::cleanup::utils::arith::evaluate_poly;
use crate::polynomial::vecvec::{vecvec_map_split, VecVecPolynomial};
use crate::utils::{build_points, Densify, MapSplit, TwistedEdwardsConfig};


pub struct BintreeTriangleWG<F: PrimeField + TwistedEdwardsConfig> {
    advices: Vec<SplitVecVecMapGKRAdvice<F>>,
}

impl<F: PrimeField + TwistedEdwardsConfig> Iterator for BintreeTriangleWG<F> {
    type Item = SplitVecVecMapGKRAdvice<F>;

    fn next(&mut self) -> Option<Self::Item> {
        self.advices.pop()
    }
}

impl<F: PrimeField + TwistedEdwardsConfig> BintreeTriangleWG<F> {
    pub fn new(
        multirow_vars: usize,
        bucket_vars: usize,
        horizontal_vars: usize,
        inputs: Vec<VecVecPolynomial<F>>
    ) -> Self {
        let mut advices = bintree_add::builder::witness::build(
            SplitVecVecMapGKRAdvice::VecVecMAP(inputs),
            horizontal_vars,
            horizontal_vars,
        );
        let last: Vec<Vec<_>> = bintree_add::builder::witness::last_step(advices.last().as_ref().unwrap(), horizontal_vars - 1).into();
        let split_l1 = Vec::algfn_map_split(
            &last,
            IdAlgFn::new(3),
            SplitIdx::HI(multirow_vars),
            3,
        );
        let split_l2 = Vec::algfn_map_split(
            &split_l1,
            RepeatedAlgFn::new(IdAlgFn::new(3), 2),
            SplitIdx::HI(multirow_vars),
            3,
        );
        advices.push(SplitVecVecMapGKRAdvice::SPLIT(()));
        advices.push(SplitVecVecMapGKRAdvice::SPLIT(()));
        advices.extend(triangle_add::builder::witness::build(
            split_l2,
            multirow_vars + bucket_vars - 2,
            SplitIdx::HI(multirow_vars),
        ));

        Self {
            advices,
        }
    }
}

pub struct BintreeTriangle<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2> {
    pub multirow_vars: usize,
    pub bucket_vars: usize,
    pub horizontal_vars: usize,
    pub gkr: SimpleGKR<SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>, Transcript, BintreeTriangleWG<F>>,
}

impl<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2> BintreeTriangle<F, Transcript> {
    pub fn new(multirow_vars: usize, bucket_vars: usize, horizontal_vars: usize) -> Self {
        let mut layers = vec![];

        layers.extend(bintree_add::builder::protocol::build(
            multirow_vars + bucket_vars + horizontal_vars,
            horizontal_vars,
            horizontal_vars,
            false,
        ));
        layers.push(Box::new(SplitAt::new(
            SplitIdx::HI(multirow_vars),
            3,
        )));
        layers.push(Box::new(SplitAt::new(
            SplitIdx::HI(multirow_vars),
            3,
        )));
        layers.extend(triangle_add::builder::protocol::build(
            multirow_vars + bucket_vars - 2,
            SplitIdx::HI(multirow_vars),
        ));

        Self {
            multirow_vars,
            bucket_vars,
            horizontal_vars,
            gkr: SimpleGKR::new(layers),
        }
    }
}

impl<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2> Protocol2<Transcript> for BintreeTriangle<F, Transcript> {
    type ProverInput = BintreeTriangleWG<F>;
    type ProverOutput = ();
    type ClaimsBefore = SinglePointClaims<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        self.gkr.prove(transcript, claims, advice)
    }

    fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        self.gkr.verify(transcript, claims)

    }
}


#[cfg(test)]
mod tests {
    use crate::cleanup::protocols::gkrs::triangle_add;
    use super::*;
    #[test]
    fn integration() {
        let rng = &mut rand::thread_rng();
        let multirow_vars = 2;
        let bucket_vars = 4;
        let point_vars = 3;
        let total_num_vars = multirow_vars + bucket_vars + point_vars;

        let pre_inputs = VecVecPolynomial::rand_points_affine::<BandersnatchConfig, _>(rng, point_vars, multirow_vars + bucket_vars).to_vec();
        let inputs = vecvec_map_split(&pre_inputs, IdAlgFn::new(2), SplitIdx::LO(0), 2);
        let dense_input = inputs.to_dense(());

        let mut bintree_triangle_wg = BintreeTriangleWG::new(
            multirow_vars,
            bucket_vars,
            point_vars,
            inputs
        );
        
        let bintree_triangle = BintreeTriangle::new(
            multirow_vars,
            bucket_vars,
            point_vars,
        );
       
        let point = (0..multirow_vars).map(|_| <BandersnatchConfig as CurveConfig>::BaseField::rand(rng)).collect_vec();
        let num_vars = multirow_vars + bucket_vars;
        let dense_output: Vec<Vec<_>> = triangle_add::builder::witness::last_step(
            bintree_triangle_wg.advices.last().unwrap().into(),
            num_vars - 2 - SplitIdx::HI(multirow_vars).hi_usize(num_vars - 2)
        );

        let claims = SinglePointClaims {
            point: point.clone(),
            evs: dense_output.iter().map(|output| evaluate_poly(output, &point)).collect(),
        };

        let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");
        
        let (bintree_output_claims, _) = bintree_triangle.prove(&mut transcript_p, claims.clone(), bintree_triangle_wg);
        
        let proof = transcript_p.end();

        let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);
        
        let bintree_expected_claims = bintree_triangle.verify(&mut transcript_v, claims.clone());
        
        assert_eq!(bintree_output_claims, bintree_expected_claims);


        // Claim vs hand computed claim of input
        let result_point = bintree_expected_claims.point.clone();
        let original_claims = SinglePointClaims {
            point: result_point.clone(),
            evs: dense_input.iter().map(|output| evaluate_poly(output, &result_point)).collect(),
        };
        assert_eq!(bintree_expected_claims, original_claims);

        // witness

        let point_inputs =
            (0..pre_inputs[0].data.len()).map(|row_idx| {
                (0..pre_inputs[0].data[row_idx].len()).map(|col_idx| {
                    Affine::<BandersnatchConfig>::new(pre_inputs[0].data[row_idx][col_idx], pre_inputs[1].data[row_idx][col_idx])
                }).collect_vec()
            }).collect_vec();

        let expected_bucket_sums = point_inputs.iter().map(|row| {
            row.iter().sum::<Projective<BandersnatchConfig>>()
        })
            .chain(repeat_n(Projective::zero(), (1 << (multirow_vars + bucket_vars)) - point_inputs.len()))
            .collect_vec();
        
        let mut expected_multirow_sums = vec![Projective::zero(); 1 << multirow_vars];

        for multirow_idx in 0..(1 << multirow_vars) {
            for bucket_idx in 0..(1 << bucket_vars) {
                expected_multirow_sums[multirow_idx] += expected_bucket_sums[multirow_idx * (1 << bucket_vars) + bucket_idx] * <BandersnatchConfig as CurveConfig>::ScalarField::from(bucket_idx as u64);
            }
        }

        let output_points = build_points(&dense_output);

        let mut output_multirow_sums = vec![Projective::zero(); 1 << multirow_vars];
        for multirow_idx in 0..(1 << multirow_vars) {
            let mut coef = 1u64;
            for bucket_idx in 1..=bucket_vars {
                output_multirow_sums[multirow_idx] += output_points[bucket_idx][multirow_idx] * <BandersnatchConfig as CurveConfig>::ScalarField::from(coef);
                coef *= 2;
            }
        }

        assert_eq!(expected_multirow_sums, output_multirow_sums);
    }
}