use ark_ec::{CurveConfig, Group};
use ark_ec::twisted_edwards::{Affine, Projective};
use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
use ark_ff::PrimeField;
use ark_std::UniformRand;
use itertools::{repeat_n, Itertools};
use num_traits::Zero;
use tracing::instrument;
use crate::cleanup::polys::common::{Densify, MapSplit};
use crate::cleanup::proof_transcript::{ProofTranscript2, TProofTranscript2};
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::gkrs::{bintree_add, triangle_add};
use crate::cleanup::protocols::gkrs::gkr::{GKRLayer, SimpleGKR};
use crate::cleanup::protocols::gkrs::split_map_gkr::SplitVecVecMapGKRAdvice;
use crate::cleanup::protocols::splits::{SplitAt, SplitIdx};
use crate::cleanup::protocols::sumcheck::SinglePointClaims;
use crate::cleanup::utils::algfn::{IdAlgFn, RepeatedAlgFn};
use crate::cleanup::utils::arith::evaluate_poly;
use crate::cleanup::polys::vecvec::{VecVecPolynomial};
use crate::cleanup::protocols::gkrs::bintree_add::{VecVecBintreeAdd, VecVecBintreeAddWG};
use crate::cleanup::protocols::gkrs::triangle_add::{TriangleAdd, TriangleAddWG};
use crate::utils::{build_points, TwistedEdwardsConfig};


pub struct PippengerEndingWG<F: PrimeField + TwistedEdwardsConfig> {
    pub bintree_advices: VecVecBintreeAddWG<F>,
    pub triangle_advices: TriangleAddWG<F>,
}

impl<F: PrimeField + TwistedEdwardsConfig> PippengerEndingWG<F> {
    #[instrument(name="PippengerEndingWG::new", level="trace", skip_all)]
    pub fn new(
        multirow_vars: usize,
        bucket_vars: usize,
        horizontal_vars: usize,
        inputs: Vec<VecVecPolynomial<F>>
    ) -> Self {
        assert_eq!(inputs.len(), 6);

        let mut advices = bintree_add::builder::witness::build(
            SplitVecVecMapGKRAdvice::VecVecMAP(inputs.clone()),
            horizontal_vars,
            horizontal_vars,
            true,
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
        advices.push(SplitVecVecMapGKRAdvice::EMPTY(()));
        advices.push(SplitVecVecMapGKRAdvice::EMPTY(()));
        advices.extend(triangle_add::builder::witness::build(
            split_l2,
            multirow_vars + bucket_vars - 2,
            SplitIdx::HI(multirow_vars),
        ));

        let bintree_wg = VecVecBintreeAddWG::new(
            inputs,
            horizontal_vars,
            horizontal_vars,
            true,
        );
        let last: Vec<Vec<_>> = bintree_add::builder::witness::last_step(bintree_wg.advices.last().as_ref().unwrap(), horizontal_vars - 1).into();
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

        Self {
            bintree_advices: bintree_wg,
            triangle_advices: TriangleAddWG::new(
                split_l2,
                multirow_vars + bucket_vars - 2,
                SplitIdx::HI(multirow_vars),
            ),
        }
    }

    pub fn last(&self) -> Option<&Vec<Vec<F>>> {
        self.triangle_advices.advices.last().map(|v| v.into())
    }
}

pub struct PippengerBucketed<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2> {
    pub multirow_vars: usize,
    pub bucket_vars: usize,
    pub horizontal_vars: usize,
    pub bintree: VecVecBintreeAdd<F, Transcript>,
    pub splits: SplitAt<F>,
    pub triangle: TriangleAdd<F, Transcript>,
}

impl<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2> PippengerBucketed<F, Transcript> {
    pub fn new(multirow_vars: usize, bucket_vars: usize, horizontal_vars: usize) -> Self {
        Self {
            multirow_vars,
            bucket_vars,
            horizontal_vars,
            bintree: VecVecBintreeAdd::new(
                horizontal_vars,
                multirow_vars + bucket_vars + horizontal_vars,
                horizontal_vars,
                true,
            ),
            splits: SplitAt::new(
                SplitIdx::HI(multirow_vars),
                3,
            ),
            triangle: TriangleAdd::new(
                multirow_vars + bucket_vars - 2,
                SplitIdx::HI(multirow_vars),
            ),
        }
    }
}

impl<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2> Protocol2<Transcript> for PippengerBucketed<F, Transcript> {
    type ProverInput = PippengerEndingWG<F>;
    type ProverOutput = ();
    type ClaimsBefore = SinglePointClaims<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    #[instrument(name="PippengerBucketed::prove", level="debug", skip_all)]
    fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {

        let (claims, _) = self.triangle.prove(transcript, claims, advice.triangle_advices);
        let (claims, _) = self.splits.prove(transcript, claims, ());
        let (claims, _) = self.splits.prove(transcript, claims, ());
        let (claims, _) = self.bintree.prove(transcript, claims, advice.bintree_advices);
        (claims, ())
    }

    fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let claims = self.triangle.verify(transcript, claims);
        let claims = self.splits.verify(transcript, claims);
        let claims = self.splits.verify(transcript, claims);
        let claims = self.bintree.verify(transcript, claims);
        claims
    }
}


pub fn vecvec_domain<F: PrimeField>(input: &VecVecPolynomial<F>) -> VecVecPolynomial<F> {
    VecVecPolynomial::new(
        input.data.iter().map(|r| vec![F::one(); r.len()]).collect_vec(),
        F::zero(),
        F::zero(),
        input.row_logsize,
        input.col_logsize,
    )
}

#[cfg(test)]
mod tests {
    use num_traits::One;
    use crate::cleanup::protocols::gkrs::triangle_add;
    use super::*;
    #[test]
    fn integration() {
        let rng = &mut rand::thread_rng();
        let multirow_vars = 2;
        let bucket_vars = 4;
        let point_vars = 3;
        let total_num_vars = multirow_vars + bucket_vars + point_vars;
        type F = <BandersnatchConfig as CurveConfig>::BaseField;

        let pre_inputs = VecVecPolynomial::rand_points_affine::<BandersnatchConfig, _>(rng, point_vars, multirow_vars + bucket_vars).to_vec();
        let domain = [
            vecvec_domain(&pre_inputs[0]),
        ];
        
        let mut inputs = VecVecPolynomial::algfn_map_split(&pre_inputs, IdAlgFn::new(2), SplitIdx::LO(0), 2);
        inputs.extend(VecVecPolynomial::algfn_map_split(&domain, IdAlgFn::new(1), SplitIdx::LO(0), 1));
        let dense_input = inputs.to_dense(());

        let mut bintree_triangle_wg = PippengerEndingWG::new(
            multirow_vars,
            bucket_vars,
            point_vars,
            inputs
        );
        
        let ending = PippengerBucketed::new(
            multirow_vars,
            bucket_vars,
            point_vars,
        );
       
        let point = (0..multirow_vars).map(|_| <BandersnatchConfig as CurveConfig>::BaseField::rand(rng)).collect_vec();
        let num_vars = multirow_vars + bucket_vars;
        let dense_output: Vec<Vec<_>> = triangle_add::builder::witness::last_step(
            bintree_triangle_wg.triangle_advices.advices.last().unwrap().into(),
            num_vars - 2 - SplitIdx::HI(multirow_vars).hi_usize(num_vars - 2)
        );

        let claims = SinglePointClaims {
            point: point.clone(),
            evs: dense_output.iter().map(|output| evaluate_poly(output, &point)).collect(),
        };

        let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");
        
        let (bintree_output_claims, _) = ending.prove(&mut transcript_p, claims.clone(), bintree_triangle_wg);
        
        let proof = transcript_p.end();

        let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);
        
        let bintree_expected_claims = ending.verify(&mut transcript_v, claims.clone());
        
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