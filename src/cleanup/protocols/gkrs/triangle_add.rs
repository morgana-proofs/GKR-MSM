use std::fmt::{Display, Formatter};
use ark_ff::PrimeField;
use merlin::Transcript;
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::gkrs::bintree_add::AdditionStep;
use crate::cleanup::protocols::gkrs::gkr::{GKRLayer, SimpleGKR};
use crate::cleanup::protocols::gkrs::split_map_gkr::SplitVecVecMapGKRAdvice;
use crate::cleanup::protocols::splits::{SplitAt, SplitIdx};
use crate::cleanup::protocols::sumcheck::{DenseEqSumcheck, SinglePointClaims};
use crate::cleanup::protocols::sumchecks::dense_eq::DenseDeg2Sumcheck;
use crate::cleanup::utils::algfn::{RepeatedAlgFn, StackedAlgFn};
use crate::cleanup::utils::twisted_edwards_ops::algfns::{triangle_twisted_edwards_add_l1, twisted_edwards_add_l1, twisted_edwards_add_l2, twisted_edwards_add_l3};
use crate::utils::{MapSplit, TwistedEdwardsConfig};

#[derive(Debug)]
pub struct TriangleAddWG<F: PrimeField> {
    pub advices:  Vec<SplitVecVecMapGKRAdvice<F>>,
}
impl<F: PrimeField> Display for TriangleAddWG<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.advices.iter().map(|a| {
            write!(f, "{}\n", a)
        }).count();
        write!(f, "\n")
    }
}
impl<F: PrimeField + TwistedEdwardsConfig> TriangleAddWG<F> {
    pub fn new(
        advice: Vec<Vec<F>>,
        num_vars: usize,
        split_idx: SplitIdx,
    ) -> Self {
        let mut advices = builder::witness::build(
            advice,
            num_vars,
            split_idx,
        );
        Self {
            advices,
        }
    }

}

impl<F: PrimeField> Iterator for TriangleAddWG<F> {
    type Item = SplitVecVecMapGKRAdvice<F>;

    fn next(&mut self) -> Option<Self::Item> {
        self.advices.pop()
    }
}


pub struct TriangleAdd<F: PrimeField, Transcript: TProofTranscript2> {
    gkr: SimpleGKR<SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>, Transcript, TriangleAddWG<F>>,
    split_var: SplitIdx,
}

impl<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2> TriangleAdd<F, Transcript> {
    pub fn new(
        num_vars: usize,
        split_var: SplitIdx,
    ) -> Self {

        Self {
            gkr: SimpleGKR::new(builder::protocol::build(num_vars, split_var)),
            split_var,
        }
    }


    #[cfg(debug_assertions)]
    pub fn describe(&self) -> String {
        format!("Triangle Add {} ", self.gkr.description())
    }
}

pub mod builder {

    pub mod witness {
        use ark_ff::PrimeField;
        use crate::cleanup::proof_transcript::TProofTranscript2;
        use crate::cleanup::protocols::gkrs::bintree_add::AdditionStep;
        use crate::cleanup::protocols::gkrs::gkr::GKRLayer;
        use crate::cleanup::protocols::gkrs::split_map_gkr::SplitVecVecMapGKRAdvice;
        use crate::cleanup::protocols::splits::{SplitAt, SplitIdx};
        use crate::cleanup::protocols::sumcheck::SinglePointClaims;
        use crate::cleanup::protocols::sumchecks::dense_eq::DenseDeg2Sumcheck;
        use crate::cleanup::utils::algfn::{RepeatedAlgFn, StackedAlgFn};
        use crate::cleanup::utils::twisted_edwards_ops::algfns::{triangle_twisted_edwards_add_l1, twisted_edwards_add_l1, twisted_edwards_add_l2, twisted_edwards_add_l3};
        use crate::utils::{MapSplit, TwistedEdwardsConfig};
        
        pub fn last_step<F: PrimeField + TwistedEdwardsConfig>(
            advice: &Vec<Vec<F>>,
            layer_idx: usize,
        ) -> Vec<Vec<F>> {
            Vec::algfn_map(
                advice,
                RepeatedAlgFn::new(
                    twisted_edwards_add_l3(),
                    layer_idx + 3,
                ),
            )
        }
        
        pub fn build<F: PrimeField + TwistedEdwardsConfig>(
            advice: Vec<Vec<F>>,
            num_vars: usize,
            split_idx: SplitIdx,
        ) -> Vec<SplitVecVecMapGKRAdvice<F>> {
            let mut advice = Some(advice);
            let mut advices = vec![];
            let split_idx = split_idx.to_hi(num_vars);
            let num_layers = num_vars - split_idx.hi_usize(num_vars);

            for layer_idx in 0..=num_layers {
                for step in AdditionStep::all() {
                    let next = make_step(advice.as_ref().unwrap(), step, layer_idx, num_layers, split_idx);
                    advices.push(SplitVecVecMapGKRAdvice::DenseMAP(advice.unwrap()));

                    advice = next;
                }
                if layer_idx < num_layers {
                    advices.push(SplitVecVecMapGKRAdvice::EMPTY(()))
                }
            }

            advices
        }

        fn make_step<F: PrimeField + TwistedEdwardsConfig>(advice: &[Vec<F>], addition_step: AdditionStep, layer_idx: usize, num_vars: usize, split_idx: SplitIdx) -> Option<Vec<Vec<F>>> {
            match (addition_step, num_vars == layer_idx) {
                (AdditionStep::L1, _) => {
                    Some(Vec::algfn_map(advice, StackedAlgFn::new(
                        triangle_twisted_edwards_add_l1(),
                        RepeatedAlgFn::new(
                            twisted_edwards_add_l1(),
                            layer_idx,
                        )
                    )))
                }
                (AdditionStep::L2, _) => {
                    Some(Vec::algfn_map(advice, RepeatedAlgFn::new(
                        twisted_edwards_add_l2(),
                        layer_idx + 3,
                    )))
                }
                (AdditionStep::L3, false) => {
                    Some(Vec::algfn_map_split(
                        advice,
                        RepeatedAlgFn::new(
                            twisted_edwards_add_l3(),
                            layer_idx + 3,
                        ),
                        split_idx,
                        3,
                    ))
                }
                (AdditionStep::L3, true) => {
                    None
                }
            }
        }
    }
    
    pub mod protocol {
        use ark_ff::PrimeField;
        use crate::cleanup::proof_transcript::TProofTranscript2;
        use crate::cleanup::protocols::gkrs::bintree_add::AdditionStep;
        use crate::cleanup::protocols::gkrs::gkr::GKRLayer;
        use crate::cleanup::protocols::gkrs::split_map_gkr::SplitVecVecMapGKRAdvice;
        use crate::cleanup::protocols::splits::{SplitAt, SplitIdx};
        use crate::cleanup::protocols::sumcheck::SinglePointClaims;
        use crate::cleanup::protocols::sumchecks::dense_eq::DenseDeg2Sumcheck;
        use crate::cleanup::utils::algfn::{RepeatedAlgFn, StackedAlgFn};
        use crate::cleanup::utils::twisted_edwards_ops::algfns::{triangle_twisted_edwards_add_l1, twisted_edwards_add_l1, twisted_edwards_add_l2, twisted_edwards_add_l3};
        use crate::utils::TwistedEdwardsConfig;
        pub fn build<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2>(
            num_vars: usize,
            split_idx: SplitIdx,
        ) -> Vec<Box<dyn GKRLayer<Transcript, SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>>>> {
            let split_idx = split_idx.to_hi(num_vars);

            let mut layers = vec![];
            let num_layers = num_vars - split_idx.hi_usize(num_vars);

            for layer_idx in 0..=num_layers {
                for step in AdditionStep::all() {
                    layers.push(make_step(step, layer_idx, num_vars));
                }
                if layer_idx < num_layers {
                    layers.push(
                        Box::new(SplitAt::new(
                            split_idx,
                            3,
                        ))
                    )
                }
            }

            layers
        }

        fn make_step<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2>(addition_step: AdditionStep, layer_idx: usize, num_vars: usize) -> Box<dyn GKRLayer<Transcript, SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>>> {
            match addition_step {
                AdditionStep::L1 => {
                    Box::new(DenseDeg2Sumcheck::new(
                        StackedAlgFn::new(
                            triangle_twisted_edwards_add_l1(),
                            RepeatedAlgFn::new(
                                twisted_edwards_add_l1(),
                                layer_idx,
                            )
                        ),
                        num_vars - layer_idx
                    )) as Box<dyn GKRLayer<Transcript, _, _>>
                }
                AdditionStep::L2 => {
                    Box::new(DenseDeg2Sumcheck::new(
                        RepeatedAlgFn::new(
                            twisted_edwards_add_l2(),
                            layer_idx + 3,
                        ),
                        num_vars - layer_idx
                    ))
                }
                AdditionStep::L3 => {
                    Box::new(DenseDeg2Sumcheck::new(
                        RepeatedAlgFn::new(
                            twisted_edwards_add_l3(),
                            layer_idx + 3,
                        ),
                        num_vars - layer_idx
                    ))
                }
            }
        }
    }
}

impl<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2> Protocol2<Transcript> for TriangleAdd<F, Transcript> {
    type ProverInput = TriangleAddWG<F>;
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
mod test {
    use std::collections::HashMap;
    use ark_bls12_381::Fr;
    use ark_ec::{CurveConfig, Group};
    use ark_ec::twisted_edwards::Projective;
    use crate::cleanup::protocols::gkrs::triangle_add::{builder, TriangleAdd, TriangleAddWG};
    use crate::cleanup::protocols::splits::SplitIdx;
    use crate::cleanup::utils::algfn::{AlgFnUtils, IdAlgFn, RepeatedAlgFn};
    use crate::utils::{build_points, prettify_coords, prettify_points, DensePolyRndConfig, MapSplit, RandomlyGeneratedPoly};
    use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
    use ark_ff::Field;
    use ark_std::iterable::Iterable;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num_traits::{One, Zero};
    use crate::cleanup::proof_transcript::{ProofTranscript2, TProofTranscript2};
    use crate::cleanup::protocol2::Protocol2;
    use crate::cleanup::protocols::gkrs::split_map_gkr::SplitVecVecMapGKRAdvice;
    use crate::cleanup::protocols::sumcheck::SinglePointClaims;
    use crate::cleanup::utils::arith::evaluate_poly;

    type F = <BandersnatchConfig as CurveConfig>::BaseField;
    
    #[test]
    fn witness_gen() {
        let rng = &mut ark_std::test_rng();
        let num_vars = 6;
        let split_var = SplitIdx::HI(2);
        let generator = Projective::<BandersnatchConfig>::generator();
        let mut point_map = HashMap::new();
        let mut p = generator;
        point_map.insert(p, 1);
        point_map.insert(Projective::zero(), 0);
        
        for i in 0..(num_vars * (1 << num_vars + 1)) {
            p += generator;
            point_map.insert(p, 2 + i);
        }
        // let input_points = (0..(1 << (num_vars)) as u64).map(|i| {
        //     Projective::<BandersnatchConfig>::generator() * <BandersnatchConfig as CurveConfig>::ScalarField::from(i)
        // }).collect_vec();
        let input_points = (0..(1 << (num_vars)) as u64).map(|i| {
            Projective::<BandersnatchConfig>::rand(rng)
        }).collect_vec();
        
        let inputs = vec![
            input_points.iter().map(|p| p.x).collect_vec(),
            input_points.iter().map(|p| p.y).collect_vec(),
            input_points.iter().map(|p| p.z).collect_vec(),
        ];
        // let inputs = Vec::rand_points::<BandersnatchConfig, _>(rng, DensePolyRndConfig { num_vars: num_vars + 2 }).to_vec();

        // println!("{}", prettify_coords(&point_map, &inputs));
        let inputs = Vec::algfn_map_split(&inputs, IdAlgFn::new(3), split_var, 3);
        // println!("{}", prettify_coords(&point_map, &inputs));
        let inputs = Vec::algfn_map_split(&inputs, RepeatedAlgFn::new(IdAlgFn::new(3), 2), split_var, 3);

        let mut wg = TriangleAddWG::new(inputs, num_vars - 2, split_var);

        // println!("{}", wg.advices.iter().step_by(4).filter_map(|a| match a {
        //     SplitVecVecMapGKRAdvice::DenseMAP(d) => {
        //         Some(
        //             prettify_coords(&point_map, d)
        //         )
        //     }
        //     _ => {None}
        // }).join("\n"));
        
        let last = builder::witness::last_step(wg.advices.last().unwrap().into(), num_vars - 2 - split_var.hi_usize(num_vars));

        // println!("{}", prettify_coords(&point_map, &last));

        let point_results = build_points(&last);
        
        let mut target_sum = vec![];
        let chunk_size = (1 << (num_vars - split_var.hi_usize(num_vars)));
        for idx in 0..(1 << split_var.hi_usize(num_vars)) {
            let mut sum = Projective::zero();
            for i in 0..chunk_size {
                    sum = sum + input_points[idx * chunk_size + i] * <BandersnatchConfig as CurveConfig>::ScalarField::from((i) as u64);
            }
            target_sum.push(sum);
        }
        
        let mut resulting_sums = vec![];
        for idx in 0..(1 << (split_var.hi_usize(num_vars))) {
            let mut resulting_sum = Projective::zero();
            let mut coef = <BandersnatchConfig as CurveConfig>::ScalarField::from(1);
            for i in 1..point_results.len() {
                resulting_sum += point_results[i][idx] * coef;
                coef = coef.double();
            }
            resulting_sums.push(resulting_sum);
        }
        
        assert_eq!(resulting_sums, target_sum);


        println!("{}", prettify_coords(&point_map, &last));
        dbg!(&point_results.len());
        dbg!(&point_results.iter().map(|r| r.len()).collect_vec());
        println!("{:?} X {:?}", point_map.get(&point_results[4][0]), point_map.get(&input_points.iter().take(1 << 2).skip(1 << (2 - 1)).sum::<Projective<BandersnatchConfig>>()));
        assert_eq!(
            point_results[4][0],
            input_points.iter().take(1 << 4).skip(1 << (4 - 1)).sum::<Projective<BandersnatchConfig>>(),
        );

    }

    #[test]
    fn prove_and_verify() {
        let rng = &mut ark_std::test_rng();
        let num_vars = 8;
        let split_var = SplitIdx::HI(2);

        let inputs = Vec::rand_points::<BandersnatchConfig, _>(rng, DensePolyRndConfig { num_vars }).to_vec();
        let inputs = Vec::algfn_map_split(&inputs, IdAlgFn::new(3), split_var, 3);
        let inputs = Vec::algfn_map_split(&inputs, IdAlgFn::new(6), split_var, 3);

        let wg = TriangleAddWG::new(inputs, num_vars - 2, split_var);

        let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");

        let prover: TriangleAdd<F, ProofTranscript2> = TriangleAdd::new(num_vars - 2, split_var);

        #[cfg(debug_assertions)]
        dbg!("{}", prover.describe());

        let point = (0..split_var.hi_usize(num_vars - 2)).map(|_| Fr::rand(rng)).collect_vec();
        let dense_output = builder::witness::last_step(wg.advices.last().unwrap().into(), num_vars - 2 - split_var.hi_usize(num_vars - 2));
        
        let claims = SinglePointClaims {
            point: point.clone(),
            evs: dense_output.iter().map(|output| evaluate_poly(output, &point)).collect(),
        };
        
        let (output_claims, _) = prover.prove(&mut transcript_p, claims.clone(), wg);

        let proof = transcript_p.end();
        
        let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);

        let expected_output_claims = prover.verify(&mut transcript_v, claims.clone());

        assert_eq!(output_claims, expected_output_claims);
    }
}
