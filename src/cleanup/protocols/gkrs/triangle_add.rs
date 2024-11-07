use std::fmt::{Display, Formatter};
use ark_ff::PrimeField;
use merlin::Transcript;
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::gkrs::bintree::AdditionStep;
use crate::cleanup::protocols::gkrs::gkr::{GKRLayer, SimpleGKR};
use crate::cleanup::protocols::gkrs::split_map_gkr::{SplitMapGKRAdvice, SplitVecVecMapGKRAdvice};
use crate::cleanup::protocols::splits::{SplitAt, SplitIdx};
use crate::cleanup::protocols::sumcheck::{DenseEqSumcheck, SinglePointClaims};
use crate::cleanup::protocols::sumchecks::dense_eq::DenseDeg2Sumcheck;
use crate::cleanup::utils::algfn::{RepeatedAlgFn, StackedAlgFn};
use crate::cleanup::utils::twisted_edwards_ops::algfns::{triangle_twisted_edwards_add_l1, twisted_edwards_add_l1, twisted_edwards_add_l2, twisted_edwards_add_l3};
use crate::utils::{MapSplit, TwistedEdwardsConfig};

#[derive(Debug)]
pub struct TriangleAddWG<F: PrimeField> {
    pub advices:  Vec<SplitMapGKRAdvice<F>>,
    pub last: Option<SplitMapGKRAdvice<F>>,
}
impl<F: PrimeField> Display for TriangleAddWG<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.advices.iter().map(|a| {
            write!(f, "{}\n", a)
        }).count();
        write!(f, "{:?}\n", self.last)
    }
}
impl<F: PrimeField + TwistedEdwardsConfig> TriangleAddWG<F> {
    pub fn new(
        mut advice: Vec<Vec<F>>,
        num_vars: usize,
        split_idx: SplitIdx,
    ) -> Self {
        let mut advices = vec![];
        let num_layers = num_vars - split_idx.hi_usize(num_vars);

        for layer_idx in 0..=num_layers {
            for step in AdditionStep::all() {
                let next = Self::step(&advice, step, layer_idx, num_layers, split_idx);
                #[cfg(debug_assertions)]
                advices.push(SplitMapGKRAdvice::DenseMAP(advice));

                advice = next;
            }
            if layer_idx < num_layers {
                advices.push(SplitMapGKRAdvice::SPLIT(()))
            }
        }

        Self {
            advices,
            last: Some(SplitMapGKRAdvice::DenseMAP(advice))
        }
    }

    fn step(advice: &[Vec<F>], addition_step: AdditionStep, layer_idx: usize, num_vars: usize, split_idx: SplitIdx) -> Vec<Vec<F>> {
        match (addition_step, num_vars == layer_idx) {
            (AdditionStep::L1, _) => {
                Vec::algfn_map(advice, StackedAlgFn::new(
                    triangle_twisted_edwards_add_l1(),
                    RepeatedAlgFn::new(
                        twisted_edwards_add_l1(),
                        layer_idx,
                    )
                ))
            }
            (AdditionStep::L2, _) => {
                Vec::algfn_map(advice, RepeatedAlgFn::new(
                    twisted_edwards_add_l2(),
                    layer_idx + 3,
                ))
            }
            (AdditionStep::L3, false) => {
                Vec::algfn_map_split(
                    advice,
                    RepeatedAlgFn::new(
                        twisted_edwards_add_l3(),
                        layer_idx + 3,
                    ),
                    split_idx,
                    3,
                )
            }
            (AdditionStep::L3, true) => {
                Vec::algfn_map(
                    advice,
                    RepeatedAlgFn::new(
                        twisted_edwards_add_l3(),
                        layer_idx + 3,
                    ),
                )
            }
        }
    }
}

impl<F: PrimeField> Iterator for TriangleAddWG<F> {
    type Item = SplitMapGKRAdvice<F>;

    fn next(&mut self) -> Option<Self::Item> {
        self.advices.pop()
    }
}


struct TriangleAdd<F: PrimeField, Transcript: TProofTranscript2> {
    gkr: SimpleGKR<SinglePointClaims<F>, SplitMapGKRAdvice<F>, Transcript, TriangleAddWG<F>>,
    split_var: SplitIdx,
}

impl<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2> TriangleAdd<F, Transcript> {
    pub fn new(
        num_vars: usize,
        split_var: SplitIdx,
    ) -> Self {

        let mut layers = vec![];
        let num_layers = num_vars - split_var.hi_usize(num_vars);

        for layer_idx in 0..=num_layers {
            for step in AdditionStep::all() {
                layers.push(Self::step(step, layer_idx, num_vars));
            }
            if layer_idx < num_layers {
                layers.push(
                    Box::new(SplitAt::new(
                        split_var,
                        3,
                    ))
                )
            }
        }

        Self {
            gkr: SimpleGKR::new(layers),
            split_var,
        }
    }

    fn step(addition_step: AdditionStep, layer_idx: usize, num_vars: usize) -> Box<dyn GKRLayer<Transcript, SinglePointClaims<F>, SplitMapGKRAdvice<F>>> {
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

    #[cfg(debug_assertions)]
    pub fn describe(&self) -> String {
        format!("Triangle Add {} ", self.gkr.description())
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
    use crate::cleanup::protocols::gkrs::triangle_add::{TriangleAdd, TriangleAddWG};
    use crate::cleanup::protocols::splits::SplitIdx;
    use crate::cleanup::utils::algfn::{AlgFnUtils, IdAlgFn};
    use crate::utils::{DensePolyRndConfig, MapSplit, RandomlyGeneratedPoly};
    use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
    use ark_ff::Field;
    use ark_std::iterable::Iterable;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num_traits::{One, Zero};
    use crate::cleanup::proof_transcript::{ProofTranscript2, TProofTranscript2};
    use crate::cleanup::protocol2::Protocol2;
    use crate::cleanup::protocols::gkrs::split_map_gkr::SplitMapGKRAdvice;
    use crate::cleanup::protocols::sumcheck::SinglePointClaims;
    use crate::cleanup::utils::arith::evaluate_poly;

    type F = <BandersnatchConfig as CurveConfig>::BaseField;

    fn prettify_points(point_map: &HashMap<Projective<BandersnatchConfig>, usize>, v: &Vec<Projective<BandersnatchConfig>>) -> String {
        v.iter().map(|p| point_map.get(p).map(|v| format!("{}", v).to_string()).unwrap_or("Unknown".to_string())).join(", ")
    }
    
    fn build_points_from_chunk(chunk: &[Vec<F>]) -> Vec<Projective<BandersnatchConfig>> {
        (0..chunk[0].len())
            .map(|i| {
                Projective::<BandersnatchConfig>::new_unchecked(
                    chunk[0][i],
                    chunk[1][i],
                    chunk[0][i] * chunk[1][i] / chunk[2][i],
                    chunk[2][i],
                )
            })
            .collect_vec()
    }
    
    fn prettify_coords_chunk(point_map: &HashMap<Projective<BandersnatchConfig>, usize>, chunk: &[Vec<F>]) -> String {
        prettify_points(
            point_map,
            &build_points_from_chunk(chunk)
        )
    }
    
    fn build_points(coords: &[Vec<F>]) -> Vec<Vec<Projective<BandersnatchConfig>>> {
        coords.chunks(3).map(|chunk| {
            build_points_from_chunk(chunk)
        }).collect_vec()
    }
    
    fn prettify_coords(point_map: &HashMap<Projective<BandersnatchConfig>, usize>, coords: &[Vec<F>]) -> String {
        coords.chunks(3).map(|chunk| {
            prettify_coords_chunk(point_map, chunk)
        }).join(" || ")
    }
    
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
        let input_points = (0..(1 << (num_vars)) as u64).map(|i| {
            Projective::<BandersnatchConfig>::generator() * <BandersnatchConfig as CurveConfig>::ScalarField::from(i)
        }).collect_vec();
        
        let inputs = vec![
            input_points.iter().map(|p| p.x).collect_vec(),
            input_points.iter().map(|p| p.y).collect_vec(),
            input_points.iter().map(|p| p.z).collect_vec(),
        ];
        // let inputs = Vec::rand_points::<BandersnatchConfig, _>(rng, DensePolyRndConfig { num_vars: num_vars + 2 }).to_vec();

        println!("{}", prettify_coords(&point_map, &inputs));
        let inputs = Vec::algfn_map_split(&inputs, IdAlgFn::new(3), split_var, 3);
        println!("{}", prettify_coords(&point_map, &inputs));
        let inputs = Vec::algfn_map_split(&inputs, IdAlgFn::new(6), split_var, 3);

        let mut wg = TriangleAddWG::new(inputs, num_vars - 2, split_var);

        println!("{}", wg.advices.iter().step_by(4).filter_map(|a| match a {
            SplitMapGKRAdvice::DenseMAP(d) => {
                Some(
                    prettify_coords(&point_map, d)
                )
            }
            SplitMapGKRAdvice::SPLIT(_) => {None}
        }).join("\n"));


        let last: Vec<Vec<F>> = wg.last.take().unwrap().into();

        println!("{}", prettify_coords(&point_map, &last));

        let point_results = build_points(&last);
        
        let mut target_sum = vec![];
        let chunk_size = (1 << (num_vars - split_var.hi_usize(num_vars)));
        for idx in 0..(1 << split_var.hi_usize(num_vars)) {
            let mut sum = Projective::zero();
            for i in 0..chunk_size {
                    sum = sum + input_points[idx * chunk_size + i] * <BandersnatchConfig as CurveConfig>::ScalarField::from((i + 1) as u64);
            }
            target_sum.push(sum);
        }
        
        let mut resulting_sums = vec![];
        for idx in 0..(1 << (split_var.hi_usize(num_vars))) {
            let mut coef = <BandersnatchConfig as CurveConfig>::ScalarField::from(2);
            let mut resulting_sum = point_results[0][idx] + point_results[1][idx] * coef;
            for i in 2..point_results.len() {
                resulting_sum += point_results[i][idx] * coef;
                coef = coef.double();
            }
            resulting_sums.push(resulting_sum);
        }
        
        assert_eq!(resulting_sums, target_sum);
    }

    #[test]
    fn prove_and_verify() {
        let rng = &mut ark_std::test_rng();
        let num_vars = 6;
        let split_var = SplitIdx::HI(2);

        let inputs = Vec::rand_points::<BandersnatchConfig, _>(rng, DensePolyRndConfig { num_vars: num_vars + 2 }).to_vec();
        let inputs = Vec::algfn_map_split(&inputs, IdAlgFn::new(3), split_var, 3);
        let inputs = Vec::algfn_map_split(&inputs, IdAlgFn::new(6), split_var, 3);

        let mut wg = TriangleAddWG::new(inputs, num_vars, split_var);

        let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");

        let prover: TriangleAdd<F, ProofTranscript2> = TriangleAdd::new(num_vars, split_var);
        
        #[cfg(debug_assertions)]
        println!("{}", prover.describe());

        let point = (0..split_var.hi_usize(num_vars)).map(|_| Fr::rand(rng)).collect_vec();
        let dense_output = match wg.last.take().unwrap() {
            SplitMapGKRAdvice::DenseMAP(m) => {m}
            SplitMapGKRAdvice::SPLIT(_) => {unreachable!()}
        };
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
