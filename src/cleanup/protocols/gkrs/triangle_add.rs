use std::fmt::{Display, Formatter};
use ark_ff::PrimeField;
use merlin::Transcript;
use crate::cleanup::proof_transcript::TProofTranscript2;
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
    ) -> Self {
        let mut advices = vec![];

        for layer_idx in 0..=num_vars {
            for step in AdditionStep::all() {
                let next = Self::step(&advice, step, layer_idx, num_vars);
                #[cfg(debug_assertions)]
                advices.push(SplitMapGKRAdvice::DenseMAP(advice));

                advice = next;
            }
            if layer_idx < num_vars {
                advices.push(SplitMapGKRAdvice::SPLIT(()))
            }
        }

        Self {
            advices,
            last: Some(SplitMapGKRAdvice::DenseMAP(advice))
        }
    }

    fn step(advice: &[Vec<F>], addition_step: AdditionStep, layer_idx: usize, num_vars: usize) -> Vec<Vec<F>> {
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
                    SplitIdx::HI(0),
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
    gkr: SimpleGKR<SinglePointClaims<F>, SplitMapGKRAdvice<F>, Transcript, TriangleAddWG<F>>
}

impl<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2> TriangleAdd<F, Transcript> {
    pub fn new(
        num_vars: usize,
    ) -> Self {

        let mut layers = vec![];

        for layer_idx in 0..=num_vars {
            for step in AdditionStep::all() {
                layers.push(Self::step(step, layer_idx, num_vars));
            }
            if layer_idx < num_vars {
                layers.push(
                    Box::new(SplitAt::new(
                        SplitIdx::HI(0),
                        3,
                    ))
                )
            }
        }

        Self {
            gkr: SimpleGKR::new(layers),
        }
    }

    fn step(addition_step: AdditionStep, layer_idx: usize, num_vars: usize) -> Box<dyn GKRLayer<Transcript, SinglePointClaims<F>, SplitMapGKRAdvice<F>>> {
        match addition_step {
            AdditionStep::L1 => {
                Box::new(DenseDeg2Sumcheck::new(
                    RepeatedAlgFn::new(
                        twisted_edwards_add_l1(),
                        layer_idx,
                    ),
                    num_vars
                )) as Box<dyn GKRLayer<Transcript, _, _>>
            }
            AdditionStep::L2 => {
                Box::new(DenseDeg2Sumcheck::new(
                    RepeatedAlgFn::new(
                        twisted_edwards_add_l2(),
                        layer_idx + 3,
                    ),
                    num_vars
                ))
            }
            AdditionStep::L3 => {
                Box::new(DenseDeg2Sumcheck::new(
                    RepeatedAlgFn::new(
                        twisted_edwards_add_l3(),
                        layer_idx + 3,
                    ),
                    num_vars
                ))
            }
        }
    }

    #[cfg(debug_assertions)]
    pub fn describe(&self) -> String {
        format!("Triangle Add {} ", self.gkr.description())
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
    use ark_std::iterable::Iterable;
    use itertools::Itertools;
    use num_traits::{One, Zero};
    use crate::cleanup::proof_transcript::{ProofTranscript2, TProofTranscript2};
    use crate::cleanup::protocols::gkrs::split_map_gkr::SplitMapGKRAdvice;

    type F = <BandersnatchConfig as CurveConfig>::BaseField;

    fn prettify_points(point_map: &HashMap<Projective<BandersnatchConfig>, usize>, v: &Vec<Projective<BandersnatchConfig>>) -> String {
        v.iter().map(|p| point_map.get(p).map(|v| format!("{}", v).to_string()).unwrap_or("Unknown".to_string())).join(", ")
    }
    
    fn prettify_coords_chunk(point_map: &HashMap<Projective<BandersnatchConfig>, usize>, chunk: &[Vec<F>]) -> String {
        prettify_points(
            point_map,
            &(0..chunk[0].len())
                .map(|i| {
                    Projective::<BandersnatchConfig>::new_unchecked(
                        chunk[0][i],
                        chunk[1][i],
                        chunk[0][i] * chunk[1][i] / chunk[2][i],
                        chunk[2][i],
                    )
                })
                .collect_vec()
        )
    }
    
    fn prettify_coords(point_map: &HashMap<Projective<BandersnatchConfig>, usize>, coords: &[Vec<F>]) -> String {
        coords.chunks(3).map(|chunk| {
            prettify_coords_chunk(point_map, chunk)
        }).join(" || ")
    }
    
    #[test]
    fn witness_gen() {
        let rng = &mut ark_std::test_rng();
        let num_vars = 4;
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
        let inputs = Vec::algfn_map_split(&inputs, IdAlgFn::new(3), SplitIdx::HI(0), 3);
        println!("{}", prettify_coords(&point_map, &inputs));
        let inputs = Vec::algfn_map_split(&inputs, IdAlgFn::new(6), SplitIdx::HI(0), 3);

        let mut wg = TriangleAddWG::new(inputs, num_vars - 2);

        println!("{}", wg.advices.iter().step_by(4).filter_map(|a| match a {
            SplitMapGKRAdvice::DenseMAP(d) => {
                Some(
                    prettify_coords(&point_map, d)
                )
            }
            SplitMapGKRAdvice::SPLIT(_) => {None}
        }).join("\n"));


        let last: Vec<Vec<F>> = wg.last.take().unwrap().into();

        let point_results = last.chunks(3).map(|chunk| {
            Projective::<BandersnatchConfig>::new(
                chunk[0][0],
                chunk[1][0],
                chunk[0][0] * chunk[1][0] / chunk[2][0],
                chunk[2][0],
            )
        }).collect_vec();
        
        println!("{}", prettify_points(&point_map, &point_results));
        
        let t_sum = input_points.iter().enumerate().map(|(i, p)| {
            *p * <BandersnatchConfig as CurveConfig>::ScalarField::from((i + 1) as u64)
        }).sum::<Projective<BandersnatchConfig>>();
        
        
    }

    #[test]
    fn prove_and_verify() {
        let rng = &mut ark_std::test_rng();
        let num_vars = 4;
        let inputs = Vec::rand_points::<BandersnatchConfig, _>(rng, DensePolyRndConfig { num_vars: num_vars + 2 }).to_vec();
        let inputs = Vec::algfn_map_split(&inputs, IdAlgFn::new(3), SplitIdx::LO(0), 3);
        let inputs = Vec::algfn_map_split(&inputs, IdAlgFn::new(6), SplitIdx::LO(0), 3);

        let mut wg = TriangleAddWG::new(inputs, num_vars);

        let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");

        let prover: TriangleAdd<F, ProofTranscript2> = TriangleAdd::new(num_vars);
        #[cfg(debug_assertions)]
        println!("{}", prover.describe());
    }
}


//                             even odd 
//                              |   /
//                              /  / 
//                             /  /
// 1 1 1 1 1 1 1 1|1 1 1 1|1 1|1|1
// 1 1 1 1 1 1 1 1|1 1 1 1|1_1|1
// 1 1 1 1 1 1 1 1|1 1 1 1|1|1
// 1 1 1 1 1 1 1 1|1_1_1_1|1
// 1 1 1 1 1 1 1 1|1 1|1|1
// 1 1 1 1 1 1 1 1|1_1|1
// 1 1 1 1 1 1 1 1|1|1
// 1_1_1_1_1_1_1_1|1
// 1 1 1 1|1 1|1|1
// 1 1 1 1|1_1|1
// 1 1 1 1|1|1
// 1_1_1_1|1
// 1 1|1|1
// 1_1|1
// 1|1
// 1