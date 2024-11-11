use std::fmt::{Display, Formatter};
use std::io::Read;
use std::iter::{once, repeat};
use std::marker::PhantomData;
use ark_ff::PrimeField;
use itertools::Itertools;
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::{splits::SplitAt, sumchecks::vecvec_eq::VecVecDeg2Sumcheck, gkrs::gkr::SimpleGKR};
use crate::cleanup::protocols::gkrs::gkr::GKRLayer;
use crate::cleanup::protocols::gkrs::split_map_gkr::SplitVecVecMapGKRAdvice;
use crate::cleanup::protocols::splits::SplitIdx;
use crate::cleanup::protocols::sumcheck::{SinglePointClaims};
use crate::cleanup::protocols::sumchecks::dense_eq::DenseDeg2Sumcheck;
use crate::polynomial::vecvec::{vecvec_map, vecvec_map_split, vecvec_map_split_to_dense, VecVecPolynomial};
use crate::cleanup::utils::twisted_edwards_ops::*;
use crate::cleanup::utils::twisted_edwards_ops::algfns::*;
use crate::utils::{MapSplit, TwistedEdwardsConfig};
use crate::cleanup::utils::algfn::{AlgFn, AlgFnSO};


#[derive(Debug)]
pub struct VecVecBintreeAddWG<F: PrimeField> {
    pub advices: Vec<SplitVecVecMapGKRAdvice<F>>,
    pub last: Option<SplitVecVecMapGKRAdvice<F>>
}

impl<F: PrimeField> Display for VecVecBintreeAddWG<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.advices.iter().map(|a| {
            write!(f, "{}\n", a)
        }).count();
        write!(f, "{:?}\n", self.last)
    }
}


#[derive(Debug, Copy, Clone)]
pub enum AdditionStep {
    L1,
    L2,
    L3,
}

impl AdditionStep {
    pub fn all() -> [AdditionStep; 3]{
        [Self::L1, Self::L2, Self::L3]
    }
}

impl<F: PrimeField + TwistedEdwardsConfig> SplitVecVecMapGKRAdvice<F> {
    fn map<Fun: AlgFn<F>>(&self, f: Fun) -> Self {
        match self {
            SplitVecVecMapGKRAdvice::VecVecMAP(vv) => {
                SplitVecVecMapGKRAdvice::VecVecMAP(vecvec_map(&vv, f))
            }
            SplitVecVecMapGKRAdvice::DenseMAP(d) => {
                SplitVecVecMapGKRAdvice::DenseMAP(Vec::algfn_map(&d, f))
            }
            SplitVecVecMapGKRAdvice::SPLIT(_) => { unreachable!() }
        }
    }

    fn map_split<Fun: AlgFn<F>>(&self, f: Fun, layer_idx: usize, row_logsize: usize, idx: SplitIdx, bundle_size: usize) -> Self {
        match self {
            SplitVecVecMapGKRAdvice::VecVecMAP(vv) => {
                match layer_idx + 2 == row_logsize {
                    true => {
                        SplitVecVecMapGKRAdvice::DenseMAP(vecvec_map_split_to_dense(&vv, f, idx, bundle_size))
                    }
                    false => {
                        SplitVecVecMapGKRAdvice::VecVecMAP(vecvec_map_split(&vv, f, idx, bundle_size))
                    }
                }
            }
            SplitVecVecMapGKRAdvice::DenseMAP(d) => {
                SplitVecVecMapGKRAdvice::DenseMAP(Vec::algfn_map_split(&d, f, idx, bundle_size))
            }
            SplitVecVecMapGKRAdvice::SPLIT(_) => { unreachable!() }
        }
    }

    fn step(&self, fwd_idx: usize, row_logsize: usize, n_adds: usize, split_last: bool, step: &AdditionStep, split_idx: SplitIdx, bundle_size: usize) -> Self {
        match (step, fwd_idx, (fwd_idx + 1 == n_adds) && !split_last) {
            (AdditionStep::L1, 0, _) => {
                self.map(affine_twisted_edwards_add_l1())
            }
            (AdditionStep::L2, 0, _) => {
                self.map(affine_twisted_edwards_add_l2())
            }
            (AdditionStep::L3, 0, true) => {
                self.map(affine_twisted_edwards_add_l3())
            }
            (AdditionStep::L3, 0, false) => {
                self.map_split(affine_twisted_edwards_add_l3(), fwd_idx, row_logsize, split_idx, bundle_size)
            }
            (AdditionStep::L1, _, _) => {
                self.map(twisted_edwards_add_l1())
            }
            (AdditionStep::L2, _, _) => {
                self.map(twisted_edwards_add_l2())
            }
            (AdditionStep::L3, _, true) => {
                self.map(twisted_edwards_add_l3())
            }
            (AdditionStep::L3, _, false) => {
                self.map_split(twisted_edwards_add_l3(), fwd_idx, row_logsize, split_idx, bundle_size)
            }
        }
    }
}

impl<F: PrimeField + TwistedEdwardsConfig> VecVecBintreeAddWG<F> {
    fn new_common(
        mut advice: SplitVecVecMapGKRAdvice<F>,
        row_logsize: usize,
        num_adds: usize,
        split_last: bool,
    ) -> Self {
        assert!(num_adds > 0);
        let mut advices = vec![];

        let mut step = AdditionStep::L1;
        let mut next;

        for add_idx in 0..num_adds {
            for step_idx in 0..3 {
                next = advice.step(add_idx, row_logsize, num_adds, split_last, &step, SplitIdx::LO(0), 3);
                advices.push(advice);
                advice = next;
                step = match step {
                    AdditionStep::L1 => {
                        AdditionStep::L2
                    }
                    AdditionStep::L2 => {
                        AdditionStep::L3
                    }
                    AdditionStep::L3 => {
                        if add_idx + 1 != num_adds || split_last {
                            advices.push(SplitVecVecMapGKRAdvice::SPLIT(()));
                        }
                        AdditionStep::L1
                    }
                };
            }
        }
        Self {
            advices,
            last: Some(advice),
        }
    }
    
    pub fn new(
        inputs: Vec<VecVecPolynomial<F>>,
        row_logsize: usize,
        num_adds: usize,
        split_last: bool,
    ) -> Self {
        Self::new_common(
            SplitVecVecMapGKRAdvice::VecVecMAP(inputs),
            row_logsize,
            num_adds,
            split_last,
        )
    }
}

impl<F: PrimeField> Iterator for VecVecBintreeAddWG<F> {
    type Item = SplitVecVecMapGKRAdvice<F>;

    fn next(&mut self) -> Option<Self::Item> {
        self.advices.pop()
    }
}

pub struct VecVecBintreeAdd<F: PrimeField, Transcript: TProofTranscript2> {
    gkr: SimpleGKR<SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>, Transcript, VecVecBintreeAddWG<F>>
}

impl<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2> VecVecBintreeAdd<F, Transcript> {
    pub fn new(num_adds: usize, num_vars: usize, row_logsize: usize, split_last: bool) -> Self {
        Self {
            gkr: SimpleGKR::new(
                Self::generate_layers(num_vars, num_adds, row_logsize, split_last),
            )
        }
    }

    pub fn generate_layers(num_vars: usize, num_adds: usize, row_logsize: usize, split_last: bool) -> Vec<Box<dyn GKRLayer<Transcript, SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>>>> {
        let mut layers: Vec<Box<dyn GKRLayer<Transcript, SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>>>> = vec![];
        let mut step = AdditionStep::L1;
        let num_vertical_vars = num_vars - row_logsize;
        for i in 0..num_adds {
            for _ in 0..3 {
                match (i, i + 1< row_logsize, &step) {
                    (0, _, AdditionStep::L1) => {
                        layers.push(Box::new(
                            VecVecDeg2Sumcheck::new(
                                affine_twisted_edwards_add_l1(),
                                num_vars - i - 1,
                                num_vertical_vars,
                            )
                        ));
                    }
                    (0, _, AdditionStep::L2) => {
                        layers.push(Box::new(
                            VecVecDeg2Sumcheck::new(
                                affine_twisted_edwards_add_l2(),
                                num_vars - i - 1,
                                num_vertical_vars,
                            )
                        ));
                    }
                    (0, _, AdditionStep::L3) => {
                        layers.push(Box::new(
                            VecVecDeg2Sumcheck::new(
                                affine_twisted_edwards_add_l3(),
                                num_vars - i - 1,
                                num_vertical_vars,
                            )
                        ));
                    }
                    (_, true, AdditionStep::L1) => {
                        layers.push(Box::new(
                            VecVecDeg2Sumcheck::new(
                                twisted_edwards_add_l1(),
                                num_vars - i - 1,
                                num_vertical_vars,
                            )
                        ));
                    }
                    (_, true, AdditionStep::L2) => {
                        layers.push(Box::new(
                            VecVecDeg2Sumcheck::new(
                                twisted_edwards_add_l2(),
                                num_vars - i - 1,
                                num_vertical_vars,
                            )
                        ));
                    }
                    (_, true, AdditionStep::L3) => {
                        layers.push(Box::new(
                            VecVecDeg2Sumcheck::new(
                                twisted_edwards_add_l3(),
                                num_vars - i - 1,
                                num_vertical_vars,
                            )
                        ));
                    }
                    (_, false, AdditionStep::L1) => {
                        layers.push(Box::new(
                            DenseDeg2Sumcheck::new(
                                twisted_edwards_add_l1(),
                                num_vars - i - 1,
                            )
                        ));
                    }
                    (_, false, AdditionStep::L2) => {
                        layers.push(Box::new(
                            DenseDeg2Sumcheck::new(
                                twisted_edwards_add_l2(),
                                num_vars - i - 1,
                            )
                        ));
                    }
                    (_, false, AdditionStep::L3) => {
                        layers.push(Box::new(
                            DenseDeg2Sumcheck::new(
                                twisted_edwards_add_l3(),
                                num_vars - i - 1,
                            )
                        ));
                    }
                }
                step = match step {
                    AdditionStep::L1 => { AdditionStep::L2}
                    AdditionStep::L2 => { AdditionStep::L3}
                    AdditionStep::L3 => { AdditionStep::L1}
                }
            }
            if i != num_adds - 1 || split_last {
                layers.push(Box::new(
                    SplitAt::new(
                        SplitIdx::LO(0),
                        3,
                    )
                ))
            }
        }
        layers
    }
    
    #[cfg(debug_assertions)]
    pub fn describe(&self) -> String {
        format!("Bintree Add {} ", self.gkr.description())
    }
}

impl<F: PrimeField + TwistedEdwardsConfig, Transcript: TProofTranscript2> Protocol2<Transcript> for VecVecBintreeAdd<F, Transcript> {
    type ProverInput = VecVecBintreeAddWG<F>;
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
    use std::error::Error;
    use ark_bls12_381::Fr;
    use ark_ec::{CurveConfig, CurveGroup};
    use ark_ec::twisted_edwards::{Affine, Projective};
    use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
    use ark_std::{test_rng, UniformRand};
    use itertools::Itertools;
    use num_traits::{One, Zero};
    use rstest::rstest;
    use crate::cleanup::proof_transcript::{ProofTranscript2, TProofTranscript2};
    use crate::cleanup::protocol2::Protocol2;
    use crate::cleanup::protocols::gkrs::bintree::{VecVecBintreeAdd, VecVecBintreeAddWG};
    use crate::cleanup::protocols::gkrs::split_map_gkr::SplitVecVecMapGKRAdvice;
    use crate::cleanup::protocols::splits::SplitIdx;
    use crate::cleanup::protocols::sumcheck::SinglePointClaims;
    use crate::cleanup::utils::algfn::IdAlgFn;
    use crate::cleanup::utils::arith::evaluate_poly;
    use crate::cleanup::utils::twisted_edwards_ops::algfns::{affine_twisted_edwards_add_l1, affine_twisted_edwards_add_l2, affine_twisted_edwards_add_l3, twisted_edwards_add_l1, twisted_edwards_add_l2, twisted_edwards_add_l3};
    use crate::polynomial::vecvec::{vecvec_map_split, VecVecPolynomial};
    use crate::utils::{DensePolyRndConfig, Densify, RandomlyGeneratedPoly};

    #[rstest]
    #[case(5, 4, 2)]
    #[case(5, 2, 4)]
    fn prove_and_verify(
        #[case] num_adds: usize,
        #[case] row_logsize: usize,
        #[case] col_logsize: usize,
        #[values(true, false)]
        split_last: bool,
    ) {
        let rng = &mut test_rng();
        type F = <BandersnatchConfig as CurveConfig>::BaseField;

        let num_vars = row_logsize + col_logsize;

        let points = VecVecPolynomial::rand_points_affine::<BandersnatchConfig, _>(rng, row_logsize, col_logsize).to_vec();
        let inputs = vecvec_map_split(&points, IdAlgFn::new(2), SplitIdx::LO(0), 2);
        let witness_gen = VecVecBintreeAddWG::new_common(SplitVecVecMapGKRAdvice::VecVecMAP(inputs), row_logsize, num_adds, split_last);

        let prover = VecVecBintreeAdd::new(
            num_adds,
            num_vars,
            row_logsize,
            split_last,
        );
        #[cfg(debug_assertions)]
        prover.gkr.layers
            .iter()
            .map(|l| { dbg!("{}", l.description()); }).interleave(
            witness_gen.advices
                .iter()
                .map(|a| { dbg!("{}", a); })
            )   
            .count();

        let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");
        let last = witness_gen.last.as_ref().unwrap();
        let dense_output = match last {
            SplitVecVecMapGKRAdvice::VecVecMAP(vv) => { vv.to_dense( ())}
            SplitVecVecMapGKRAdvice::DenseMAP(d) => { d.iter().map(|c| c.to_dense(num_vars - num_adds - match split_last {true => 1, false => 0})).collect_vec() }
            SplitVecVecMapGKRAdvice::SPLIT(_) => { unreachable!() }
        };

        let point = (0..(num_vars - 1 - num_adds + match split_last {true => 0, false => 1})).map(|_| Fr::rand(rng)).collect_vec();
        dbg!("{}, {:?}", dense_output.len(), dense_output.iter().map(|x| x.len()).collect_vec());
        dbg!("{}", point.len());
        let claims = SinglePointClaims {
            point: point.clone(),
            evs: dense_output.iter().map(|output| evaluate_poly(output, &point)).collect(),
        };
        let (output_claims, _) = prover.prove(&mut transcript_p, claims.clone(), witness_gen);

        let proof = transcript_p.end();

        let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);

        let expected_output_claims = prover.verify(&mut transcript_v, claims.clone());

        assert_eq!(output_claims, expected_output_claims);
    }

    #[test]
    fn witness_gen() {
        let rng = &mut test_rng();
        type F = <BandersnatchConfig as CurveConfig>::BaseField;

        let row_logsize = 4;
        let col_logsize = 2;
        let num_adds = 5;
        let split_last = false;
        let points = VecVecPolynomial::rand_points_affine::<BandersnatchConfig, _>(rng, row_logsize, col_logsize).to_vec();
        let inputs = vecvec_map_split(&points, IdAlgFn::new(2), SplitIdx::LO(0), 2);
        let smth = VecVecBintreeAddWG::new_common(SplitVecVecMapGKRAdvice::VecVecMAP(inputs.clone()), row_logsize, num_adds, split_last);
        let outs = smth.last.unwrap();
        let densified_out = match outs {
            SplitVecVecMapGKRAdvice::VecVecMAP(vv) => {
                vv.to_dense(())
            }
            SplitVecVecMapGKRAdvice::DenseMAP(d) => {
                d.iter().map(|v| v.to_dense(row_logsize + col_logsize - num_adds)).collect_vec()
            }
            SplitVecVecMapGKRAdvice::SPLIT(_) => {unreachable!()}
        };
        let densified_points = points.iter().map(|p| p.vec()).collect_vec();

        let group_size = 1 << num_adds;
        for idx in 0..densified_out[0].len() {
            let mut acc = Projective::zero();
            for count in 0..group_size {
                acc += Affine::<BandersnatchConfig>::new(
                    densified_points[0][idx * group_size + count],
                    densified_points[1][idx * group_size + count],
                );
            }
            if !densified_out[2][idx].is_zero() {
                let out = Projective::<BandersnatchConfig>::new_unchecked(
                    densified_out[0][idx],
                    densified_out[1][idx],
                    densified_out[0][idx] * densified_out[1][idx] / densified_out[2][idx],
                    densified_out[2][idx],
                );
                assert!(out.into_affine().is_on_curve())
            }
        }
    }


    #[rstest]
    fn check_affine_point_addition(
        #[values(0, 4)]
        col_logsize: usize,
        #[values(2, 3, 5)]
        row_logsize: usize,
    ) {

        let out_n_vars = col_logsize + row_logsize;
        type F = <BandersnatchConfig as CurveConfig>::BaseField;
        let rng = &mut test_rng();

        let point_coords = VecVecPolynomial::rand_points_affine::<BandersnatchConfig, _>(rng, row_logsize, col_logsize).to_vec();
        let inputs = vecvec_map_split(&point_coords, IdAlgFn::new(2), SplitIdx::LO(0), 2);

        let inputs = SplitVecVecMapGKRAdvice::VecVecMAP(inputs);

        let dense_point_coords = point_coords.to_dense(());

        let dense_points = (0..(1 << (col_logsize + row_logsize)))
            .filter_map(|idx| {
                let p = Affine::<BandersnatchConfig>::new_unchecked(dense_point_coords[0][idx], dense_point_coords[1][idx]);
                match p.is_on_curve() {
                    true => {Some(p)}
                    false => {
                        assert!(dense_point_coords[0][idx].is_zero());
                        assert!(dense_point_coords[1][idx].is_zero());
                        None
                    }
                }
            })
            .collect_vec();
        let output_points = dense_points.chunks(2).map(|c| c[0] + c[1]).collect_vec();


        let l1 = inputs.map(affine_twisted_edwards_add_l1());
        let l2 = l1.map(affine_twisted_edwards_add_l2());
        let l3 = l2.map_split(affine_twisted_edwards_add_l3(),0, row_logsize, SplitIdx::LO(0), 3);

        dbg!(&l3);
        let dense_ans = match l3 {
            SplitVecVecMapGKRAdvice::VecVecMAP(vv) => {vv.to_dense(())}
            SplitVecVecMapGKRAdvice::DenseMAP(d) => {d.iter().map(|p| p.to_dense(out_n_vars)).collect_vec()}
            SplitVecVecMapGKRAdvice::SPLIT(_) => {unreachable!()}
        };

        for idx in 0..output_points.len() {
            let point = Projective::<BandersnatchConfig>::new_unchecked(
                dense_ans[3 * (idx % 2) + 0][idx / 2],
                dense_ans[3 * (idx % 2) + 1][idx / 2],
                dense_ans[3 * (idx % 2) + 0][idx / 2] * dense_ans[3 * (idx % 2) + 1][idx / 2] / dense_ans[3 * (idx % 2) + 2][idx / 2],
                dense_ans[3 * (idx % 2) + 2][idx / 2],
            );
            assert!(point.into_affine().is_on_curve());
            assert_eq!(point, output_points[idx]);
        }
    }

    #[rstest]
    fn check_projective_point_addition(
        #[values(0, 4)]
        col_logsize: usize,
        #[values(2, 3, 5)]
        row_logsize: usize,
    ) {

        let out_n_vars = col_logsize + row_logsize;
        type F = <BandersnatchConfig as CurveConfig>::BaseField;
        let rng = &mut test_rng();

        let point_coords = VecVecPolynomial::rand_points::<BandersnatchConfig, _>(rng, row_logsize, col_logsize).to_vec();
        let inputs = vecvec_map_split(&point_coords, IdAlgFn::new(3), SplitIdx::LO(0), 3);

        let inputs = SplitVecVecMapGKRAdvice::VecVecMAP(inputs);

        let dense_point_coords = point_coords.to_dense(());

        let dense_points = (0..(1 << (col_logsize + row_logsize)))
            .filter_map(|idx| {
                match dense_point_coords[2][idx].is_zero() {
                    true => {
                        assert!(dense_point_coords[0][idx].is_zero());
                        assert!(dense_point_coords[1][idx].is_zero());
                        assert!(dense_point_coords[2][idx].is_zero());
                        None
                    }
                    false => {
                        let p = Projective::<BandersnatchConfig>::new_unchecked(
                            dense_point_coords[0][idx],
                            dense_point_coords[1][idx],
                            dense_point_coords[0][idx] * dense_point_coords[1][idx] / dense_point_coords[2][idx],
                            dense_point_coords[2][idx],
                        );
                        match p.into_affine().is_on_curve()
                            {
                                true => { Some(p) }
                                false => {
                                assert!(dense_point_coords[0][idx].is_zero());
                                assert!(dense_point_coords[1][idx].is_zero());
                                assert!(dense_point_coords[2][idx].is_zero());
                                None
                            }
                        }
                    }
                }
            })
            // .map(|p| p.into_affine())
            .collect_vec();
        let output_points = dense_points.chunks(2).map(|c| (c[0] + c[1]).into_affine()).collect_vec();


        let l1 = inputs.map(twisted_edwards_add_l1());
        let l2 = l1.map(twisted_edwards_add_l2());
        let l3 = l2.map_split(twisted_edwards_add_l3(),1, row_logsize + 1, SplitIdx::LO(0), 3);

        let dense_ans = match l3 {
            SplitVecVecMapGKRAdvice::VecVecMAP(vv) => {vv.to_dense(())}
            SplitVecVecMapGKRAdvice::DenseMAP(d) => {d.iter().map(|p| p.to_dense(out_n_vars)).collect_vec()}
            SplitVecVecMapGKRAdvice::SPLIT(_) => {unreachable!()}
        };

        for idx in 0..output_points.len() {
            let point = Projective::<BandersnatchConfig>::new_unchecked(
                dense_ans[3 * (idx % 2) + 0][idx / 2],
                dense_ans[3 * (idx % 2) + 1][idx / 2],
                dense_ans[3 * (idx % 2) + 0][idx / 2] * dense_ans[3 * (idx % 2) + 1][idx / 2],
                dense_ans[3 * (idx % 2) + 2][idx / 2],
            ).into_affine();
            assert!(point.is_on_curve());
            assert_eq!(point, output_points[idx]);
        }
    }
}