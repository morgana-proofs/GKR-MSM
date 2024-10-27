use std::fmt::{Display, Formatter};
use std::io::Read;
use std::iter::{once, repeat};
use std::marker::PhantomData;
use ark_ff::PrimeField;
use itertools::Itertools;
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::{splits::SplitAt, sumchecks::vecvec_eq::VecVecDeg2Sumcheck, gkrs::gkr::SimpleGKR};
use crate::cleanup::protocols::gkrs::split_map_gkr::SplitVecVecMapGKRAdvice;
use crate::cleanup::protocols::splits::SplitIdx;
use crate::cleanup::protocols::sumcheck::{AlgFn, SinglePointClaims};
use crate::polynomial::vecvec::{vecvec_map, vecvec_map_split, vecvec_map_split_to_dense, VecVecPolynomial};
use crate::cleanup::utils::twisted_edwards_ops::*;
use crate::cleanup::utils::twisted_edwards_ops::algfns::*;
use crate::utils::{MapSplit, TwistedEdwardsConfig};

#[derive(Debug)]
struct VecVecBintreeAddWG<F: PrimeField> {
    advices: Vec<SplitVecVecMapGKRAdvice<F>>,
    last: Option<SplitVecVecMapGKRAdvice<F>>
}

impl<F: PrimeField> Display for VecVecBintreeAddWG<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.advices.iter().map(|a| {
            write!(f, "{}\n", a)
        }).count();
        write!(f, "{:?}\n", self.last)
    }
}


#[derive(Debug)]
enum Step {
    L1,
    L2,
    L3,
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

    fn step(&self, fwd_idx: usize, row_logsize: usize, split_last: bool, step: &Step, split_idx: SplitIdx, bundle_size: usize) -> Self {
        // println!("Layer {} of {}, Step {:?}", fwd_idx, n_iters, step);
        // println!("Split params: split_last: {}, split_idx: {:?}, bundle_size: {}", split_last, split_idx, bundle_size);
        // dbg!(&self);

        match (step, fwd_idx, (fwd_idx + 1 == row_logsize) && !split_last) {
            (Step::L1, 0, _) => {
                self.map(affine_twisted_edwards_add_l1())
            }
            (Step::L2, 0, _) => {
                self.map(affine_twisted_edwards_add_l2())
            }
            (Step::L3, 0, true) => {
                self.map(affine_twisted_edwards_add_l3())
            }
            (Step::L3, 0, false) => {
                self.map_split(affine_twisted_edwards_add_l3(), fwd_idx, row_logsize, split_idx, bundle_size)
            }
            (Step::L1, _, _) => {
                self.map(twisted_edwards_add_l1())
            }
            (Step::L2, _, _) => {
                self.map(twisted_edwards_add_l2())
            }
            (Step::L3, _, true) => {
                self.map(twisted_edwards_add_l3())
            }
            (Step::L3, _, false) => {
                self.map_split(twisted_edwards_add_l3(), fwd_idx, row_logsize, split_idx, bundle_size)
            }
        }
    }
}


impl<F: PrimeField + TwistedEdwardsConfig> VecVecBintreeAddWG<F> {
    pub fn new(
        mut advice: SplitVecVecMapGKRAdvice<F>,
        row_logsize: usize,
        num_adds: usize,
        split_last: bool,
    ) -> Self {
        assert!(num_adds > 0);
        let mut advices = vec![];

        let mut step = Step::L1;
        let mut next;

        for add_idx in 0..num_adds {
            for step_idx in 0..3 {
                next = advice.step(add_idx, row_logsize, split_last, &step, SplitIdx::LO(0), 3);
                advices.push(advice);
                advice = next;
                step = match step {
                    Step::L1 => {
                        Step::L2
                    }
                    Step::L2 => {
                        Step::L3
                    }
                    Step::L3 => {
                        if add_idx + 1 != num_adds || split_last {
                            advices.push(SplitVecVecMapGKRAdvice::SPLIT(()));
                        }
                        Step::L1
                    }
                };
            }
        }
        Self {
            advices,
            last: Some(advice),
        }
    }
}

impl<F: PrimeField> Iterator for VecVecBintreeAddWG<F> {
    type Item = SplitVecVecMapGKRAdvice<F>;

    fn next(&mut self) -> Option<Self::Item> {
        self.advices.pop()
    }
}

struct VecVecBintreeAdd<F: PrimeField, Transcript: TProofTranscript2> {
    gkr: SimpleGKR<SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>, Transcript, VecVecBintreeAddWG<F>>
}

impl<F: PrimeField, Transcript: TProofTranscript2> Protocol2<Transcript> for VecVecBintreeAdd<F, Transcript> {
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
    use ark_bls12_381::Fr;
    use ark_ec::{CurveConfig, CurveGroup};
    use ark_ec::twisted_edwards::{Affine, Projective};
    use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
    use ark_std::{test_rng, UniformRand};
    use itertools::Itertools;
    use num_traits::{One, Zero};
    use rstest::rstest;
    use crate::cleanup::protocols::gkrs::bintree::VecVecBintreeAddWG;
    use crate::cleanup::protocols::gkrs::split_map_gkr::SplitVecVecMapGKRAdvice;
    use crate::cleanup::protocols::splits::SplitIdx;
    use crate::cleanup::utils::algfn::IdAlgFn;
    use crate::cleanup::utils::twisted_edwards_ops::algfns::{affine_twisted_edwards_add_l1, affine_twisted_edwards_add_l2, affine_twisted_edwards_add_l3, twisted_edwards_add_l1, twisted_edwards_add_l2, twisted_edwards_add_l3};
    use crate::polynomial::vecvec::{vecvec_map_split, VecVecPolynomial};
    use crate::utils::{DensePolyRndConfig, Densify, RandomlyGeneratedPoly};

    #[test]
    fn witness_gen() {
        let rng = &mut test_rng();
        type F = <BandersnatchConfig as CurveConfig>::BaseField;
        
        let row_logsize = 4;
        let col_logsize = 2;
        let num_adds = 2;
        let split_last = false;
        let points = VecVecPolynomial::rand_points_affine::<BandersnatchConfig, _>(rng, row_logsize, col_logsize).to_vec();
        let inputs = vecvec_map_split(&points, IdAlgFn::new(2), SplitIdx::LO(0), 2);
        let smth = VecVecBintreeAddWG::new(SplitVecVecMapGKRAdvice::VecVecMAP(inputs), row_logsize, num_adds, split_last);
        dbg!(&smth);
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
            // if !densified_out[2][idx].is_zero() {
            //     let out = Projective::<BandersnatchConfig>::new_unchecked(
            //         densified_out[0][idx],
            //         densified_out[1][idx],
            //         densified_out[0][idx] * densified_out[1][idx],
            //         densified_out[2][idx],
            //     );
            //     dbg!(&out);
            //     assert!(out.into_affine().is_on_curve())
            // }
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
                dense_ans[3 * (idx % 2) + 0][idx / 2] * dense_ans[3 * (idx % 2) + 1][idx / 2],
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
                let p = Projective::<BandersnatchConfig>::new_unchecked(
                    dense_point_coords[0][idx],
                    dense_point_coords[1][idx],
                    dense_point_coords[0][idx] * dense_point_coords[1][idx],
                    dense_point_coords[2][idx],
                );
                match p.z.is_zero() {
                    true => {
                        assert!(dense_point_coords[0][idx].is_zero());
                        assert!(dense_point_coords[1][idx].is_zero());
                        assert!(dense_point_coords[2][idx].is_zero());
                        None
                    }
                    false => {
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