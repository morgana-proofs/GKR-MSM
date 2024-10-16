use std::io::Read;
use std::iter::{once, repeat};
use std::marker::PhantomData;
use ark_ff::PrimeField;
use itertools::Itertools;
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::{splits::SplitAt, sumchecks::vecvec::VecVecDeg2Sumcheck, gkrs::gkr::SimpleGKR};
use crate::cleanup::protocols::gkrs::split_map_gkr::SplitVecVecMapGKRAdvice;
use crate::cleanup::protocols::splits::SplitIdx;
use crate::cleanup::protocols::sumcheck::SinglePointClaims;
use crate::polynomial::vecvec::{vecvec_map, vecvec_map_split, vecvec_map_split_to_dense, VecVecPolynomial};
use crate::cleanup::utils::twisted_edwards_ops::*;
use crate::cleanup::utils::twisted_edwards_ops::algfns::*;
use crate::utils::TwistedEdwardsConfig;

#[derive(Debug)]
struct VecVecBintreeAddWG<F: PrimeField> {
    advices: Vec<SplitVecVecMapGKRAdvice<F>>,
    last: Option<Vec<Vec<F>>>
}

impl<F: PrimeField + TwistedEdwardsConfig> VecVecBintreeAddWG<F> {
    pub fn new(mut polys: Vec<VecVecPolynomial<F>>) -> Self {
        assert_eq!(polys.len(), 4);
        for i in 1..4 {
            assert_eq!(polys[i].row_logsize, polys[0].row_logsize);
            assert_eq!(polys[i].col_logsize, polys[0].col_logsize)
        }
        let num_adds = polys[0].row_logsize + 1;
        assert!(num_adds > 0);

        let mut advices = vec![];
        let mut next;
        let mut last;
        
        for add_idx in 0..num_adds {
            for stage_idx in 1..=3 {
                match stage_idx { 
                    1 => {
                        match add_idx {
                            0 => {
                                next = vecvec_map(&polys, affine_twisted_edwards_add_l1());
                                advices.push(SplitVecVecMapGKRAdvice::VecVecMAP(polys));
                                polys = next;
                            }
                            _ => {
                                next = vecvec_map(&polys, twisted_edwards_add_l1());
                                advices.push(SplitVecVecMapGKRAdvice::VecVecMAP(polys));
                                polys = next;
                            }
                        }
                    }
                    2 => {
                        match add_idx { 
                            0 => {
                                next = vecvec_map(&polys, affine_twisted_edwards_add_l2());
                                advices.push(SplitVecVecMapGKRAdvice::VecVecMAP(polys));
                                polys = next;
                            }
                            _ => {
                                next = vecvec_map(&polys, twisted_edwards_add_l2());
                                advices.push(SplitVecVecMapGKRAdvice::VecVecMAP(polys));
                                polys = next;
                            }
                        }
                    }
                    3 => {
                        match (add_idx == 0, add_idx == num_adds - 1) {
                            (true, true) => {
                                last = vecvec_map(&polys, affine_twisted_edwards_add_l3());
                                advices.push(SplitVecVecMapGKRAdvice::VecVecMAP(polys));
                                return Self {
                                    advices,
                                    last: Some(last.into_iter().map(|v| v.vec()).collect_vec()),
                                }
                            }
                            (false, true) => {
                                last = vecvec_map(&polys, twisted_edwards_add_l3());
                                advices.push(SplitVecVecMapGKRAdvice::VecVecMAP(polys));
                                return Self {
                                    advices,
                                    last: Some(last.into_iter().map(|v| v.vec()).collect_vec()),
                                }
                            }
                            (true, false) => {
                                next = vecvec_map_split(&polys, affine_twisted_edwards_add_l3(), SplitIdx::LO(0), 2);
                                advices.push(SplitVecVecMapGKRAdvice::VecVecMAP(polys));
                                advices.push(SplitVecVecMapGKRAdvice::SPLIT(()));
                                polys = next;
                            }
                            (false, false) => {
                                next = vecvec_map_split(&polys, twisted_edwards_add_l3(), SplitIdx::LO(0), 3);
                                advices.push(SplitVecVecMapGKRAdvice::VecVecMAP(polys));
                                advices.push(SplitVecVecMapGKRAdvice::SPLIT(()));
                                polys = next;
                            }
                        }
                    }
                    _ => { unreachable!() }
                }
            }
        };
        unreachable!()
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
    use ark_ec::CurveConfig;
    use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
    use ark_std::test_rng;
    use crate::cleanup::protocols::gkrs::bintree::VecVecBintreeAddWG;
    use crate::cleanup::protocols::splits::SplitIdx;
    use crate::cleanup::utils::algfn::IdAlgFn;
    use crate::polynomial::vecvec::{vecvec_map_split, VecVecPolynomial};

    #[test]
    fn witness_gen() {
        let rng = &mut test_rng();
        type F = <BandersnatchConfig as CurveConfig>::BaseField;
        let points = VecVecPolynomial::rand_points_affine::<BandersnatchConfig, _>(rng, 2, 0).to_vec();
        dbg!(&points);
        let points = vecvec_map_split(&points, IdAlgFn::new(2), SplitIdx::LO(0), 2);
        let smth = VecVecBintreeAddWG::new(points);
        dbg!(smth);
    }
}