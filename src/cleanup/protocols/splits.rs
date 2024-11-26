use std::marker::PhantomData;
use ark_ff::PrimeField;
use itertools::Itertools;
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::gkrs::gkr::GKRLayer;
use crate::cleanup::protocols::sumcheck::{SinglePointClaims};
use crate::cleanup::utils::algfn::{AlgFn, AlgFnSO};

use crate::cleanup::polys::vecvec::VecVecPolynomial;
use crate::protocol::protocol::EvalClaim;
use crate::cleanup::protocols::sumchecks::vecvec_eq::VecVecDeg2Sumcheck;
use crate::utils::fix_var_top;


#[derive(Debug, Copy, Clone)]
pub enum SplitIdx {
    LO(usize),
    HI(usize),
}

impl SplitIdx {
    // LO: 7 6 5 4 3 2 1 0
    //     _ _ _ _ _ _ _ _
    // HI: 0 1 2 3 4 5 6 7
    // num_vars = 8

    pub fn to_hi(&self, num_vars: usize) -> Self {
        SplitIdx::HI(match self {
            SplitIdx::LO(lo) => {num_vars - lo - 1}
            SplitIdx::HI(hi) => {*hi}
        })
    }

    pub fn to_lo(&self, num_vars: usize) -> Self {
        SplitIdx::LO(match self {
            SplitIdx::HI(hi) => {num_vars - hi - 1}
            SplitIdx::LO(lo) => {*lo }
        })
    }
    
    pub fn hi_usize(&self, num_vars: usize) -> usize {
        match self.to_hi(num_vars) {
            SplitIdx::HI(hi) => hi,
            _ => unreachable!(),
        }
    }
    pub fn lo_usize(&self, num_vars: usize) -> usize {
        match self.to_lo(num_vars) {
            SplitIdx::LO(lo) => lo,
            _ => unreachable!(),
        }
    }
}

pub struct SplitAt<F: PrimeField> {
    pub bundle_size: usize,
    pub var_idx: SplitIdx,
    _pd: PhantomData<F>,
}
pub struct SplitAtParams<F> {
    bundle_size: usize,
    var_idx: SplitIdx,
    _pd: PhantomData<F>
}

impl<F: PrimeField> SplitAtParams<F> {
    pub fn set_bundle_size(mut self, bundle_size: usize) -> Self {
        self.bundle_size = bundle_size;
        self
    }
    pub fn set_lo_indexing(mut self) -> Self {
        self.var_idx = SplitIdx::LO(match self.var_idx {
            SplitIdx::HI(x) => {x}
            SplitIdx::LO(x) => {x}
        });
        self
    }

    pub fn set_hi_indexing(mut self) -> Self {
        self.var_idx = SplitIdx::HI(match self.var_idx {
            SplitIdx::HI(x) => {x}
            SplitIdx::LO(x) => {x}
        });
        self
    }

    pub fn set_var_idx(mut self, var_idx: usize) -> Self {
        self.var_idx = match self.var_idx {
            SplitIdx::LO(_) => {SplitIdx::LO(var_idx)}
            SplitIdx::HI(_) => {SplitIdx::HI(var_idx)}
        };
        self
    }
    pub fn end(self) -> SplitAt<F> {
        SplitAt::from_params(self)
    }
}

impl<F: PrimeField> SplitAt<F> {
    pub fn new(var_idx: SplitIdx, bundle_size: usize) -> Self {
        Self {
            bundle_size,
            var_idx,
            _pd: Default::default(),
        }
    }

    pub fn from_params(params: SplitAtParams<F>) -> Self {
        Self {
            bundle_size: params.bundle_size,
            var_idx: params.var_idx,
            _pd: Default::default(),
        }
    }
    pub fn builder() -> SplitAtParams<F> {
        SplitAtParams {
            bundle_size: 1,
            var_idx: SplitIdx::LO(0),
            _pd: PhantomData,
        }
    }
}

impl<Transcript: TProofTranscript2, F: PrimeField> Protocol2<Transcript> for SplitAt<F> {
    type ProverInput = ();
    type ProverOutput = ();
    type ClaimsBefore = SinglePointClaims<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, _: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let r = transcript.challenge_sumcheck();
        let SinglePointClaims { mut point, evs } = claims;

        let (iter_l, iter_r) = evs.chunks(self.bundle_size).tee();
        let evs_l = iter_l.step_by(2).flatten();
        let evs_r = iter_r.skip(1).step_by(2).flatten();

        let evs_new = evs_l.zip(evs_r).map(|(x, y)| *x + r * (*y - x)).collect();

        point.insert(match self.var_idx {
            SplitIdx::LO(x) => {point.len() - x}
            SplitIdx::HI(x) => {x}
        }, r);

        (SinglePointClaims{ point, evs: evs_new }, ())
    }

    fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        self.prove(transcript, claims, ()).0
    }
}


impl<Transcript: TProofTranscript2, F: PrimeField> GKRLayer<Transcript, SinglePointClaims<F>, ()> for SplitAt<F> {
    fn prove_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>, advice: ()) -> SinglePointClaims<F> {
        Protocol2::prove(self, transcript, claims.into(), advice.into()).0
    }

    fn verify_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>) -> SinglePointClaims<F> {
        Protocol2::verify(self, transcript, claims.into())
    }
}

pub struct GlueSplit<F: PrimeField> {
    _pd: PhantomData<F>,
}

impl<Transcript: TProofTranscript2, F: PrimeField> Protocol2<Transcript> for GlueSplit<F> {
    type ProverInput = ();
    type ProverOutput = ();
    type ClaimsBefore = SinglePointClaims<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let r = transcript.challenge_sumcheck();
        let SinglePointClaims { mut point, evs } = claims;

        let evs_new = vec![
            evs[0] + r * (evs[2] - evs[0]),
            evs[1] + r * (evs[3] - evs[1]),
            evs[4] + r * (evs[5] - evs[4]),
        ];

        point.push(r);
        (SinglePointClaims{ point, evs: evs_new }, ())
    }

    fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        self.prove(transcript, claims, ()).0
    }
}

#[cfg(test)]
mod test {
    use ark_ed_on_bls12_381_bandersnatch::Fr;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use rstest::rstest;
    use crate::cleanup::proof_transcript::{ProofTranscript2, TProofTranscript2};
    use crate::cleanup::protocol2::Protocol2;
    use crate::cleanup::protocols::splits::{SplitAt, SplitIdx};
    use crate::cleanup::protocols::sumcheck::SinglePointClaims;
    use crate::cleanup::polys::common::EvaluateAtPoint;

    #[rstest]
    #[case(5, 3, 1, SplitIdx::HI(4))]
    #[case(5, 3, 1, SplitIdx::LO(4))]
    #[case(5, 3, 3, SplitIdx::HI(4))]
    #[case(5, 3, 3, SplitIdx::LO(4))]
    #[case(5, 3, 3, SplitIdx::HI(3))]
    #[case(5, 3, 3, SplitIdx::LO(3))]
    fn vecvec_split(
        #[case]
        num_vars: usize,
        #[case]
        num_bundles: usize,
        #[case]
        bundle_size: usize,
        #[case]
        var_idx: SplitIdx,
    ) {
        let rng = &mut ark_std::test_rng();


        let data: Vec<Vec<Vec<Vec<Fr>>>> = (0..num_bundles).map(|_| (0..2).map(|_| (0..bundle_size).map(|_| (0..(1 << num_vars - 1)).map(|_| Fr::rand(rng)).collect_vec()).collect_vec()).collect_vec()).collect_vec();
        let splitted_polys = data
            .iter()
            .map(|s|
                s
                    .iter()
                    .map(|b|
                        b
                            .iter()
                            .map(|p|
                                p
                                    .iter()
                                    .map(|v|
                                        *v
                                    )
                                    .collect_vec()
                            )
                    )
                    .flatten().collect_vec()
            )
            .flatten()
            .collect_vec();

        let sector_size = 1 << (match var_idx {
            SplitIdx::LO(var_idx) => {var_idx}
            SplitIdx::HI(var_idx) => {num_vars - 1 - var_idx}
        });
        let concatenated_polys = data
            .iter()
            .map(|s| {
                let (first, other) = s.split_first().unwrap();
                let (second, ..) = other.split_first().unwrap();
                first.iter().zip_eq(second.iter())
                    .map(|(l, r)| {
                        l.chunks(sector_size).interleave(r.chunks(sector_size)).flatten().cloned().collect_vec()
                    })
            })
            .flatten()
            .collect_vec();

        let point = (0..(num_vars - 1)).map(|_| Fr::rand(rng)).collect_vec();

        let split_evals = splitted_polys.iter().map(|p| p.evaluate(&point)).collect();
        let split_claims = SinglePointClaims { point, evs: split_evals };

        let proto = SplitAt::new(var_idx, bundle_size);

        let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");
        let (concat_claim, _) = proto.prove(&mut transcript_p, split_claims.clone(), ());

        let concat_evals: Vec<Fr> = concatenated_polys.iter().map(|p| p.evaluate(&concat_claim.point)).collect();
        assert_eq!(&concat_evals, &concat_claim.evs);
        let proof = transcript_p.end();

        let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);
        proto.verify(&mut transcript_v, split_claims);

    }
}