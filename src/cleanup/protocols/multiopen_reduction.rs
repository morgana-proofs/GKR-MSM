use std::marker::PhantomData;
use std::ops::Index;
use ark_ff::PrimeField;
use itertools::{repeat_n, Itertools};
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::sumcheck::{gamma_rlc, DenseSumcheckObject, DenseSumcheckObjectSO, FoldToSumcheckable, GenericSumcheckProtocol, PointClaim, SinglePointClaims};
use crate::cleanup::protocols::verifier_polys::{EqPoly, VerifierPoly};
use crate::cleanup::utils::algfn::AlgFnSO;
use crate::utils::{eq_poly_sequence_last, make_gamma_pows};

#[derive(Clone)]
struct FoldedProdAlgFn<F: PrimeField> {
    gammas: Vec<F>,
    nargs: usize,
}

impl<F: PrimeField> FoldedProdAlgFn<F> {
    pub fn new(gamma: F, nargs: usize) -> Self {
        Self {
            gammas: make_gamma_pows(gamma, nargs),
            nargs,
        }
    }
}

impl <F: PrimeField> AlgFnSO<F> for FoldedProdAlgFn<F> {
    fn exec(&self, args: &impl Index<usize, Output=F>) -> F {
        (0..self.nargs).map(|i| {
            args[i] * args[i + self.nargs] * self.gammas[i]
        }).sum::<F>()
    }

    fn deg(&self) -> usize {
        2
    }

    fn n_ins(&self) -> usize {
        self.nargs * 2
    }
}

pub struct MultiOpenReduction<F: PrimeField> {
    pub nvars: usize,
    pub nargs: usize,
    _pd: PhantomData<F>
}

impl<F: PrimeField> MultiOpenReduction<F> {
    pub fn new(nvars: usize, nargs: usize) -> Self {
        Self {
            nvars,
            nargs,
            _pd: Default::default(),
        }
    }
}

impl<Transcript: TProofTranscript2, F: PrimeField> Protocol2<Transcript> for MultiOpenReduction<F> {
    type ProverInput = Vec<Vec<F>>;
    type ProverOutput = ();
    type ClaimsBefore = Vec<PointClaim<F>>;
    type ClaimsAfter = SinglePointClaims<F>;

    fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, mut advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let gamma = transcript.challenge(128);
        let fun = FoldedProdAlgFn::new(gamma, self.nargs);
        let folded_claim = gamma_rlc(gamma, &claims.iter().map(|c| c.ev).collect_vec());

        advice.extend(claims.iter().map(|p| EqPoly::new(self.nvars, &p.point).evals()));

        let so = DenseSumcheckObjectSO::new(
            advice,
            fun.clone(),
            self.nvars,
            folded_claim,
        );

        let degrees = repeat_n(fun.deg(), self.nvars);
        let generic_protocol_config = GenericSumcheckProtocol::new(degrees);

        let ((_, output_point), mut poly_evs) = generic_protocol_config.prove(transcript, so.claim, so);

        let evs = poly_evs[..self.nargs].to_vec();
        transcript.write_scalars(&evs);
        (
            SinglePointClaims {
                point: output_point,
                evs,
            },
            ()
        )
    }

    fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        assert_eq!(claims.len(), self.nargs);

        let gamma = transcript.challenge(128);
        let fun = FoldedProdAlgFn::new(gamma, self.nargs);
        let folded_claim = gamma_rlc(gamma, &claims.iter().map(|c| c.ev).collect_vec());

        let degrees = repeat_n(fun.deg(), self.nvars);
        let generic_protocol_config = GenericSumcheckProtocol::<_, _, DenseSumcheckObjectSO<F, FoldedProdAlgFn<F>>>::new(degrees);

        let (claim, output_point) = generic_protocol_config.verify(transcript, folded_claim);

        let evs = transcript.read_scalars(self.nargs);
        let mut extended_evs = evs.clone();
        extended_evs.extend(claims.iter().map(|p| EqPoly::new(self.nvars, &p.point).evaluate(&output_point)));

        assert_eq!(claim, fun.exec(&extended_evs), "Final combinator check has failed.");

        SinglePointClaims {
            point: output_point,
            evs,
        }
    }
}