use std::marker::PhantomData;
use ark_ff::PrimeField;
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::sumcheck::SinglePointClaims;

pub struct ZeroCheck<F> {
    _pd: PhantomData<F>,
}

impl<F> ZeroCheck<F> {
    pub fn new() -> Self {
        Self {
            _pd: PhantomData,
        }
    }
}
impl<Transcript: TProofTranscript2, F: PrimeField> Protocol2<Transcript> for ZeroCheck<F> {
    type ProverInput = ();
    type ProverOutput = ();
    type ClaimsBefore = SinglePointClaims<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    fn prove(&self, transcript: &mut Transcript, mut claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        claims.evs.push(F::zero());
        claims.evs.push(F::zero());
        (claims, ())
        
    }

    fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        self.prove(transcript, claims, ()).0
    }
}