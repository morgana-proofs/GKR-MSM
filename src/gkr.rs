use std::marker::PhantomData;
use ark_ff::PrimeField;
use crate::protocol::{IndexedProofTranscript, TranscriptReceiver, TranscriptSender, Challenge, Protocol, ProtocolProver, ProtocolVerifier};

pub struct GKR<F: PrimeField> {
    _pd: PhantomData<F>,
}

pub struct GKRProver<F: PrimeField> {
    _pd: PhantomData<F>,
}


pub struct GKRVerifier<F: PrimeField> {
    _pd: PhantomData<F>,
}

// pub struct GKRProof<F: PrimeField> {
//
// }

impl<F: PrimeField> Protocol<F> for GKR<F> {
    type Prover = GKRProver<F>;
    type Verifier = GKRVerifier<F>;
    type ClaimsToReduce = ();
    type ClaimsNew = ();
    type WitnessInput = ();
    type WitnessOutput = ();
    type Proof = ();
    type Params = ();

    fn witness(args: &Self::WitnessInput, params: &Self::Params) -> Self::WitnessOutput {
        todo!()
    }
}

impl<F: PrimeField> ProtocolProver<F> for GKRProver<F> {
    type ClaimsToReduce = ();
    type ClaimsNew = ();
    type Proof = ();
    type Params = ();
    type WitnessInput = ();

    fn start(claims_to_reduce: Self::ClaimsToReduce, args: Self::WitnessInput, params: &Self::Params) -> Self {
        todo!()
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T) -> Option<(Self::ClaimsNew, Self::Proof)> {
        todo!()
    }
}

impl<F: PrimeField> ProtocolVerifier<F> for GKRVerifier<F> {
    type Params = ();
    type ClaimsToReduce = ();
    type ClaimsNew = ();
    type Proof = ();

    fn start(claims_to_reduce: Self::ClaimsToReduce, proof: Self::Proof, params: &Self::Params) -> Self {
        todo!()
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T) -> Option<Self::ClaimsNew> {
        todo!()
    }
}