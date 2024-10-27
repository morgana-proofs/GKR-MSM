use std::marker::PhantomData;
use ark_ff::PrimeField;
use itertools::Itertools;
use merlin::Transcript;
use crate::cleanup::proof_transcript::{TProofTranscript2};
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::sumcheck::{AlgFn, SinglePointClaims};
use crate::polynomial::vecvec::VecVecPolynomial;
use crate::cleanup::protocols::sumchecks::vecvec_eq::{VecVecDeg2Sumcheck, VecVecDeg2SumcheckObject};

pub trait GKRLayer<Transcript: TProofTranscript2, Claims, Advice> {
    fn prove_layer(&self, transcript: &mut Transcript, claims: Claims, advice: Advice) -> Claims;
    fn verify_layer(&self, transcript: &mut Transcript, claims: Claims) -> Claims;
}

pub struct SimpleGKR<Claims, Advice, Transcript: TProofTranscript2, WitnessGenerator> {
    layers: Vec<Box<dyn GKRLayer<Transcript, Claims, Advice>>>,
    _pd: PhantomData<WitnessGenerator>
}

impl<Claims, Advice, Transcript: TProofTranscript2, WitnessGenerator: Iterator<Item=Advice>> SimpleGKR<Claims, Advice, Transcript, WitnessGenerator> {
    pub fn new(layers: Vec<Box<dyn GKRLayer<Transcript, Claims, Advice>>>) -> Self {
        Self {
            layers,
            _pd: Default::default(),
        }
    }
}

impl<Claims, Advice, Transcript: TProofTranscript2, AdviceIterator: Iterator<Item=Advice>> Protocol2<Transcript> for SimpleGKR<Claims, Advice, Transcript, AdviceIterator> {
    type ProverInput = AdviceIterator;
    type ProverOutput = ();
    type ClaimsBefore = Claims;
    type ClaimsAfter = Claims;

    fn prove(&self, transcript: &mut Transcript, mut claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        for (layer, layer_advice) in self.layers.iter().rev().zip_eq(advice) {
            claims = layer.prove_layer(transcript, claims, layer_advice);
        }
        (claims, ())
    }

    fn verify(&self, transcript: &mut Transcript, mut claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        for layer in self.layers.iter().rev() {
            claims = layer.verify_layer(transcript, claims);
        }
        claims
    }
}


#[cfg(test)]
mod test {}