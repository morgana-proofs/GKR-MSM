use std::sync::Arc;

use ark_ff::PrimeField;

use crate::transcript::{Challenge, TranscriptReceiver};

#[derive(Clone)]
pub struct PolynomialMapping<F: PrimeField> {
    pub exec: Arc<dyn Fn(&[F]) -> Vec<F> + Send + Sync>,
    pub degree: usize,
    pub num_i: usize,
    pub num_o: usize,
}

// Claim
#[derive(Clone)]
#[allow(dead_code)]
pub struct Claim<F: PrimeField> {
    pub point: Vec<F>,
    pub value: F,
}

#[derive(Clone)]
pub struct MultiEvalClaim<F: PrimeField> {
    pub points: Vec<Vec<F>>,
    pub evs: Vec<Vec<(usize, F)>>,
}

#[derive(Clone)]
pub struct EvalClaim<F: PrimeField> {
    pub point: Vec<F>,
    pub evs: Vec<F>,
}


pub trait Protocol<F: PrimeField> {

    type Prover : ProtocolProver<
        F,
        ClaimsToReduce = Self::ClaimsToReduce,
        ClaimsNew = Self::ClaimsNew,
        Proof = Self::Proof,
        Params = Self::Params,
        Trace = Self::Trace,
    >;

    type Verifier : ProtocolVerifier<
        F,
        ClaimsToReduce = Self::ClaimsToReduce,
        ClaimsNew = Self::ClaimsNew,
        Proof = Self::Proof,
        Params = Self::Params,
    >;

    type ClaimsToReduce;
    type ClaimsNew;
    type WitnessInput;
    type Trace;
    type WitnessOutput;
    type Proof;
    type Params;

    fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput);
}


pub trait ProtocolProver<F: PrimeField> {

    type ClaimsToReduce;
    type ClaimsNew;
    type Proof;
    type Params;
    type Trace;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        args: Self::Trace,
        params: &Self::Params,
    ) -> Self;


    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
        ->
    Option<(Self::ClaimsNew, Self::Proof)>;
}

pub trait ProtocolVerifier<F: PrimeField> {
    type Params;
    type ClaimsToReduce;
    type ClaimsNew;
    type Proof;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        proof: Self::Proof,
        params: &Self::Params,
    ) -> Self;


    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T) 
        -> 
    Option<Self::ClaimsNew>;
}