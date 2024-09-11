// This module contains everything related to our pushforward argument.

use std::marker::PhantomData;

use ark_ff::{Field, PrimeField};

use crate::polynomial::fragmented::FragmentedPoly;

use super::protocol::{Protocol, ProtocolProver, ProtocolVerifier};

pub struct PushforwardProtocol<F: Field> {
    _marker: PhantomData<F>,
}

pub struct PushforwardProver<F: Field> {
    _marker: PhantomData<F>,
}

pub struct PushforwardVerifier<F: Field> {
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PushforwardParams<F: Field> {
    default_value: Vec<F>, // the tuple that gets written in all empty cells
    row_size: usize,
    num_rows: usize,

    counters_logsizes: Vec<usize>, 
}

impl<F: Field> PushforwardParams<F> {
    pub fn new(default_value: Vec<F>, row_size: usize, num_rows: usize, counters_logsizes: Vec<usize>) -> Self {
        Self { default_value, row_size, num_rows, counters_logsizes }
    }

    pub fn default_value(&self) -> Vec<F> {
        self.default_value.clone()
    }

    pub fn row_size(&self) -> usize {
        self.row_size
    }

    pub fn num_rows(&self) -> usize {
        self.num_rows
    }

    pub fn counters_logsizes(&self) -> Vec<usize> {
        self.counters_logsizes.clone()
    }
    
    pub fn counters_sizes(&self) -> Vec<usize> {
        self.counters_logsizes.iter().map(|x| 1 << x).collect()
    }

    pub fn num_counters(&self) -> usize {
        self.counters_logsizes.len()
    }
}


impl<F: PrimeField> Protocol<F> for PushforwardProtocol<F> {
    type Prover = PushforwardProver<F>;
    type Verifier = PushforwardVerifier<F>;

    type ClaimsToReduce = ();
    type ClaimsNew = ();
    type WitnessInput = Vec<FragmentedPoly<F>>;
    type Trace = Vec<FragmentedPoly<F>>;
    type WitnessOutput = Vec<FragmentedPoly<F>>;
    type Proof = ();
    type Params = (PushforwardParams<F>);

    fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
        todo!()
    }
}

impl<F: PrimeField> ProtocolProver<F> for PushforwardProver<F> {
    type ClaimsToReduce = ();
    type ClaimsNew = ();
    type Proof = ();
    type Params = PushforwardParams<F>;
    type Trace = Vec<FragmentedPoly<F>>;
    
    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        args: Self::Trace,
        params: &Self::Params,
    ) -> Self {
        todo!()
    }
    
    fn round<T: crate::transcript::TranscriptReceiver<F>>(&mut self, challenge: crate::transcript::Challenge<F>, transcript: &mut T)
        ->
    Option<(Self::ClaimsNew, Self::Proof)> {
        todo!()
    }
}

impl<F: PrimeField> ProtocolVerifier<F> for PushforwardVerifier<F> {
    type ClaimsToReduce = ();
    type ClaimsNew = ();
    type Proof = ();
    type Params = PushforwardParams<F>;
    
    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        proof: Self::Proof,
        params: &Self::Params,
    ) -> Self {
        todo!()
    }
    
    fn round<T: crate::transcript::TranscriptReceiver<F>>(&mut self, challenge: crate::transcript::Challenge<F>, transcript: &mut T) 
        -> 
    Option<Self::ClaimsNew> {
        todo!()
    }

}
