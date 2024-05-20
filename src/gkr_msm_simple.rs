use ark_ec::{CurveGroup, ScalarMul};
use ark_ff::PrimeField;
use std::fs::{File};
use ark_serialize::*;

use crate::utils::TwistedEdwardsConfig;

pub trait MSMCircuitConfig {
    type F : PrimeField;
    type Comm : CurveGroup<ScalarField = Self::F>;
    type G : CurveGroup<Config : TwistedEdwardsConfig>;
}

pub struct ExtendedBases<G: CurveGroup>{
    packing_factor: usize,
    values: Vec<Vec<G::Affine>>,
}

pub struct Committer<G: CurveGroup> {
    bases: Option<Vec<G::Affine>>,
    binary_extended_bases: Option<Vec<Vec<G::Affine>>>,
}

impl<G: CurveGroup> Committer<G> {
    pub fn new() -> Self {
        Self {bases: None, binary_extended_bases: None}
    }
    
    pub fn load(&mut self, file: &mut File) {
        todo!()
    }

    pub fn commit_vec(&self, v: &[G::ScalarField]) -> G{
        G::msm(self.bases.as_ref().unwrap(), v).unwrap()
    }

}




pub struct MSMCircuit {}

pub fn msm_input<M : MSMCircuitConfig>(bases: &[<M::G as ScalarMul>::MulBase]) -> () {
}