use ark_ec::{CurveGroup, ScalarMul};
use ark_ff::PrimeField;

use crate::utils::TwistedEdwardsConfig;

pub trait MSMCircuitConfig {
    type F : PrimeField;
    type Comm : CurveGroup<ScalarField = Self::F>;
    type G : CurveGroup<Config : TwistedEdwardsConfig>;
}


pub struct MSMCircuit {}

pub fn msm_input<M : MSMCircuitConfig>(bases: &[<M::G as ScalarMul>::MulBase]) -> () {

}