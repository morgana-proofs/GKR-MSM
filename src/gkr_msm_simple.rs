use ark_ec::CurveGroup;
use ark_ff::PrimeField;

use crate::utils::TwistedEdwardsConfig;

pub trait MSMCircuitConfig {
    type F : PrimeField;
    type CommitmentGroup : CurveGroup<ScalarField = Self::F>;
    type Curve : CurveGroup<Config : TwistedEdwardsConfig>;
}


pub struct MSMCircuit {}

/// Creates bit decompositions 
pub fn prepare_witness<M: MSMCircuitConfig>(scalars: &[M::F], num_columns: usize) -> () {
    let scalars_per_column = div_ceil(scalars.len(), num_columns);

}


fn div_ceil(x: usize, y: usize) -> usize {
    (x + y - 1) / y
}

fn log_ceil(x: usize) -> usize {
    let mut k = 0;
    assert!(x > 0, "logarithm of zero");
    let mut x = x - 1;
    while x > 0 {
        k += 1;
        x >>= 1;
    }
    k
}