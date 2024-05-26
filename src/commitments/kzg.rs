// This implements non-hiding KZG commitments (in a form typically used in PlonK, i.e. powers of tau in first group, and
// only a single power of tau in a second group).

// Lagrange form is unimplemented, as we will not need it.

use std::fs::File;

use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_std::One;
use ark_ec::CurveGroup;
use liblasso::msm::VariableBaseMSM;
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;

pub struct KzgSrs<Ctx: Pairing> {
    ptau_1: Vec<Ctx::G1Affine>,
    h0: Ctx::G2Affine,
    h1: Ctx::G2Affine,
}

/// Computes quotient and remainder of division of p(x)/(x-a)
pub fn div_by_linear<F: PrimeField>(poly: &[F], pt: F) -> (Vec<F>, F) {
    let mut quotient = vec![F::zero(); poly.len()-1];
    let mut rem = poly[poly.len()-1];
    for i in (0..quotient.len()).rev() {
        quotient[i] = rem;
        rem = poly[i] + rem*pt;
    }
    (quotient, rem)
}

impl<Ctx: Pairing> KzgSrs<Ctx> {
    pub fn mock_setup(tau: Ctx::ScalarField, g0: Ctx::G1Affine, h0: Ctx::G2Affine, size: usize) -> Self {
        let mut powers_of_tau = Vec::with_capacity(size);
        let mut p = Ctx::ScalarField::one();
        for _ in 0..size {
            powers_of_tau.push(p);
            p *= tau;
        }

        let h1 : Ctx::G2Affine = (h0 * tau).into();

        let ptau1_proj : Vec<Ctx::G1> = powers_of_tau.into_par_iter().map(|sc| g0 * sc).collect();

        Self{ptau_1: Ctx::G1::normalize_batch(&ptau1_proj), h0, h1}
    }

    pub fn load(file: &mut File) -> Self {
        todo!()
    }

    pub fn dump(&self, file: &mut File) {
        todo!()
    }

    pub fn ptau_1(&self) -> &[Ctx::G1Affine] {
        &self.ptau_1
    }

    pub fn h0(&self) -> &Ctx::G2Affine {
        &self.h0
    }

    pub fn h1(&self) -> &Ctx::G2Affine {
        &self.h1
    }

    pub fn commit(&self, v: &[Ctx::ScalarField]) -> Ctx::G1Affine {
        assert!(v.len() <= self.ptau_1.len(), "Vector is too large.");
        <Ctx::G1 as VariableBaseMSM>::msm(&self.ptau_1[..v.len()], v).unwrap().into()
    }
}

#[cfg(test)]
mod tests {
use ark_bls12_381::Fr;

use super::div_by_linear;

    #[test]
    fn quotient() {
        let poly : Vec<Fr> = vec![1, 3, 3, 7, 2, 0, 2, 4].into_iter().map(|x|Fr::from(x)).collect();
        let pt = Fr::from(322);
        println!("{:?}", div_by_linear(&poly, pt).1);
    }
}
