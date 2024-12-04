use ark_ff::PrimeField;
use itertools::Itertools;
use liblasso::poly::eq_poly::EqPolynomial;
use crate::utils::eq_poly_sequence_last;

pub fn evaluate_poly<F: PrimeField>(poly: &[F], pt: &[F]) -> F {
    let e_p = eq_poly_sequence_last(&pt.to_vec()).unwrap();
    poly.iter().zip_eq(e_p.iter()).map(|(&a, b)| a * b).sum::<F>()
}
