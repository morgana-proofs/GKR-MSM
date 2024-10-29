use ark_ff::PrimeField;
use itertools::Itertools;
use liblasso::poly::eq_poly::EqPolynomial;


pub fn evaluate_poly<F: PrimeField>(poly: &[F], pt: &[F]) -> F {
    let e_p = EqPolynomial::new(pt.to_vec());
    poly.iter().zip_eq(e_p.evals().iter()).map(|(&a, b)| a * b).sum::<F>()
}
