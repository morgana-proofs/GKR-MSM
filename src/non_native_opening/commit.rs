// Commit
// 1. Prepare multilinear polynomial $P\in\mathbb{F}_p[\mathbf{x}]$ of $n$ variables. Denote $P(\mathbf{x}) = \sum_{a\in\mathbb{B}^n}c_a[\mathbf{x}==a]$
// 2. Represent $c_a = c_{a,>}2^{128}+c_{a,<}$ for each $a$.
// 3. Commit to two multilinear polynomials over $\mathbb{F}_q$, defined as  $P_<(\mathbf{x}) = \sum_{a\in\mathbb{B}^n}c_{a,<}[\mathbf{x}==a]$ and $P_>(\mathbf{x}) = \sum_{a\in\mathbb{B}^n}c_{a,>}[\mathbf{x}==a]$.
// 4. Prepare a proof $\mathcal{R}$ that the coefficients of $P_<,P_>$ are range-checked.


//use ark_ff::One;
use liblasso::poly::dense_mlpoly::DensePolynomial;

use super::*;
//use num_bigint::BigInt;
use num_traits::{One, Zero};
use::ark_ff::biginteger::BigInt;


// takes a number 
pub fn big_number_to_bits<F: PrimeField>(
    n: F,
) -> Vec<F>
{
    let two = <F as PrimeField>::BigInt::one()+ <F as PrimeField>::BigInt::one();
    let bigint_n = n.into_bigint();
    todo!();
}

// takes a polynomial with evaluations in F that can be treated as non-negative integers
// returns a list of polynomial with evaluations in F that are bits of the original polynomial
// e.g. input = {p(0) = 0, p(1) = 1, p(2) = 2, p(3) = 3}
// output = vec![{p(0) = 0, p(1) = 1, p(2) = 0, p(3) = 1}, {p(0) = 0, p(1) = 0, p(2) = 1, p(3) = 1}]
pub fn polynomial_from_values_to_bits<F: PrimeField>(
    p: DensePolynomial<F>,
) -> Vec<DensePolynomial<F>>
//where F: 
{
    todo!();
}

pub fn preparation_from_field<F: PrimeField>(
    p: DensePolynomial<F>,
    limb_size: usize,
) -> Vec<DensePolynomial<F>>
{    
    let bit_polys = vec![];
    let pow_two = BigUint::one() << limb_size;

    

    todo!();

}

pub fn preparation_from_bigint_to_field<F: PrimeField>(
    p: DensePolynomial<BigUint>,
    limb_size: usize,
) -> Vec<DensePolynomial<F>>
{    
    let bit_polys = vec![];
    let pow_two = 2i32.pow(limb_size as u32);
    
    

    todo!();

}