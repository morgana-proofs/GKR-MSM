// Commit
// 1. Prepare multilinear polynomial $P\in\mathbb{F}_p[\mathbf{x}]$ of $n$ variables. Denote $P(\mathbf{x}) = \sum_{a\in\mathbb{B}^n}c_a[\mathbf{x}==a]$
// 2. Represent $c_a = c_{a,>}2^{128}+c_{a,<}$ for each $a$.
// 3. Commit to two multilinear polynomials over $\mathbb{F}_q$, defined as  $P_<(\mathbf{x}) = \sum_{a\in\mathbb{B}^n}c_{a,<}[\mathbf{x}==a]$ and $P_>(\mathbf{x}) = \sum_{a\in\mathbb{B}^n}c_{a,>}[\mathbf{x}==a]$.
// 4. Prepare a proof $\mathcal{R}$ that the coefficients of $P_<,P_>$ are range-checked.


use ark_ff::BigInteger;
use liblasso::poly::dense_mlpoly::DensePolynomial;

use super::*;
use num_traits::{One, Zero};
//use std::iter::DoubleEndedIterator;
use crate::gkr_msm_simple::{CommitmentKey, MSMCircuitConfig, MSMProof};



pub fn bytes_to_bit(
    n: Vec<u8>,
) -> Vec<u8>
{
    let mut bits = vec![];
    for byte in n{
        for i in 0..8 {
            let mask = 1 << (7 - i);
            let bit_is_set = ((mask & byte) > 0) as u8;
            bits.push(bit_is_set);
        }
    }
    bits

}


pub fn prime_field_element_to_bits<F: PrimeField>(
    n: F,
) -> Vec<F>
{
    //type B = <F as PrimeField>::BigInt;
    //let zero = <F as PrimeField>::BigInt::from(0u64);
    let mut bigint_n: <F as PrimeField>::BigInt = n.into_bigint();
    big_integer_to_bits(bigint_n)
    //println!("{:?}\n", ans);
}


pub fn big_integer_to_bits<F: PrimeField, B: BigInteger>(
    bigint_n: B,
) -> Vec<F>
{
    //type B = <F as PrimeField>::BigInt;
    let bytes = bigint_n.to_bytes_be();
    let ans: Vec<F> = bytes_to_bit(bytes).iter()
                                        .map(|&x| F::from_le_bytes_mod_order(&[x]))
                                        .collect();
    //println!("{:?}\n", ans);
    ans
}

fn transpose<T>(v: Vec<Vec<T>>) -> Vec<Vec<T>>
where
    T: Clone,
{
    assert!(!v.is_empty());
    (0..v[0].len())
        .map(|i| v.iter().map(|inner| inner[i].clone()).collect::<Vec<T>>())
        .collect()
}

// takes a polynomial with evaluations in F that can be treated as non-negative integers
// returns a list of polynomial with evaluations in F that are bits of the original polynomial
// e.g. input = {p(0) = 0, p(1) = 1, p(2) = 2, p(3) = 3}
// output = vec![{p(0) = 0, p(1) = 1, p(2) = 0, p(3) = 1}, {p(0) = 0, p(1) = 0, p(2) = 1, p(3) = 1}]
pub fn polynomial_from_values_to_bits<F: PrimeField>(
    p: DensePolynomial<F>,
) -> Vec<DensePolynomial<F>>
{
    let (num_vars, len, Z) = (p.num_vars, p.len, p.Z);
    let v: Vec<_> = Z.iter()
                                    .map(|&x| prime_field_element_to_bits(x))
                                    .collect();
    let w = transpose(v);
    let ans: Vec<_> = w.iter()
                    .map(|x| DensePolynomial{num_vars, len, Z: x.to_vec()})
                    .collect();
    ans
}


pub fn commit_bits<
    F: PrimeField + TwistedEdwardsConfig,
    T: TranscriptReceiver<F> + TranscriptSender<F>,
    G: CurveGroup<ScalarField = F>,
>(
    scalars: Vec<DensePolynomial<F>>,
    log_num_points: usize,
    log_num_scalar_bits: usize,
    log_num_bit_columns: usize, // Logamount of columns that host the bitvector. Normally ~5-6 should be reasonable.
    ck: &CommitmentKey<G>,
    transcript: &mut T,
) -> (EvalClaim<F>, MSMProof<G>)    
{    
    let bit_polys = vec![];
    let pow_two = BigUint::one() << limb_size;

     todo!();
}




// // takes a polynomial with evaluations in F that can be treated as non-negative integers
// // returns a list of polynomial with evaluations in F that are bits of the original polynomial
// // e.g. input = {p(0) = 0, p(1) = 1, p(2) = 2, p(3) = 3}
// // output = vec![{p(0) = 0, p(1) = 1, p(2) = 0, p(3) = 1}, {p(0) = 0, p(1) = 0, p(2) = 1, p(3) = 1}]
// pub fn polynomial_from_values_to_bits<F: PrimeField>(
//     p: DensePolynomial<F>,
// ) -> Vec<DensePolynomial<F>>
// {
//     let values = vec![];
//     let Z = p.Z;
//     todo!();
// }


mod tests{
    use ark_bls12_381::Fq as Fq;
    use ark_ff::MontBackend;
    use ark_std::{test_rng, UniformRand};
    use ark_std::rand::Rng;
    use super::*;


    #[test]
    fn test_smolnum() {
        prime_field_element_to_bits(Fq::from(3));
        prime_field_element_to_bits(Fq::from(4));
        prime_field_element_to_bits(Fq::from(5));
        prime_field_element_to_bits(Fq::from(6));
    }

    #[test]
    fn test_bignum() {
        let mut rng = test_rng();
        println!("{:?}\n", (prime_field_element_to_bits((Fq::rand(&mut rng)))));
        println!("{:?}\n", (prime_field_element_to_bits(Fq::from(521))));
    }
    #[test]
    fn test_dense_poly_to_bits() {
        let mut rng = test_rng();
        let three = Fq::from(3);
        let four = Fq::from(4);
        let fiveee = Fq::from(500);
        let sixxx = Fq::from(600);
        let Z = vec![three, four, fiveee, sixxx];
        let inp = DensePolynomial{
            num_vars : 2,
            len : 4,
            Z
        };
        println!("{:?}\n\n", polynomial_from_values_to_bits(inp));
        //println!("{:?}", <ark_ff::Fp<MontBackend<ark_bls12_381::FqConfig, 6>, 6> as ark_ff::PrimeField>::BigInt::from(1u64));
    }
}


// pub fn preparation_from_bigint_to_field<F: PrimeField>(
//     p: DensePolynomial<BigUint>,
//     limb_size: usize,
// ) -> Vec<DensePolynomial<F>>
// {    
//     let bit_polys = vec![];
//     let pow_two = 2i32.pow(limb_size as u32);
    
    

//     todo!();

// }