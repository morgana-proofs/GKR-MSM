use super::*;
use ark_ff::{biginteger::{BigInt, BigInteger64 as B1}, BigInteger};

use ark_ff::PrimeField;
use liblasso::utils::math::Math;

use super::non_native_equalizer::bit_utils::{*, BitMath};

use std::ops::Neg;


#[derive(Debug, Default, Clone)]
pub struct PolynomialWithZeros<F: PrimeField>{
    // evals is a list of (non-zero) evaluations; the real eval list has length 2**log_len with the last several evals being zero
    // e.g. if we want to encode bits of a 254-bit number as evals, len should be 254, and log_len is 8
    evals: Vec<F>,
    len: usize,
    log_len: usize,
}


impl <F:PrimeField> PolynomialWithZeros<F>{
    fn new(evals: &[F]) -> Self
    {
        let eval_vec = evals.into();
        let len = evals.len();
        let log_len = len.log_2();

        PolynomialWithZeros{
            evals: eval_vec,
            len,
            log_len
        }
    }

    // for testing
    fn evaluate(&self, r: &[F]) -> F
    {
        assert_eq!(r.len(), self.log_len, "trying to evaluate at a point with different dimention");

        let ans = self.evals.iter().enumerate().map(
            |(i, ev)|{
                let i_bits = i.to_bits(self.log_len);
                let copol = i_bits
                    .iter()
                    .zip(r)
                    .map(|(&y, ev)|
                        match y {
                            true => ev.to_owned(),
                            false => F::one() - ev.to_owned(),
                    }).fold(F::one(), |acc, x| acc*x);
                copol*ev
            }  
        ).fold(F::zero(), |acc, x| acc+x);
        ans


    }
    
}


mod tests{
    use super::*;

    use ark_bls12_381::Fr;
    use ark_bls12_381::Fq;
    use ark_bls12_381::G1Projective;
    use ark_ff::{MontBackend};
    use ark_std::{test_rng, UniformRand};
    use ark_std::rand::Rng;
    use liblasso::poly;
    use liblasso::utils::math::Math;
    use crate::transcript::IndexedProofTranscript;
    use liblasso::utils::test_lib::TestTranscript;

    #[test]
    fn test_polynomial_new(){

        let mut rng  = test_rng();
        let num_limbs = 3;
        let limb_len = roundup_to_pow2( Fq::MODULUS_BIT_SIZE  as usize / num_limbs);

        let poly_size = 6u64;
        let log_poly_size = 3u64;

        let poly1: Vec<_> =  (0..poly_size).map(|i| Fq::from(i)).collect();
        let poly2: Vec<_> =  (0..poly_size).map(|i| Fq::from(i+1)).collect();
        // let r_bits = big_num_to_bits_F(r);
        let point: Vec<_> = (0..log_poly_size).map(|i| Fq::from(2*i + 1)).collect();

        let p1 = PolynomialWithZeros::new(&poly1);
        let value1 = p1.evaluate(&point);
        
        let p2 = PolynomialWithZeros::new(&poly2);
        let value2 = p2.evaluate(&point);

        assert_eq!(p1.len, poly_size as usize);
        assert_eq!(p1.log_len, log_poly_size as usize);
        assert_eq!(value1 +  Fq::from(78), Fq::from(0));
        assert_eq!(value2 +  Fq::from(78)+  Fq::from(15), Fq::from(1));

    }
}



