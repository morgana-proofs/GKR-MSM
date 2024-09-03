// make equalizer limbs:

use std::ops::Deref;

//use ark_ff::BigInt;

use super::*;
use crate::polynomial::fragmented::Shape;
use ark_ff::{biginteger::{BigInt, BigInteger64 as B1}, BigInteger};

use ark_ff::PrimeField;



pub mod bit_utils{
    use liblasso::utils::math::Math;

    use super::*;
    pub fn big_num_to_limbs<F1: PrimeField, F2: PrimeField>(x: &F1, limb_len: usize) -> Vec<F2>
    {
        let x = x.into_bigint();
        x.to_bits_le()
            .chunks(limb_len)
            .map(|bits| F2::from(F2::BigInt::from_bits_le(bits)))
            .collect()

    }


    pub fn big_num_to_bits_u64<const N: usize>(x: BigInt<N>) -> Vec<u64>
    {
        x.to_bits_le().iter().map(|&b| b as u64).collect()
    }


    pub fn big_num_to_bits_F<F: PrimeField, const N: usize>(x: BigInt<N>) -> Vec<F>
    { 
        x.to_bits_le().iter().map(|&b| F::from(b as u64)).collect()
    }

    
    pub fn roundup_to_pow2(x: usize) -> usize
    { 
        x.log_2().pow2()
    }

    pub fn transpose<T>(v: Vec<Vec<T>>) -> Vec<Vec<T>> // credit https://stackoverflow.com/questions/64498617/how-to-transpose-a-vector-of-vectors-in-rust
    where
        T: Clone,
    {
        assert!(!v.is_empty());
        (0..v[0].len())
            .map(|i| v.iter().map(|inner| inner[i].clone()).collect::<Vec<T>>())
            .collect()
    }
}

use bit_utils::*;

pub fn make_equalizer_limbs<FNat: PrimeField, FNonNat:  PrimeField>(
    point: &Vec<FNonNat>,
    limb_len: usize,
    poly_size: usize,
) -> Vec<FragmentedPoly<FNat>>
{
    let evals: Vec<FNonNat> = (0..poly_size as u64).map(
        |x| {
            let x_bits = FNonNat::BigInt::from(x).to_bits_le();
            x_bits
                .iter()
                .zip(point)
                .map(|(&y, r)|
                    match y {
                        true => r.to_owned(),
                        false => FNonNat::one() - r.to_owned(),
                })
                .fold(FNonNat::one(), |acc, x| acc*x)
        })
        .collect();

    let eval_limbs_transposed: Vec<_> = evals.iter().map(|x| big_num_to_limbs::<FNonNat, FNat>(x, limb_len)).collect();

    let eval_limbs = transpose(eval_limbs_transposed);

    let polys = eval_limbs.iter().map(|limbs| FragmentedPoly::new(limbs.clone(), vec![FNat::zero()], Shape::full(limb_len))).collect();
    
    polys

}
 
mod tests{
    use super::*;

    use ark_bls12_381::Fr;
    use ark_bls12_381::Fq;
    use ark_bls12_381::G1Projective;
    use ark_ff::{MontBackend};
    use ark_std::{test_rng, UniformRand};
    use ark_std::rand::Rng;
    use liblasso::utils::math::Math;
    use crate::protocol::protocol::MultiEvalClaim;
    use crate::protocol::protocol::{ProtocolVerifier, ProtocolProver};
    use crate::protocol::sumcheck::{*, SumcheckPolyMapVerifier, SumcheckPolyMapProver};
    use crate::transcript::Challenge;
    use crate::transcript::IndexedProofTranscript;
    use liblasso::utils::test_lib::TestTranscript;

    #[test]
    fn test_equalizer(){

        let mut rng  = test_rng();
        let num_limbs = 3;
        let limb_len = roundup_to_pow2( Fq::MODULUS_BIT_SIZE  as usize / num_limbs);

        let poly_size = 64;

        let r =  (0..poly_size).map(|_| Fq::rand(&mut rng)).collect();
        // let r_bits = big_num_to_bits_F(r);

        //assert_eq!(r_bits.len(), num_limbs * limb_len);

        let polys : Vec<FragmentedPoly<Fr>> = make_equalizer_limbs::<Fr, Fq>(
            &r,
            limb_len,
            poly_size
        );

        assert_eq!(polys.len(), num_limbs);

    }
}