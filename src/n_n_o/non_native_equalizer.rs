// make equalizer limbs
//use ark_ff::BigInt;

use super::*;
use crate::polynomial::fragmented::Shape;
use ark_ff::{biginteger::{BigInt, BigInteger64 as B1}, BigInteger};

use ark_ff::PrimeField;
use liblasso::utils::math::Math;
use std::ops::{Shl, Shr, BitAnd};



use super::cleanup::utils::bit_utils::*;

pub fn make_equalizer_limbs<FNat: PrimeField, FNonNat:  PrimeField>(
    point: &Vec<FNonNat>,
    limb_len: usize,
    poly_size: usize,
) -> Vec<FragmentedPoly<FNat>>
{
    let evals: Vec<FNonNat> = (0..poly_size).map(
        |x| {
            let x_bits = x.to_bits(poly_size.log_2());
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

    let eval_limbs_transposed: Vec<_> = evals.iter().map(|x| big_num_to_limbs::<FNonNat, FNat>(&x, limb_len)).collect();

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

    // #[test]
    // fn test_equalizer(){

    //     let mut rng  = test_rng();
    //     let num_limbs = 3;
    //     let limb_len = roundup_to_pow2( Fq::MODULUS_BIT_SIZE  as usize / num_limbs);

    //     let num_vars = 6;
    //     let poly_size = 1<<num_vars;

    //     let r =  (0..poly_size).map(|_| Fq::rand(&mut rng)).collect();
    //     // let r_bits = big_num_to_bits_F(r);

    //     //assert_eq!(r_bits.len(), num_limbs * limb_len);

    //     let polys : Vec<FragmentedPoly<Fr>> = make_equalizer_limbs::<Fr, Fq>(
    //         &r,
    //         limb_len,
    //         poly_size
    //     );

    //     assert_eq!(polys.len(), num_limbs);

    // }
}