// Implements two polynomials:
// E_t(y) - polynomial with evaluations 1, t, t^2, ..., t^{m-1}, 0, 0, 0... and its verifier-side evaluation function (can be relatively inefficient, because in practice m is relatively small in all applications)
// E_pt(x, y) - polynomial which contains the limbs of E_pt(x) over non-native field.
// data layout of E_pt(x, y) adheres to the one used in matrix-poly - i.e. every column (values with fixed x and varying y) are layed out in chunks of length m [...][...][...][...]. Padding 0s are not allocated.

use std::ops::Sub;
use super::{BitMath};
use ark_ff::{biginteger::{BigInt, BigInteger64 as B1}, BigInteger};
use ark_ff::{Field, PrimeField};
use liblasso::utils::math::Math;
use ark_std::{One, Zero, UniformRand};


fn fe_to_limbs<F: PrimeField>(x: &F, limb_size: usize) -> Vec<u64>
{
    let x = x.into_bigint();

    assert_eq!(limb_size%8, 0);

    x.to_bytes_le()
        .chunks(limb_size/8)
        .map(|bytes| u64::from_le_bytes(bytes.try_into().unwrap()))
        .collect()

}


#[derive(Debug, Default, Clone)]
pub struct Eqpoly<F: Zero>{
    evals: Vec<F>,
    num_limbs_in_fe: usize,
    limb_size: usize,
}



impl<F: PrimeField> Eqpoly<F>{
    fn new<NNF: PrimeField>(pt: &[NNF], limb_size: usize, num_limbs: usize) -> Self{
        assert!((NNF::MODULUS_BIT_SIZE  as usize) <( limb_size * num_limbs), "not enough limbs");
        let num_var = pt.len();
        let poly_size = 1<<num_var;
        let evals: Vec<_> = (0..poly_size).map(
            |x| {
                let x_bits = x.to_bits(num_var);
                let factor = x_bits
                    .iter()
                    .zip(pt)
                    .map(|(&y, r)|
                        match y {
                            true => *r,
                            false => NNF::one() - r,
                    })
                    //.collect::<Vec<_>>()
                    .fold(NNF::one(), |acc, x| acc*x);
                let factor_limbs = fe_to_limbs(&factor, limb_size);
                factor_limbs.iter().map(|x| F::from(*x)).collect::<Vec<_>>()
            })
            .flatten()
            .collect();

        

        Eqpoly{
                evals,
                num_limbs_in_fe: num_limbs,
                limb_size: limb_size,
            }   
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
        // let limb_size = roundup_to_pow2( Fq::MODULUS_BIT_SIZE  as usize / num_limbs);

        let (limb_size, num_limbs) = (64, 6);

        let dim = 5;
        let pt: Vec<_> = (1..dim).map(|_| Fq::rand(&mut rng)).collect();

        let poly : Eqpoly<Fr> = Eqpoly::new(&pt, limb_size, num_limbs);


        println!("{} , {}", Fq::MODULUS_BIT_SIZE  as usize, limb_size * num_limbs);

        println!("{:?}", poly.evals.len());
        


    }

}