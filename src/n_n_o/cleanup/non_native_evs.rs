// Implements two polynomials:
// E_t(y) - polynomial with evaluations 1, t, t^2, ..., t^{m-1}, 0, 0, 0... and its verifier-side evaluation function (can be relatively inefficient, because in practice m is relatively small in all applications)
// E_pt(x, y) - polynomial which contains the limbs of E_pt(x) over non-native field.
// data layout of E_pt(x, y) adheres to the one used in matrix-poly - i.e. every column (values with fixed x and varying y) are layed out in chunks of length m [...][...][...][...]. Padding 0s are not allocated.
#[allow(unused_imports)]

use std::{cmp::min, mem::MaybeUninit, ops::Sub};
use crate::cleanup::protocols::sumcheck::PointClaim;

use super::utils::bit_utils::{BitMath, *};
use ark_ff::{biginteger::{BigInt, BigInteger64 as B1}, BigInteger};
use ark_ff::{Field, PrimeField};
use hashcaster::ptr_utils::{AsSharedMUMutPtr, UninitArr, UnsafeIndexMut, UnsafeIndexRawMut};
use liblasso::{poly::eq_poly, utils::math::Math};
use ark_std::{One, Zero, UniformRand};
use rayon::{current_num_threads, iter::{IntoParallelIterator, ParallelIterator}, slice::ParallelSlice};


pub fn native_repr<F: PrimeField, NNF: PrimeField>(poly: &[NNF]) -> Vec<F> {
    let factor = 8 * current_num_threads();
    let l = poly.len();
    let limbsize = NNF::zero().into_bigint().as_ref().len();
    
    let mut ret = UninitArr::<F>::new(l * limbsize);
    let ret_ptr = ret.as_shared_mut_ptr();

    (0 .. factor).into_par_iter().map(|task_id| {
        (task_id * factor .. min((task_id + 1) * factor, l)).map(|i| {
            let p = poly[i].into_bigint();
            let p = p.as_ref();
            for s in 0..limbsize {
                unsafe{*(ret_ptr.get_mut(i * limbsize + s)) = F::from(p[s])};
            }
        }).count();
    }).count();
    unsafe{ret.assume_init()}
}



#[derive(Debug, Default, Clone)]
pub struct Eqpoly<F: Zero>{
    pub evals: Vec<F>,
    num_limbs_in_fe: usize,
}


impl<F: Zero + From<u64>> Eqpoly<F>{
    pub fn new<NNF: PrimeField>(pt: &[NNF], num_limbs: usize) -> Self{
        assert!((NNF::MODULUS_BIT_SIZE  as usize) < (64 * num_limbs), "not enough limbs");
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
                let factor_limbs = fe_to_limbs(&factor);
                factor_limbs.iter().map(|x| F::from(*x)).collect::<Vec<_>>()
            })
            .flatten()
            .collect();

        

        Eqpoly{
                evals,
                num_limbs_in_fe: num_limbs,
            }   
        }
    }

// pub fn make_equalizer_limbs<const N :usize, NNF: PrimeField>(pt: &[NNF]) -> ([u64; N], [u64; N]){
//     // where NNF::BigInt::N = N;
//     assert!((NNF::MODULUS_BIT_SIZE  as usize) < (64 * N*2), "not enough limbs");
//     let num_var = pt.len();
//     let poly_size = 1<<num_var;
//     let evals: Vec<_> = (0..poly_size).map(
//         |x| {
//             let x_bits = x.to_bits(num_var);
//             let factor = x_bits
//                 .iter()
//                 .zip(pt)
//                 .map(|(&y, r)|
//                     match y {
//                         true => *r,
//                         false => NNF::one() - r,
//                 })
//                 //.collect::<Vec<_>>()
//                 .fold(NNF::one(), |acc, x| acc*x);
//             let factor_limbs = fe_to_limbs(&factor);
//             factor_limbs.iter().map(|x| F::from(*x)).collect::<Vec<_>>()
//         })
//         .flatten()
//         .collect();

//     let mut eq_poly = Eqpoly::new_u64_limbs(pt, num_limbs);
//     let mid = eq_poly.evals.len();
//     eq_poly.evals.split_at(mid)

// }

mod tests{
    #[allow(unused_imports)]

    use super::*;

    use ark_bls12_381::Fr;
    use ark_bls12_381::Fq;
    use ark_bls12_381::G1Projective;
    use ark_ff::{MontBackend};
    use ark_std::{test_rng, UniformRand};
    use ark_std::rand::Rng;
    use itertools::Itertools;
    use liblasso::utils::math::Math;
    use crate::protocol::protocol::MultiEvalClaim;
    use crate::protocol::protocol::{ProtocolVerifier, ProtocolProver};
    use crate::protocol::sumcheck::{*, SumcheckPolyMapVerifier, SumcheckPolyMapProver};
    use crate::transcript::Challenge;
    use crate::transcript::IndexedProofTranscript;
    use liblasso::utils::test_lib::TestTranscript;

    #[test]
    fn native_repr_works() {
        let rng = &mut test_rng();
        let nn_poly = (0..5).map(|_| Fq::rand(rng)).collect_vec();
        
        let s = (Fq::zero()).into_bigint().as_ref().len();
        println!("Number of 64 bit limbs: {}", (Fq::zero()).into_bigint().as_ref().len());

        let native_repr = native_repr::<Fr, Fq>(&nn_poly);

        let mut expected_native_repr = vec![];

        for i in 0..5 {
            let x = nn_poly[i].into_bigint();
            for j in 0..x.as_ref().len() {
                expected_native_repr.push(Fr::from(x.as_ref()[j]));
            }
        }

        assert_eq!(native_repr, expected_native_repr);
    }

    #[test]
    fn test_equalizer(){

        let mut rng  = test_rng();
        // let limb_size = roundup_to_pow2( Fq::MODULUS_BIT_SIZE  as usize / num_limbs);

        let (limb_size, num_limbs) = (64, 6);

        let dim = 5;
        let pt: Vec<_> = (1..dim).map(|_| Fq::rand(&mut rng)).collect();

        let poly : Eqpoly<u64> = Eqpoly::new(&pt, num_limbs);
        let poly : Eqpoly<Fr> = Eqpoly::new(&pt, num_limbs);

        // let coeffs = (1..(1<<dim)).map(|_| Fq::rand(&mut rng)).collect();
        // let evals = 

    }

}