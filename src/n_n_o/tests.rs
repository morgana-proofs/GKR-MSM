use super::polynomial_with_zeros::*;
use super::non_native_equalizer::bit_utils::*;
use super::non_native_equalizer::*;

use ark_bls12_381::Fr;
use ark_bls12_381::Fq;
use ark_bls12_381::G1Projective;
use ark_ec::scalar_mul;
use ark_ff::{MontBackend, PrimeField};
use ark_std::{test_rng, UniformRand};
use ark_std::rand::Rng;
use liblasso::poly;
use liblasso::utils::math::Math;

use rayon::iter::plumbing::UnindexedConsumer;
use rayon::prelude::*;

use std::iter;
use crate::transcript::IndexedProofTranscript;
use liblasso::utils::test_lib::TestTranscript;
use ark_std::Zero;

// #[test]
// fn test_polynomial_new(){

//     let mut rng  = test_rng();
//     let num_limbs = 3;
//     let limb_len = roundup_to_pow2( Fq::MODULUS_BIT_SIZE  as usize / num_limbs);

//     let poly_size = 6u64;
//     let log_poly_size = 3u64;

//     let poly1: Vec<_> =  (0..poly_size).map(|i| Fq::from(i)).collect();
//     let poly2: Vec<_> =  (0..poly_size).map(|i| Fq::from(i+1)).collect();
//     // let r_bits = big_num_to_bits_F(r);
//     let point: Vec<_> = (0..log_poly_size).map(|i| Fq::from(2*i + 1)).collect();

//     let p1 = PolynomialWithZeros::new(&poly1);
//     let value1 = p1.evaluate(&point);
    
//     let p2 = PolynomialWithZeros::new(&poly2);
//     let value2 = p2.evaluate(&point);

//     assert_eq!(p1.len, poly_size as usize);
//     assert_eq!(p1.log_len, log_poly_size as usize);
//     assert_eq!(value1 +  Fq::from(78), Fq::from(0));
//     assert_eq!(value2 +  Fq::from(78)+  Fq::from(15), Fq::from(1));

// }


#[test]
fn test_polynomial_sum_1d(){

    let mut rng  = test_rng();
    let num_limbs = 3;
    let limb_len = roundup_to_pow2( Fq::MODULUS_BIT_SIZE  as usize / num_limbs);

    let poly_size1 = rand::thread_rng().gen_range(0..128);
    let poly_size2 = rand::thread_rng().gen_range(0..128);
    let log_poly_size = 7;

    for _ in 0..10{
        let p1 = PolynomialWithZeros::rand(&mut rng, poly_size1, log_poly_size);
        let p2 = PolynomialWithZeros::rand(&mut rng, poly_size2, log_poly_size);

        let p1_evals = p1.clone().evals;
        let p2_evals = p2.clone().evals;

        let mut sum_p = p1.clone();
        sum_p += &p2;
        let sum_evals = sum_p.evals;
        let mut diff_p = p2.clone();
        diff_p -= &p1;
        let diff_evals = diff_p.evals;

        let check_sum = p1_evals.iter()
                                        .zip(p2_evals.iter()
                                                    .chain(iter::repeat(&Fq::zero())))
                                        .zip(sum_evals.iter()
                                                    .chain(iter::repeat(&Fq::zero())))
                                        .all(|((a, b), c)| a.clone() + b.clone() - c.clone() == Fq::zero());

        assert!(check_sum, "sum bad");

        
        let check_diff = p1_evals.iter()
                                        .zip(p2_evals.iter()
                                                    .chain(iter::repeat(&Fq::zero())))
                                        .zip(diff_evals.iter()
                                                    .chain(iter::repeat(&Fq::zero())))
                                        .all(|((a, b), c)| b.clone() - a.clone() - c.clone() == Fq::zero());
    
        assert!(check_diff, "diff bad");
    }
}





#[test]
fn test_polynomial_sum_evals(){

    let mut rng  = test_rng();
    let num_limbs = 3;
    let limb_len = roundup_to_pow2( Fq::MODULUS_BIT_SIZE  as usize / num_limbs);

    let poly_size = 6u64;
    let log_poly_size = 3u64;

    let poly1: Vec<_> =  (0..poly_size).map(|i| Fq::from(i)).collect();
    let poly2: Vec<_> =  (0..poly_size + 1).map(|i| Fq::from(i+1)).collect();
    
    let p1 = PolynomialWithZeros::new(&poly1);
    let p2 = PolynomialWithZeros::new(&poly2);

    let sum_p_1 = p1.sum();
    let sum_p_2 = p2.sum();

    let expected_sum_1 = Fq::from(poly_size*(poly_size - 1)/2);
    let expected_sum_2 = Fq::from((poly_size+2)*(poly_size + 1)/2);


    println!("sum_p = {:?}, diff_p = {:?}\n", sum_p_1, sum_p_2);

    
    assert_eq!( sum_p_1, expected_sum_1, "first sum failed");
    assert_eq!( sum_p_2, expected_sum_2, "second sum failed");
}


use std::os::unix::thread;
use rand::thread_rng;
use super::n_n_sumcheck::NonNatOpen;
use crate::protocol::sumcheck::Sumcheckable;


#[test]
fn test_nnat_open_split(){

    let mut rng  = thread_rng();

    let num_vars = 7;
    let num_polys = 10;

    let polys: Vec<PolynomialWithZeros<Fq>> = (0..num_polys)
            .map(|_| PolynomialWithZeros::rand(&mut rng, thread_rng().gen_range(0..1<<num_vars), num_vars))
            .collect();

    let point: Vec<_> = (0..num_vars)
            .map( |_| Fq::rand(&mut rng))
            .collect();

    let mut test_opener = NonNatOpen::new_from_polys(&polys);

    let vals: Vec<_> = polys.clone().iter()
            .map(|p| p.evaluate(&point))
            .collect();

    (0..num_vars).map(|i| test_opener.bind(&point[i])).count();

    let final_evals = test_opener.final_evals();

    (0..num_polys).map(|i| 
        {
            assert_eq!(test_opener.polys[i].evals.len(), 1);
            assert_eq!(test_opener.polys[i].evals[0], vals[i]);
            assert_eq!(final_evals[i], vals[i]);
        })
        .count();

}




