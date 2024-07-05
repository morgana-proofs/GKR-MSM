use ark_bls12_381::Fr;
use ark_bls12_381::Fq;
use ark_bls12_381::G1Projective;
use ark_ff::{MontBackend};
use ark_std::{test_rng, UniformRand};
use ark_std::rand::Rng;
use super::open::*;
use super::bit_utils::*;
use super::*;
use crate::nested_poly::NestedPoly;
use crate::protocol::protocol::MultiEvalClaim;
use crate::protocol::protocol::{ProtocolVerifier, ProtocolProver};
use crate::protocol::sumcheck::{*, SumcheckPolyMapVerifier, SumcheckPolyMapProver};
use crate::transcript::Challenge;
use crate::transcript::IndexedProofTranscript;
use liblasso::utils::test_lib::TestTranscript;



#[test]
fn field_size(){
    let mut rng = test_rng();

    let evals: Vec<_> = (0..4).map(|_| Fr::rand(&mut rng))
                                .collect();
    let eval_bits: Vec<_> = evals.iter()
                                .map( |&x|prime_field_element_to_bool_bits(x))
                                .collect();

    let point: Vec<_> = (0..2).map(|_|Fr::rand(&mut rng))
                                .collect(); 

    let point_bits: Vec<_> = point.iter()
                                .map( |&x|prime_field_element_to_bool_bits(x))
                                .collect();
    
    let the_eval = evals[0] 
                + (evals[1] - evals[0])*point[0]
                + (evals[2] - evals[0])*point[1]
                + (evals[3] - evals[2] - evals[1] + evals[0])*point[0]*point[1]; 

    let eval_claim = to_multieval(
        EvalClaim{
        point,
        evs: vec![the_eval],

    });

    let challenge_t = Fr::rand(&mut rng);

    opening::<Fr>(eval_bits, point_bits, eval_claim, 2, MY_FAVORITE_LIMB_SIZE, challenge_t);
}




#[test]
fn test_mini_msm(){
    use merlin::Transcript;

    let mut rng = test_rng();
    let evals: Vec<_> = (0..2).map(|_| Fr::one())
                                .collect();
    let eval_bits: Vec<_> = evals.iter()
                                .map( |&x|prime_field_element_to_bool_bits(x))
                                .collect();

    
    let mut p_transcript = Transcript::new(b"test");

    mini_msm::<Fr, Transcript>(eval_bits,  &mut p_transcript);
}


#[test]
fn test_equalizer_1(){
    println!("{:?}", elemenary_equalizer_poly(Fr::one(), 0, 2));
    println!("{:?}", elemenary_equalizer_poly(Fr::zero(), 1, 2));
}

#[test]
fn test_equalizer_2(){
    let point = vec![Fr::one(), Fr::zero()];
    println!("{:?}", equalizer_poly(point, 2));
}

#[test]
fn test_equalizer_3(){
    let point = vec![Fr::from(5u64), Fr::from(2u64)];
    println!("{:?}", equalizer_poly(point.clone(), 2));
    println!("{:?}, {:?}", equalizer_poly(point.clone(), 2)[1] + Fr::from(5u64), equalizer_poly(point.clone(), 2)[2] + Fr::from(8u64));
}



#[test]
fn test_sumcheck_mite_mod() {
    let gen = &mut test_rng();

    let num_i =  3;

    let non_native_field_num_bits = Fq::MODULUS_BIT_SIZE as usize;
    
    let num_vars: usize = non_native_field_num_bits.log_2();
    let num_vars = 1;

    let values_bits = vec![
        vec![Fr::one(); non_native_field_num_bits],
        vec![Fr::zero(); non_native_field_num_bits],
        vec![Fr::zero(); non_native_field_num_bits],
        vec![Fr::one(); non_native_field_num_bits],
    ];

    // let values_exponents = powers_of_t(Fr::from(2), 64);
    // let polys_exponents = vec![{
    //     let my_nested_poly = NestedPoly::from_values_uncontinued(values_exponents.clone());
    //     NestedPolynomial::new(my_nested_poly, vec![num_vars])
    // }];


    // let polys: Vec<NestedPolynomial<Fr>> = values_bits.iter().map(|values| 
    //     {
    //         let my_nested_poly = NestedPoly::from_values_uncontinued(values.clone());
    //         NestedPolynomial::new(my_nested_poly, vec![num_vars])
    //     })
    //     .chain(polys_exponents)
    //     .collect();
        
    let polys: Vec<NestedPolynomial<Fr>> = (0..num_i).map(|i| 
        {
            //let my_values = vec![Fr::zero(), Fr::one(), Fr::from(2u64)];//, Fr::one(), Fr::from((i % 2) as u64), Fr::one(), Fr::zero(), Fr::one()];
            let my_nested_poly1 = NestedPoly::from_values(vec![Fr::zero(), Fr::one()], Fr::zero());
            let my_nested_poly2 = NestedPoly::from_values(vec![Fr::one() + Fr::from(3*i as u64), Fr::zero()], Fr::zero());
            let my_nested_poly = NestedPoly::from_polys(vec![my_nested_poly1, my_nested_poly2], Fr::zero());

            NestedPolynomial::new(my_nested_poly, vec![1, num_vars])
        }).collect();

        // fn combfunc(i: &[Fr]) -> Vec<Fr> {
        //     vec![Fr::from(2u64) + i[0] *i[0] * i[1], i[2]]
        // }
        // let num_o = 2;

        fn combfunc(i: &[Fr]) -> Vec<Fr> {
            vec![i[0]*i[1] + i[2]]
        }
        let num_o = 1;

    let params = SumcheckPolyMapParams {
        f: PolynomialMapping {
            exec: Arc::new(combfunc),
            degree: 3,
            num_i,
            num_o,
        },
        num_vars: num_vars + 1,
    };

    let (trace, image_polys) = SumcheckPolyMap::witness(polys.clone(), &params);

    let point: Vec<Fr> = (0..(num_vars as u64 + 1)).map(|i| Fr::from(1 - i)).collect();
    let claims : Vec<_> = image_polys.iter().enumerate().map(|(i, p)| (i, p.evaluate(&point))).collect();

    let multiclaim = MultiEvalClaim {
        points: vec![point],
        evs: vec![claims.clone()],
    };

    println!("{:?}", multiclaim);


    let mut prover = SumcheckPolyMapProver::start(
        multiclaim.clone(),
        trace,
        &params,
    );

    let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
    //let gamma_c = p_transcript.challenge_scalar(b"challenge_combine_outputs");
    let gamma_c = Challenge{value: Fr::from(2u64)};
    let mut res = prover.round(gamma_c, &mut p_transcript);
    let mut counter = 0u64;
    while res.is_none() {
        let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
        let challenge = Challenge{value: Fr::from(counter)};
        res = prover.round(challenge, &mut p_transcript);
        counter += 1;
        
     //   println!("polys : {:?},\n round_polys : {:?},\n rs : {:?},\n claims : {:?},\n, num_vars : {:?},\n", 
            // prover.polys,
            // prover.round_polys,
            // prover.rs,
            // prover.claims,
            // prover.num_vars,
            // );

    }

    //println!("{:?}", p_transcript.transcript.log);
    //println!("{:?}", res);
    use std::ops::Neg;
    let (EvalClaim{point: proof_point, evs}, proof) = res.unwrap();
    //let (evals, proof) = res.unwrap();
    println!("\nsup, {:?}, {:?}\n", proof_point, evs.iter().map(|x| (x, x.neg() )).collect_vec());
    //assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

    // let mut verifier = SumcheckPolyMapVerifier::start(
    //     multiclaim,
    //     proof,
    //     &params,
    // );

    // let mut v_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));
    // let gamma_c = v_transcript.challenge_scalar(b"challenge_combine_outputs");
    // let mut res = verifier.round(gamma_c, &mut v_transcript);
    // while res.is_none() {
    //     let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
    //     res = verifier.round(challenge, &mut v_transcript);
    // }

    // println!("{:?}", v_transcript.transcript.log);

    // let EvalClaim{point: proof_point, evs} = res.unwrap();
    // assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());
}

