use ark_bls12_381::Fr;
use ark_bls12_381::G1Projective;
use ark_ff::{MontBackend};
use ark_std::{test_rng, UniformRand};
use ark_std::rand::Rng;
use super::open::*;
use super::bit_utils::*;
use super::*;
use crate::protocol::protocol::MultiEvalClaim;
use crate::protocol::protocol::{ProtocolVerifier, ProtocolProver};
use crate::protocol::sumcheck::{*, SumcheckPolyMapVerifier, SumcheckPolyMapProver};
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
fn test_sumcheck_lite_mod() {
    let gen = &mut test_rng();

    let num_vars: usize = 5;
    let polys: Vec<NestedPolynomial<Fr>> = (0..3).map(|_| NestedPolynomial::rand(gen, 5)).collect();

    fn combfunc(i: &[Fr]) -> Vec<Fr> {
        vec![i[0], i[1], i[2] * i[2] * i[0], i[2] * i[2] * i[0]]
    }

    let params = SumcheckPolyMapParams {
        f: PolynomialMapping {
            exec: Arc::new(combfunc),
            degree: 3,
            num_i: 3,
            num_o: 4,
        },
        num_vars,
    };

    let (trace, image_polys) = SumcheckPolyMap::witness(polys.clone(), &params);

    let point: Vec<Fr> = (0..(num_vars as u64)).map(|i| Fr::from(i * 13)).collect();
    let claims : Vec<_> = image_polys.iter().enumerate().map(|(i, p)| (i, p.evaluate(&point))).collect();

    let _point = point.clone();

    let multiclaim = MultiEvalClaim {
        points: vec![point],
        evs: vec![claims.clone()],
    };


    let mut prover = SumcheckPolyMapProver::start(
        multiclaim.clone(),
        trace,
        &params,
    );

    let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
    let gamma_c = p_transcript.challenge_scalar(b"challenge_combine_outputs");
    let mut res = prover.round(gamma_c, &mut p_transcript);
    while res.is_none() {
        let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
        res = prover.round(challenge, &mut p_transcript);
    }

    println!("{:?}", p_transcript.transcript.log);

    let (EvalClaim{point: proof_point, evs}, proof) = res.unwrap();
    assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

    let mut verifier = SumcheckPolyMapVerifier::start(
        multiclaim,
        proof,
        &params,
    );

    let mut v_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));
    let gamma_c = v_transcript.challenge_scalar(b"challenge_combine_outputs");
    let mut res = verifier.round(gamma_c, &mut v_transcript);
    while res.is_none() {
        let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
        res = verifier.round(challenge, &mut v_transcript);
    }

    println!("{:?}", v_transcript.transcript.log);

    let EvalClaim{point: proof_point, evs} = res.unwrap();
    assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());
}