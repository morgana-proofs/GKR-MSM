// We use GKR-logup in a following fashion:

// There is a collection of pairs of polynomials, treated as numerators and denominators. Different pairs might have different logsizes.
// We then do the following two processes
// WHILE logsize > 0:
//     WHILE there exists a unique pair with max logsize:
//         do normal bintree GKR
//     WHILE there are two pairs with max logsize:
//         merge them

// This process is optimal in terms of verifier rounds, but it spits out different claims for different polynomials.
// We circumvent it by doing a first phase synchronously (which is application-specific and needs to be combined with other protocols, anyway).
// I.e. this protocol will spit out different claims, but the separate first layer will reduce these claims to openings in somewhat related points.

// Most annoying part of this is a witness generator. Currently, we will just do it for dense polynomials (but if this becomes a hotspot and we will need to
// to move to padded ones, the pain will be immense).

use std::marker::PhantomData;

use ark_ff::PrimeField;
use hashcaster::ptr_utils::{AsSharedMUMutPtr, UninitArr, UnsafeIndexRawMut};
use itertools::Itertools;
use rayon::iter::IntoParallelIterator;

use crate::cleanup::protocols::splits::{SplitAt, SplitIdx};
use crate::cleanup::protocols::sumcheck::{DenseEqSumcheck, SinglePointClaims};
use crate::cleanup::{proof_transcript::TProofTranscript2, protocol2::Protocol2, protocols::sumcheck::PointClaim, utils::algfn::AlgFnUtils};
use crate::cleanup::utils::algfn::{AlgFn, AlgFnSO};


#[derive(Debug, Clone, Copy)]
pub struct LogupLayerFn<F: PrimeField> {
    _marker: PhantomData<F>,
}

impl<F: PrimeField> LogupLayerFn<F> {
    pub fn new() -> Self {
        Self { _marker: PhantomData }
    }
}

impl<F: PrimeField> AlgFn<F> for LogupLayerFn<F>{
    fn exec(&self, args: &impl std::ops::Index<usize, Output = F>) -> impl Iterator<Item = F> {
        [
            args[0] * args[3] + args[1] * args[2], // ad + bc
            args[1] * args[3]                      // bd
        ].into_iter()
    }

    fn deg(&self) -> usize {
        2
    }

    fn n_ins(&self) -> usize {
        4
    }

    fn n_outs(&self) -> usize {
        2
    }
}




#[derive(Clone)]
pub struct LogupMainphaseProtocol<F: PrimeField> {
    pub logsizes: Vec<usize>,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> LogupMainphaseProtocol<F> {

    /// Assumes that first two logsizes have the same length - i.e. they corresponding polynomial is already split.
    pub fn new(logsizes: Vec<usize>) -> Self {
        assert!(logsizes.len() > 1);
        for i in 0 .. logsizes.len() - 1 {
            assert!(logsizes[i] >= logsizes[i+1], "logsizes must be non-increasing")
        }
        assert!(logsizes[0] == logsizes[1]);

        Self { logsizes, _marker: PhantomData }
    }

    pub fn make_witness(&self, input: Vec<[Vec<F>; 2]>) -> (Vec<[Vec<F>; 2]>, [F; 2]) {
        input.iter().zip_eq(self.logsizes.iter()).for_each(|(fraction_arr, logsize)| assert!(fraction_arr[0].len() == 1 << logsize && fraction_arr[1].len() == 1 << logsize));

        let mut input = input;
        input.reverse();
        
        let mut layers : Vec<[Vec<F>; 2]> = vec![];
        layers.push(input.pop().unwrap());
        layers.push(input.pop().unwrap());
        
        let mut i = 0;

        let f = LogupLayerFn::new();
        
        // This cycle is concerned with 2 last elements of layers (they always have the same size). If the next advice has the same size, it maps them without splitting, and fetches next advice.
        // If the next advice is smaller, then it maps and splits.
        // First option will be chosen if there is no next advice and size == 1, in which case it will just push the final mapping result and break from the cycle.
        loop {
            let next_size = input.last().map_or(1, |arr|arr[0].len());
            let curr_size = layers[i][0].len();

            if curr_size == next_size {                    
                let a0 = &layers[i];
                let a1 = &layers[i+1];
                let out = f.map(&[&a0[0], &a0[1], &a1[0], &a1[1]]);
                layers.push(out.try_into().unwrap());
                if let Some(adv) = input.pop() {
                    layers.push(adv)
                } else {break};
                i += 2;

            } else if curr_size > next_size {
                let a0 = &layers[i];
                let a1 = &layers[i+1];    
                let out = f.map_split_hi(&[&a0[0], &a0[1], &a1[0], &a1[1]]);
                let [out0, out1] = out;
                layers.push(out0.try_into().unwrap());
                layers.push(out1.try_into().unwrap());
                i += 2;
            } else {
                unreachable!()
            }
        }

        let tmp = layers.pop().unwrap();
        assert!(tmp[0].len() == 1);
        assert!(tmp[1].len() == 1); // sanity

        let n = tmp[0][0];
        let d = tmp[1][0];

        (layers, [n, d])
    }
}

impl<F: PrimeField, PT: TProofTranscript2> Protocol2<PT> for LogupMainphaseProtocol<F> {
    type ProverInput = Vec<[Vec<F>; 2]>;

    type ProverOutput = ();

    type ClaimsBefore = ();

    type ClaimsAfter = Vec<SinglePointClaims<F>>; // In reality, some of these opening points might coincide, but not in our case + we don't care for now.

    fn prove(&self, transcript: &mut PT, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let f = LogupLayerFn::<F>::new();

        let (mut witness, [num, denom]) = self.make_witness(advice);

        assert!(num == F::zero()); // we are checking that the sum is equal to zero
        assert!(denom != F::zero()); // sanity check. verifier will not need to check this.
        transcript.write_scalars(&[denom]);

        let mut logsizes = self.logsizes.clone();

        let mut curr_logsize = 0;
        let mut running_claim = SinglePointClaims{ point: vec![], evs: vec![num, denom] };
        let mut accumulated_claims = vec![];

        let tmp =
            loop {
                let incoming_logsize = logsizes.last().unwrap();                 

                let protocol = DenseEqSumcheck::new(f, curr_logsize);

                let [advice_r_0, advice_r_1] = witness.pop().unwrap();
                let [advice_l_0, advice_l_1] = witness.pop().unwrap();    
                let advice = vec![advice_l_0, advice_l_1, advice_r_0, advice_r_1];

                let (claim_4, _) = protocol.prove(
                    transcript,
                    running_claim.clone(),
                    advice
                );

                if *incoming_logsize == curr_logsize {
                    if logsizes.len() == 2 {
                        break claim_4
                    }
                    running_claim = SinglePointClaims{ point: claim_4.point.clone(), evs: vec![claim_4.evs[0], claim_4.evs[1]] };
                    accumulated_claims.push(SinglePointClaims{ point: claim_4.point, evs: vec![claim_4.evs[2], claim_4.evs[3]] });
                    logsizes.pop();
                } else {
                    let split = SplitAt::new(SplitIdx::HI(0), 2);
                    (running_claim, _) = split.prove(transcript, claim_4, ());
                    curr_logsize += 1;
                }

            };
            
        accumulated_claims.push(tmp);
        accumulated_claims.reverse();
        (accumulated_claims, ())

    }

    fn verify(&self, transcript: &mut PT, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let f = LogupLayerFn::<F>::new();

        let num = F::zero();
        let denom = transcript.read_scalars(1)[0];
        
        let mut logsizes = self.logsizes.clone();
        let mut curr_logsize = 0;
        let mut running_claim = SinglePointClaims{ point: vec![], evs: vec![num, denom] };
        let mut accumulated_claims = vec![];

        let tmp =
            loop {
                let incoming_logsize = logsizes.last().unwrap();                 

                let protocol = DenseEqSumcheck::new(f, curr_logsize);
                let claim_4 = protocol.verify(
                    transcript,
                    running_claim.clone()
                );

                if *incoming_logsize == curr_logsize {
                    if logsizes.len() == 2 {
                        break claim_4
                    }
                    running_claim = SinglePointClaims{ point: claim_4.point.clone(), evs: vec![claim_4.evs[0], claim_4.evs[1]] };
                    accumulated_claims.push(SinglePointClaims{ point: claim_4.point, evs: vec![claim_4.evs[2], claim_4.evs[3]] });
                    logsizes.pop();
                } else {
                    let split = SplitAt::new(SplitIdx::HI(0), 2);
                    (running_claim, _) = split.prove(transcript, claim_4, ());
                    curr_logsize += 1;
                }
            };

        accumulated_claims.push(tmp);
        accumulated_claims.reverse();
        accumulated_claims
    }
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::Fr;
    use crate::cleanup::{proof_transcript::ProofTranscript2, protocols::sumcheck::evaluate_univar, utils::arith::evaluate_poly};

    use super::*;
    use ark_std::{UniformRand, test_rng, Zero, One};

    #[test] 
    fn witness_gen_works() {
        let rng = &mut test_rng();
        let logsizes = vec![5, 5, 3, 3, 3, 3, 1, 0, 0, 0];
        let mut input = vec![];
        
        let mut expected_sum = Fr::zero();

        for logsize in &logsizes {
            let quotient : Vec<_> = (0 .. 1 << logsize).map(|_| Fr::rand(rng)).collect();
            let denominator : Vec<_> = (0 .. 1 << logsize).map(|_| Fr::rand(rng)).collect();
            let numerator : Vec<_> = quotient.iter().zip(denominator.iter()).map(|(&a, &b)| a * b).collect();
            for q in quotient {
                expected_sum += q
            }
            input.push([numerator, denominator]);
        }

        let protocol = LogupMainphaseProtocol::new(logsizes);

        let [n, d] = protocol.make_witness(input).1;
        assert!(d != Fr::zero());
        assert!(expected_sum * d == n)
    }


    #[test]

    fn logup_maincycle_works() {
        let rng = &mut test_rng();
        let logsizes = vec![5, 5, 3, 3, 3, 3];
        let mut input = vec![];

        for logsize in &logsizes {
            let mut acc = Fr::zero();
            
            let mut quotient : Vec<_> = (0 .. (1 << logsize) - 1).map(|_| {
                let tmp = Fr::rand(rng);
                acc += tmp;
                tmp
            }).collect();

            quotient.push(- acc); // enforce that the actual sum is zero

            let denominator : Vec<_> = (0 .. 1 << logsize).map(|_| Fr::rand(rng)).collect();
            let numerator : Vec<_> = quotient.iter().zip(denominator.iter()).map(|(&a, &b)| a * b).collect();

            input.push([numerator, denominator]);
        }

        let protocol = LogupMainphaseProtocol::new(logsizes);
        let mut p_transcript = ProofTranscript2::start_prover(b"awoo");


        let (p_claims, _) = protocol.prove(&mut p_transcript, (), input.clone());

        let proof = p_transcript.end();

        println!("proof size in bytes: {}", proof.len());

        let mut v_transcript = ProofTranscript2::start_verifier(b"awoo", proof);

        let v_claims = protocol.verify(&mut v_transcript, ());

        assert_eq!(p_claims, v_claims);

        let mut claims = p_claims;
        input.reverse();
        claims.reverse();

        // process first and second separately

        let SinglePointClaims { point, evs } = claims.pop().unwrap();

        let poly0 = input.pop().unwrap();
        let poly1 = input.pop().unwrap();

        assert!( evaluate_poly(&poly0[0], &point) == evs[0]);
        assert!( evaluate_poly(&poly0[1], &point) == evs[1]);
        assert!( evaluate_poly(&poly1[0], &point) == evs[2]);
        assert!( evaluate_poly(&poly1[1], &point) == evs[3]);

        while let Some(poly) = input.pop() {
            let SinglePointClaims { point, evs } = claims.pop().unwrap();

            assert!(evaluate_poly(&poly[0], &point) == evs[0]);
            assert!(evaluate_poly(&poly[1], &point) == evs[1]);
        }

    }
}