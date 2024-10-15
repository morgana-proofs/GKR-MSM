use std::marker::PhantomData;
use ark_ff::PrimeField;
use itertools::Itertools;
use merlin::Transcript;
use crate::cleanup::proof_transcript::{TProofTranscript2};
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::sumcheck::{AlgFn, SinglePointClaims};
use crate::polynomial::vecvec::VecVecPolynomial;
use crate::protocol::sumcheckv2::{VecVecDeg2Sumcheck, VecVecDeg2SumcheckObject};

pub trait GKRLayer<Transcript: TProofTranscript2, Claims, Advice> {
    fn prove_layer(&self, transcript: &mut Transcript, claims: Claims, advice: Advice) -> Claims;
    fn verify_layer(&self, transcript: &mut Transcript, claims: Claims) -> Claims;
}

pub struct SimpleGKR<Claims, Advice, Transcript: TProofTranscript2, WitnessGenerator> {
    layers: Vec<Box<dyn GKRLayer<Transcript, Claims, Advice>>>,
    _pd: PhantomData<WitnessGenerator>
}

impl<Claims, Advice, Transcript: TProofTranscript2, WitnessGenerator: Iterator<Item=Advice>> SimpleGKR<Claims, Advice, Transcript, WitnessGenerator> {
    pub fn new(layers: Vec<Box<dyn GKRLayer<Transcript, Claims, Advice>>>) -> Self {
        Self {
            layers,
            _pd: Default::default(),
        }
    }
}

impl<Claims, Advice, Transcript: TProofTranscript2, AdviceIterator: Iterator<Item=Advice>> Protocol2<Transcript> for SimpleGKR<Claims, Advice, Transcript, AdviceIterator> {
    type ProverInput = AdviceIterator;
    type ProverOutput = ();
    type ClaimsBefore = Claims;
    type ClaimsAfter = Claims;

    fn prove(&self, transcript: &mut Transcript, mut claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        for (layer, layer_advice) in self.layers.iter().rev().zip_eq(advice) {
            claims = layer.prove_layer(transcript, claims, layer_advice);
        }
        (claims, ())
    }

    fn verify(&self, transcript: &mut Transcript, mut claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        for layer in self.layers.iter().rev() {
            claims = layer.verify_layer(transcript, claims);
        }
        claims
    }
}

impl<Transcript: TProofTranscript2, F: PrimeField, Fun: AlgFn<F>> GKRLayer<Transcript, SinglePointClaims<F>, Vec<VecVecPolynomial<F>>> for VecVecDeg2Sumcheck<F, Fun> {
    fn prove_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>, advice: Vec<VecVecPolynomial<F>>) -> SinglePointClaims<F> {
        Protocol2::prove(self, transcript, claims.into(), advice.into()).0
    }

    fn verify_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>) -> SinglePointClaims<F> {
        Protocol2::verify(self, transcript, claims.into())
    }
}


#[cfg(test)]
mod test {
    mod toy {
        use crate::cleanup::proof_transcript::{ProofTranscript2, TProofTranscript2};
        use crate::cleanup::protocol2::Protocol2;
        use crate::cleanup::protocols::gkr::{GKRLayer, SimpleGKR};

        struct Add {
            p: u8
        }

        struct Mul {
            p: u8
        }

        impl<Transcript: TProofTranscript2> Protocol2<Transcript> for Add {
            type ProverInput = u8;
            type ProverOutput = u8;
            type ClaimsBefore = u8;
            type ClaimsAfter = u8;

            fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
                transcript.write_raw_msg(&[advice]);
                (claims + advice + self.p, 1)
            }

            fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
                let advice = transcript.read_raw_msg(1)[0];
                claims + advice + self.p
            }
        }
        impl<Transcript: TProofTranscript2> Protocol2<Transcript> for Mul {
            type ProverInput = u8;
            type ProverOutput = ();
            type ClaimsBefore = u8;
            type ClaimsAfter = u8;

            fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
                transcript.write_raw_msg(&[advice]);
                (claims * advice * self.p, ())
            }

            fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
                let advice = transcript.read_raw_msg(1)[0];
                claims * advice * self.p
            }
        }
        
        impl<Transcript: TProofTranscript2> GKRLayer<Transcript, u8, u8> for Add {
            fn prove_layer(&self, transcript: &mut Transcript, claims: u8, advice: u8) -> u8 {
                Protocol2::<Transcript>::prove(self, transcript, claims, advice.into()).0
            }

            fn verify_layer(&self, transcript: &mut Transcript, claims: u8) -> u8 {
                Protocol2::<Transcript>::verify(self, transcript, claims.into())
            }
        }
        impl<Transcript: TProofTranscript2> GKRLayer<Transcript, u8, u8> for Mul {
            fn prove_layer(&self, transcript: &mut Transcript, claims: u8, advice: u8) -> u8 {
                Protocol2::<Transcript>::prove(self, transcript, claims.into(), advice.into()).0
            }

            fn verify_layer(&self, transcript: &mut Transcript, claims: u8) -> u8 {
                Protocol2::<Transcript>::verify(self, transcript, claims.into())
            }
        }


        #[test]
        fn api() {
            let gkr = SimpleGKR::new(
                vec![
                    Box::new(Add { p: 1 }),
                    Box::new(Add { p: 3 }),
                    Box::new(Mul { p: 2 }),
                    Box::new(Add { p: 2 }),
                    Box::new(Mul { p: 2 }),
                    Box::new(Add { p: 5 }),
                ],
            );
            let mut ptranscript = ProofTranscript2::start_prover(b"fgstglsp");
            let (final_claim, final_advice) = gkr.prove(&mut ptranscript, 0, [0u8, 1, 4, 8, 10, 20].into_iter());
            let proof = ptranscript.end();
            let mut vtranscript = ProofTranscript2::start_verifier(b"fgstglsp", proof);
            let verified_claim = gkr.verify(&mut vtranscript, 0);
            assert_eq!(final_claim, verified_claim);
        }

    }


}