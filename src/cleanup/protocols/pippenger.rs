use std::marker::PhantomData;
use ark_ec::twisted_edwards::{Affine, TECurveConfig};
use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
use ark_ff::{BigInteger, Field, PrimeField};
use ark_std::iterable::Iterable;
use ark_std::log2;
use itertools::Itertools;
use num_traits::{One, Zero};
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::pippenger_ending::{vecvec_domain, PippengerEnding, PippengerEndingWG};
use crate::cleanup::protocols::pushforward::pushforward::{compute_bucketing_image, PipMSMPhase1Data, PipMSMPhase2Data, PushForwardAdvice, PushforwardProtocol};
use crate::cleanup::protocols::splits::GlueSplit;
use crate::cleanup::protocols::sumcheck::SinglePointClaims;
use crate::cleanup::protocols::verifier_polys::EqPoly;
use crate::utils::TwistedEdwardsConfig;

pub struct PippengerWG<CC: TECurveConfig> where CC::BaseField: PrimeField + TwistedEdwardsConfig {
    beginning: PushForwardAdvice<CC::BaseField>,
    ending: PippengerEndingWG<CC::BaseField>,
    _pd: PhantomData<CC>,
}

impl<CC: TECurveConfig> PippengerWG<CC> where CC::BaseField: PrimeField + TwistedEdwardsConfig {
    pub fn new(
        points: &[Affine<CC>],
        coefs: &[CC::ScalarField],
        y_size: usize,
        y_logsize: usize,
        d_logsize: usize,
        x_logsize: usize,
    ) -> Self {
        let size_y = y_size;
        let mut pfa = PushForwardAdvice::new(
            points,
            coefs,
            size_y,
            y_logsize,
            d_logsize,
            x_logsize,
        );
        let image = pfa.image.take().unwrap();

        Self {
            beginning: pfa,
            ending: PippengerEndingWG::new(
                y_logsize,
                d_logsize,
                x_logsize,
                GlueSplit::witness(&image),
            ),
            _pd: Default::default(),
        }
    }
}

pub struct Pippenger<CC: TECurveConfig, Transcript: TProofTranscript2> where CC::BaseField: PrimeField + TwistedEdwardsConfig {
    beginning: PushforwardProtocol<CC::BaseField>,
    ending: PippengerEnding<CC::BaseField, Transcript>,
    _pd: PhantomData<CC>,
}

impl<CC: TECurveConfig, Transcript: TProofTranscript2> Pippenger<CC, Transcript> where CC::BaseField: PrimeField + TwistedEdwardsConfig {
    pub fn new(
        y_size: usize,
        y_logsize: usize,
        d_logsize: usize,
        x_logsize: usize,
    ) -> Self {
        Self {
            beginning: PushforwardProtocol::new(
                x_logsize,
                y_logsize,
                y_size,
                d_logsize,
            ),
            ending: PippengerEnding::new(
                y_logsize,
                d_logsize,
                x_logsize,
            ),
            _pd: Default::default(),
        }
    }
}

impl<CC: TECurveConfig, Transcript: TProofTranscript2> Protocol2<Transcript> for Pippenger<CC, Transcript> where CC::BaseField: PrimeField + TwistedEdwardsConfig {
    type ProverInput = PippengerWG<CC>;
    type ProverOutput = ();
    type ClaimsBefore = SinglePointClaims<CC::BaseField>;
    type ClaimsAfter = SinglePointClaims<CC::BaseField>;

    fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, mut advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let (claims, _) = self.ending.prove(transcript, claims, advice.ending);
        let (claims, _) = GlueSplit::new().prove(transcript, claims, ());
        advice.beginning.bind(&claims.point);
        let (claims, _) = self.beginning.prove(transcript, claims, (advice.beginning.p1, advice.beginning.p2.unwrap()));
        (claims, ())
    }

    fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let claims = self.ending.verify(transcript, claims);
        let claims = GlueSplit::new().verify(transcript, claims);
        self.beginning.verify(transcript, claims)
    }
}

#[cfg(test)]
mod test {
    use ark_ec::CurveConfig;
    use ark_std::{test_rng, UniformRand};
    use crate::cleanup::proof_transcript::ProofTranscript2;
    use crate::cleanup::protocols::gkrs::triangle_add;
    use crate::cleanup::protocols::splits::SplitIdx;
    use crate::cleanup::utils::arith::evaluate_poly;
    use super::*;

    #[test]
    fn test_pippenger() {
        let rng = &mut test_rng();

        let points = (0..(1 << 10)).map(|_| Affine::<BandersnatchConfig>::rand(rng)).collect_vec();
        let coefs = (0..(1 << 10)).map(|_| <BandersnatchConfig as CurveConfig>::ScalarField::rand(rng)).collect_vec();

        let d_logsize = 8;
        let num_bits = <<BandersnatchConfig as CurveConfig>::ScalarField as PrimeField>::BigInt::NUM_LIMBS * 8;
        let size_x = points.len();
        let y_size = (num_bits + d_logsize - 1) / d_logsize;
        let x_logsize = log2(size_x) as usize;
        let y_logsize = log2(y_size) as usize;

        let pip_wg = PippengerWG::<BandersnatchConfig>::new(
            &points,
            &coefs,
            y_size,
            y_logsize,
            d_logsize,
            x_logsize,
        );

        let pippenger = Pippenger::new(
            y_size,
            y_logsize,
            d_logsize,
            x_logsize,
        );


        let point = (0..y_logsize).map(|_| <BandersnatchConfig as CurveConfig>::BaseField::rand(rng)).collect_vec();
        let dense_output: Vec<Vec<_>> = triangle_add::builder::witness::last_step(
            pip_wg.ending.advices.last().unwrap().into(),
            y_logsize + d_logsize - 2 - SplitIdx::HI(y_logsize).hi_usize(y_logsize + d_logsize - 2)
        );

        let claims = SinglePointClaims {
            point: point.clone(),
            evs: dense_output.iter().map(|output| evaluate_poly(output, &point)).collect(),
        };

        let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");

        let (prover_claims, _) = pippenger.prove(&mut transcript_p, claims.clone(), pip_wg);

        let proof = transcript_p.end();
        let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);
        let verifier_claims = pippenger.verify(&mut transcript_v, claims);
        assert_eq!(prover_claims, verifier_claims);
    }
}