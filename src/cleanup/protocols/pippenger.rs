use std::marker::PhantomData;
use ark_ec::pairing::Pairing;
use ark_ec::twisted_edwards::{Affine, TECurveConfig};
use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
use ark_ff::{BigInteger, Field, PrimeField};
use ark_std::iterable::Iterable;
use ark_std::log2;
use itertools::Itertools;
use num_traits::{One, Zero};
use crate::cleanup::polys::vecvec::VecVecPolynomial;
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::pippenger_ending::{vecvec_domain, PippengerEnding, PippengerEndingWG};
use crate::cleanup::protocols::pushforward::pushforward::{compute_bucketing_image, PipMSMPhase1Data, PipMSMPhase2Data, PushForwardAdvice, PushforwardProtocol};
use crate::cleanup::protocols::splits::GlueSplit;
use crate::cleanup::protocols::sumcheck::SinglePointClaims;
use crate::cleanup::protocols::verifier_polys::EqPoly;
use crate::commitments::knuckles::KnucklesProvingKey;
use crate::utils::TwistedEdwardsConfig;

pub struct PippengerWG<F: PrimeField + TwistedEdwardsConfig, Ctx: Pairing<ScalarField = F>, CC: TECurveConfig<BaseField = F>> {
    beginning: PushForwardAdvice<F, Ctx>,
    pub ending: PippengerEndingWG<F>,
    _pd: PhantomData<CC>,
}

impl<F: PrimeField + TwistedEdwardsConfig, Ctx: Pairing<ScalarField = F>, CC: TECurveConfig<BaseField = F>> PippengerWG<F, Ctx, CC> {
    pub fn new(
        points: &[Affine<CC>],
        coefs: &[CC::ScalarField],
        y_size: usize,
        y_logsize: usize,
        d_logsize: usize,
        x_logsize: usize,

        commitment_log_multiplicity: usize,
        commitment_key: KnucklesProvingKey<Ctx>,
    ) -> Self {
        let mut pfa = PushForwardAdvice::new(
            points,
            coefs,
            y_size,
            y_logsize,
            d_logsize,
            x_logsize,

            commitment_log_multiplicity,
            commitment_key,
        );
        let image = Option::take(&mut pfa.image).unwrap();

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

pub struct Pippenger<F: PrimeField + TwistedEdwardsConfig, Ctx: Pairing<ScalarField = F>, CC: TECurveConfig<BaseField = F>, Transcript: TProofTranscript2> {
    beginning: PushforwardProtocol<F>,
    ending: PippengerEnding<F, Transcript>,
    _pd: PhantomData<(F, Ctx, CC)>,
}

impl<F: PrimeField + TwistedEdwardsConfig, Ctx: Pairing<ScalarField = F>, CC: TECurveConfig<BaseField = F>, Transcript: TProofTranscript2> Pippenger<F, Ctx, CC, Transcript> {
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

impl<F: PrimeField + TwistedEdwardsConfig, Ctx: Pairing<ScalarField = F>, CC: TECurveConfig<BaseField = F>, Transcript: TProofTranscript2> Protocol2<Transcript> for Pippenger<F, Ctx, CC, Transcript> {
    type ProverInput = PippengerWG<F, Ctx, CC>;
    type ProverOutput = ();
    type ClaimsBefore = SinglePointClaims<CC::BaseField>;
    type ClaimsAfter = SinglePointClaims<CC::BaseField>;

    fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, mut advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let (claims, _) = self.ending.prove(transcript, claims, advice.ending);
        let (claims, _) = GlueSplit::new().prove(transcript, claims, ());
        advice.beginning.second_phase(&claims.point);
        let (claims, _) = self.beginning.prove(transcript, claims, (advice.beginning.phase_1_data, advice.beginning.phase_2_data.unwrap()));
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
    use crate::commitments::kzg::random_kzg_pk;
    use super::*;

    use ark_bls12_381::Bls12_381 as Ctx;
    use ark_bls12_381::Fr;


    #[test]
    fn test_pippenger() {
        let rng = &mut test_rng();

        let points = (0..(1 << 10)).map(|_| Affine::<BandersnatchConfig>::rand(rng)).collect_vec();
        let coefs = (0..(1 << 10)).map(|_| <BandersnatchConfig as CurveConfig>::ScalarField::rand(rng)).collect_vec();

        let d_logsize = 8;
        let num_bits = <<BandersnatchConfig as CurveConfig>::ScalarField as PrimeField>::BigInt::NUM_LIMBS * 8;
        let x_size = points.len();
        let y_size = (num_bits + d_logsize - 1) / d_logsize;
        let x_logsize = log2(x_size) as usize;
        let y_logsize = log2(y_size) as usize;

        let commitment_log_multiplicity = 3;

        let comm_n_vars = commitment_log_multiplicity + x_logsize;
        let comm_size = 1 << comm_n_vars;

        let kzg_pk  = random_kzg_pk(2*comm_size - 1, rng);

        let commitment_key = KnucklesProvingKey::new(kzg_pk, commitment_log_multiplicity + x_logsize, Fr::from(2));

        let pip_wg = PippengerWG::<Fr, Ctx, BandersnatchConfig>::new(
            &points,
            &coefs,
            y_size,
            y_logsize,
            d_logsize,
            x_logsize,

            commitment_log_multiplicity,
            commitment_key,
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