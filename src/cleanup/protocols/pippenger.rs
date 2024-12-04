use std::iter::repeat_n;
use std::marker::PhantomData;
use ark_bls12_381::G1Affine;
use ark_ec::pairing::Pairing;
use ark_ec::twisted_edwards::{Affine, TECurveConfig};
use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
use ark_ff::{BigInteger, Field, PrimeField};
use ark_std::iterable::Iterable;
use ark_std::log2;
use itertools::Itertools;
use num_traits::{One, Zero};
use rayon::prelude::*;
use crate::cleanup::polys::vecvec::VecVecPolynomial;
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::pippenger_ending::{vecvec_domain, PippengerEnding, PippengerEndingWG};
use crate::cleanup::protocols::pushforward::pushforward::{compute_bucketing_image, PipMSMPhase1Data, PipMSMPhase2Data, PushForwardState, PushforwardFinalClaims, PushforwardProtocol};
use crate::cleanup::protocols::splits::GlueSplit;
use crate::cleanup::protocols::sumcheck::SinglePointClaims;
use crate::cleanup::protocols::verifier_polys::{EqPoly, VerifierPoly};
use crate::commitments::knuckles::{KnucklesProvingKey, KnucklesVerifyingKey};
use crate::utils::{make_gamma_pows, TwistedEdwardsConfig};

use super::opening::{KnucklesOpeningProtocol, OpeningClaim};
use super::pushforward::pushforward::{PipMSMPhase1Comm, PipMSMPhase2Comm};

pub struct PippengerWG<F: PrimeField + TwistedEdwardsConfig, Ctx: Pairing<ScalarField = F>, CC: TECurveConfig<BaseField = F>> {
    beginning: PushForwardState<F, Ctx>,
    pub ending: PippengerEndingWG<F>,
    _pd: PhantomData<CC>,
}

impl<F: PrimeField + TwistedEdwardsConfig, Ctx: Pairing<ScalarField = F>, CC: TECurveConfig<BaseField = F>> PippengerWG<F, Ctx, CC> {
    pub fn new(
        points: &[Affine<CC>],
        coeffs: &[CC::ScalarField],
        y_size: usize,
        y_logsize: usize,
        d_logsize: usize,
        x_logsize: usize,

        commitment_log_multiplicity: usize,
        commitment_key: KnucklesProvingKey<Ctx>,
    ) -> Self {
        let mut pfs = PushForwardState::new(
            points,
            coeffs,
            y_size,
            y_logsize,
            d_logsize,
            x_logsize,

            commitment_log_multiplicity,
            commitment_key,
        );
        let image = Option::take(&mut pfs.image).unwrap();

        Self {
            beginning: pfs,
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
    vkey: KnucklesVerifyingKey<Ctx>,
    commitment_log_multiplicity: usize,

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

        vkey: KnucklesVerifyingKey<Ctx>,
        commitment_log_multiplicity: usize,
    ) -> Self {

        assert!(x_logsize >= d_logsize);
        assert!(y_logsize >= commitment_log_multiplicity);

        Self {
            vkey,
            commitment_log_multiplicity,
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
    type ClaimsAfter = ();

    fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, mut state: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        
        assert!(&state.beginning.commitment_key.verifying_key() == &self.vkey);
        let num_matrix_comms = self.beginning.y_size.div_ceil(1 << self.commitment_log_multiplicity);

        let phase_1_comm = state.beginning.phase_1_comm.clone();
        let PipMSMPhase1Comm{ c, d, p_0, p_1, ac_c, ac_d } = phase_1_comm;
        assert!(c.len() == num_matrix_comms); //sanity
        assert!(d.len() == num_matrix_comms); //sanity
        
        transcript.write_points::<<Ctx as Pairing>::G1>(&c);
        transcript.write_points::<<Ctx as Pairing>::G1>(&d);
        transcript.write_points::<<Ctx as Pairing>::G1>(&[p_0]);
        transcript.write_points::<<Ctx as Pairing>::G1>(&[p_1]);
        transcript.write_points::<<Ctx as Pairing>::G1>(&[ac_c]);
        transcript.write_points::<<Ctx as Pairing>::G1>(&[ac_d]);

        let (claims, _) = self.ending.prove(transcript, claims, state.ending);
        let (claims, _) = GlueSplit::new().prove(transcript, claims, ());
        state.beginning.second_phase(&claims.point);

        let PushForwardState{phase_2_comm, ..} = &state.beginning;
        let PipMSMPhase2Comm{ c_pull, d_pull } = phase_2_comm.as_ref().unwrap().clone();
        assert!(c_pull.len() == num_matrix_comms); //sanity
        assert!(d_pull.len() == num_matrix_comms); //sanity

        transcript.write_points::<<Ctx as Pairing>::G1>(&c_pull);
        transcript.write_points::<<Ctx as Pairing>::G1>(&d_pull);

        let (claims, (phase_1_data, phase_2_data)) = self.beginning.prove(transcript, claims, (state.beginning.phase_1_data, state.beginning.phase_2_data.unwrap()));
        
        let PushforwardFinalClaims{
            gamma,
            claims_about_matrix,
            claims_ac_c,
            claims_ac_d
        } = claims;
        
        let matrix_pt = claims_about_matrix.point;
        let [p_folded_ev, c_pull_ev, d_pull_ev, c_ev, d_ev] = claims_about_matrix.evs.try_into().unwrap();
        
        let pk = state.beginning.commitment_key;

        let opener = KnucklesOpeningProtocol::new(self.vkey, Some(pk));

        let point = repeat_n(F::zero(), self.commitment_log_multiplicity).chain(matrix_pt[self.beginning.y_logsize..].iter().map(|x|*x)).collect();

        let ps_pair = opener.prove(
            transcript,
            OpeningClaim{
                commitment: (p_0 + p_1 * gamma).into(),
                point,
                ev: p_folded_ev - gamma * gamma
            },
            phase_1_data.p_0.into_par_iter().zip(phase_1_data.p_1.into_par_iter()).map(|(x, y)| x + gamma * y).collect()
        );        

        let ac_c_point = repeat_n(F::zero(), self.commitment_log_multiplicity).chain(claims_ac_c.point.iter().map(|x|*x)).collect();

        let ac_c_pair = opener.prove(
            transcript,
            OpeningClaim{
                commitment: ac_c,
                point: ac_c_point,
                ev: claims_ac_c.evs[0]
            },
            phase_1_data.ac_c
        );

        let ac_d_point = repeat_n(F::zero(), self.beginning.x_logsize + self.commitment_log_multiplicity - self.beginning.d_logsize).chain(claims_ac_d.point.iter().map(|x|*x)).collect();

        let ac_d_pair = opener.prove(
            transcript,
            OpeningClaim{
                commitment: ac_d,
                point: ac_d_point,
                ev: claims_ac_d.evs[0]
            },
            phase_1_data.ac_d
        );


        let multirow_evs = EqPoly::new(
            self.beginning.y_logsize - self.commitment_log_multiplicity,
            &matrix_pt[..self.beginning.y_logsize - self.commitment_log_multiplicity]
        ).evals();

        let c_combined : Ctx::G1 = multirow_evs.iter().zip(c.iter()).map(|(coeff, &comm)| comm * coeff).sum::<Ctx::G1>();
        let d_combined : Ctx::G1 = multirow_evs.iter().zip(d.iter()).map(|(coeff, &comm)| comm * coeff).sum::<Ctx::G1>();
        let c_pull_combined : Ctx::G1 = multirow_evs.iter().zip(c_pull.iter()).map(|(coeff, &comm)| comm * coeff).sum::<Ctx::G1>();
        let d_pull_combined : Ctx::G1 = multirow_evs.iter().zip(d_pull.iter()).map(|(coeff, &comm)| comm * coeff).sum::<Ctx::G1>();

        // evals don't change, because we are just combining pieces representing our polynomials

        let u: F = transcript.challenge(512);
        let us : [_; 4] = make_gamma_pows(u, 4).try_into().unwrap();

        let combined_matrix_commitment = c_combined + d_combined * us[1] + c_pull_combined * us[2] + d_pull_combined * us[3];
        let combined_opening_point = matrix_pt[self.beginning.y_logsize - self.commitment_log_multiplicity ..].to_vec();
        let combined_evaluation = c_ev + d_ev * us[1] + c_pull_ev * us[2] + d_pull_ev * us[3];

        let x_size = 1 << self.beginning.x_logsize;
        let y_size = self.beginning.y_size;
        let x_logsize = self.beginning.x_logsize;
        let commitment_multiplicity = 1 << self.commitment_log_multiplicity;

        let combined_witness : Vec<F> = (0 .. x_size * commitment_multiplicity).into_par_iter().map(|i| {
            let mut ret = F::zero();
            let x = i % x_size;
            let y_rem = i >> x_logsize;

            for y in 0 .. y_size {
                if y % commitment_multiplicity == y_rem {
                    let multirow_idx = y / commitment_multiplicity;
                    let idx = x + x_size * y;
                    ret += multirow_evs[multirow_idx] * (phase_1_data.c[idx] + phase_1_data.d[idx] * us[1] + phase_2_data.c_pull[idx] * us[2] + phase_2_data.d_pull[idx] * us[3]);
                }
            }

            ret
        }).collect();

        let cd_comb_pair = opener.prove(
            transcript,
            OpeningClaim{
                commitment: combined_matrix_commitment.into(),
                point: combined_opening_point,
                ev: combined_evaluation
            },
            combined_witness
        );

        ((), ())
    }

    fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let num_matrix_comms = self.beginning.y_size.div_ceil(1 << self.commitment_log_multiplicity);

        let c = transcript.read_points::<<Ctx as Pairing>::G1>(num_matrix_comms);
        let d = transcript.read_points::<<Ctx as Pairing>::G1>(num_matrix_comms);
        let p_0 = transcript.read_points::<<Ctx as Pairing>::G1>(1)[0];
        let p_1 = transcript.read_points::<<Ctx as Pairing>::G1>(1)[0];
        let ac_c = transcript.read_points::<<Ctx as Pairing>::G1>(1)[0];
        let ac_d = transcript.read_points::<<Ctx as Pairing>::G1>(1)[0];

        let claims = self.ending.verify(transcript, claims);
        let claims = GlueSplit::new().verify(transcript, claims);

        let c_pull = transcript.read_points::<<Ctx as Pairing>::G1>(num_matrix_comms);
        let d_pull = transcript.read_points::<<Ctx as Pairing>::G1>(num_matrix_comms);

        let claims = self.beginning.verify(transcript, claims);
        
        let PushforwardFinalClaims{
            gamma,
            claims_about_matrix,
            claims_ac_c,
            claims_ac_d
        } = claims;
        
        let matrix_pt = claims_about_matrix.point;
        let [p_folded_ev, c_pull_ev, d_pull_ev, c_ev, d_ev] = claims_about_matrix.evs.try_into().unwrap();
        
        let opener = KnucklesOpeningProtocol::new(self.vkey, None);

        let ps_point = repeat_n(F::zero(), self.commitment_log_multiplicity).chain(matrix_pt[self.beginning.y_logsize..].iter().map(|x|*x)).collect();

        let ps_pair = opener.verify(
            transcript,
            OpeningClaim{
                commitment: (p_0 + p_1 * gamma).into(),
                point: ps_point,
                ev: p_folded_ev - gamma * gamma
            }
        );

        let ac_c_point = repeat_n(F::zero(), self.commitment_log_multiplicity).chain(claims_ac_c.point.iter().map(|x|*x)).collect();

        let ac_c_pair = opener.verify(
            transcript,
            OpeningClaim{
                commitment: ac_c,
                point: ac_c_point,
                ev: claims_ac_c.evs[0]
            },
        );

        let ac_d_point = repeat_n(F::zero(), self.beginning.x_logsize + self.commitment_log_multiplicity - self.beginning.d_logsize).chain(claims_ac_d.point.iter().map(|x|*x)).collect();

        let ac_d_pair = opener.verify(
            transcript,
            OpeningClaim{
                commitment: ac_d,
                point: ac_d_point,
                ev: claims_ac_d.evs[0]
            },
        );

        let multirow_evs = EqPoly::new(
            self.beginning.y_logsize - self.commitment_log_multiplicity,
            &matrix_pt[..self.beginning.y_logsize - self.commitment_log_multiplicity]
        ).evals();

        let c_combined : Ctx::G1 = multirow_evs.iter().zip(c.iter()).map(|(coeff, &comm)| comm * coeff).sum::<Ctx::G1>();
        let d_combined : Ctx::G1 = multirow_evs.iter().zip(d.iter()).map(|(coeff, &comm)| comm * coeff).sum::<Ctx::G1>();
        let c_pull_combined : Ctx::G1 = multirow_evs.iter().zip(c_pull.iter()).map(|(coeff, &comm)| comm * coeff).sum::<Ctx::G1>();
        let d_pull_combined : Ctx::G1 = multirow_evs.iter().zip(d_pull.iter()).map(|(coeff, &comm)| comm * coeff).sum::<Ctx::G1>();

        // evals don't change, because we are just combining pieces representing our polynomials

        let u: F = transcript.challenge(512);
        let us : [_; 4] = make_gamma_pows(u, 4).try_into().unwrap();
        
        let combined_matrix_commitment = c_combined + d_combined * us[1] + c_pull_combined * us[2] + d_pull_combined * us[3];
        let combined_opening_point = matrix_pt[self.beginning.y_logsize - self.commitment_log_multiplicity ..].to_vec();
        let combined_evaluation = c_ev + d_ev * us[1] + c_pull_ev * us[2] + d_pull_ev * us[3];

        let cd_comb_pair = opener.verify(
            transcript,
            OpeningClaim{
                commitment: combined_matrix_commitment.into(),
                point: combined_opening_point,
                ev: combined_evaluation
            }
        );

        self.vkey.kzg_vk.verify_pair(ps_pair);
        self.vkey.kzg_vk.verify_pair(ac_c_pair);
        self.vkey.kzg_vk.verify_pair(ac_d_pair);
        self.vkey.kzg_vk.verify_pair(cd_comb_pair);
    }
}

#[cfg(test)]
mod test {
    use std::time::Instant;

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

        let d_logsize = 8;
        let num_bits = <<BandersnatchConfig as CurveConfig>::ScalarField as PrimeField>::MODULUS_BIT_SIZE as usize;
        let num_bits = 128;

        let x_logsize = 16;
        let x_size = 1 << x_logsize;
        let y_size = (num_bits + d_logsize - 1) / d_logsize;
        let y_logsize = log2(y_size) as usize;
        

        let points = (0..x_size).map(|_| Affine::<BandersnatchConfig>::rand(rng)).collect_vec();
        let coeffs = (0..x_size).map(|_| <BandersnatchConfig as CurveConfig>::ScalarField::rand(rng)).collect_vec();

        let commitment_log_multiplicity = 3;

        let comm_n_vars = commitment_log_multiplicity + x_logsize;
        let comm_size = 1 << comm_n_vars;

        let kzg_pk  = random_kzg_pk::<Ctx>(2*comm_size - 1, rng);

        let commitment_key = KnucklesProvingKey::new(kzg_pk, commitment_log_multiplicity + x_logsize, Fr::from(2));

        let vk = commitment_key.verifying_key();

        let label_start = Instant::now();

        let pippenger = Pippenger::new(
            y_size,
            y_logsize,
            d_logsize,
            x_logsize,
            vk,
            commitment_log_multiplicity,
        );


        let pip_wg = PippengerWG::new(&points,
            &coeffs,
            y_size,
            y_logsize,
            d_logsize,
            x_logsize,
            commitment_log_multiplicity,
            commitment_key
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

        let label_start_proof = Instant::now();

        let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");

        let (prover_claims, _) = pippenger.prove(&mut transcript_p, claims.clone(), pip_wg);

        let proof = transcript_p.end();

        let label_end_proof = Instant::now();

        println!("MSM params:");
        println!("log num points: {}, num bits: {}", x_logsize, num_bits);
        println!("Witness gen took: {}ms", (label_start_proof - label_start).as_millis());
        println!("Proof took: {}ms", (label_end_proof - label_start_proof).as_millis());

        let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);
        let verifier_claims = pippenger.verify(&mut transcript_v, claims);
        assert_eq!(prover_claims, verifier_claims);
    }
}