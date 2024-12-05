use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::pippenger_ending::{PippengerBucketed, PippengerEndingWG};
use crate::cleanup::protocols::pushforward::pushforward::{PushForwardState, PushforwardFinalClaims, PushforwardProtocol};
use crate::cleanup::protocols::splits::GlueSplit;
use crate::cleanup::protocols::sumcheck::{gamma_rlc, DenseSumcheckObjectSO, PointClaim, SinglePointClaims};
use crate::cleanup::protocols::verifier_polys::{EqPoly, VerifierPoly};
use crate::commitments::knuckles::{KnucklesProvingKey, KnucklesVerifyingKey};
use crate::utils::{make_gamma_pows, TwistedEdwardsConfig};
use ark_ec::pairing::Pairing;
use ark_ec::twisted_edwards::{Affine, TECurveConfig};
use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
use ark_ff::{BigInteger, Field, PrimeField};
use ark_std::iterable::Iterable;
use ark_std::log2;
use itertools::Itertools;
use num_traits::{One, Zero};
use rayon::prelude::*;
use std::iter::{repeat, repeat_n};
use std::marker::PhantomData;
use std::ops::Index;
use tracing::{event, info, info_span, instrument};
use crate::cleanup::protocols::multiopen_reduction::MultiOpenReduction;
use crate::cleanup::protocols::sumchecks::dense_eq::DenseDeg2Sumcheck;
use crate::cleanup::utils::algfn::{AlgFn, AlgFnSO};
use crate::cleanup::utils::arith::evaluate_poly;
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

        Self {
            ending: PippengerEndingWG::new(
                y_logsize,
                d_logsize,
                x_logsize,
                GlueSplit::witness(pfs.image.as_ref().unwrap()),
            ),
            beginning: pfs,
            _pd: Default::default(),
        }
    }
}

pub struct Pippenger<F: PrimeField + TwistedEdwardsConfig, Ctx: Pairing<ScalarField = F>, CC: TECurveConfig<BaseField = F>, Transcript: TProofTranscript2> {
    vkey: KnucklesVerifyingKey<Ctx>,
    commitment_log_multiplicity: usize,

    beginning: PushforwardProtocol<F>,
    ending: PippengerBucketed<F, Transcript>,
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
            ending: PippengerBucketed::new(
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

    #[instrument(skip_all)]
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

        let span = info_span!("prove image part").entered();
        let (claims, _) = self.ending.prove(transcript, claims, state.ending);
        let (claims, _) = GlueSplit::new().prove(transcript, claims, ());
        span.exit();

        let span = info_span!("commit phase 2").entered();
        state.beginning.second_phase(&claims.point);
        span.exit();

        let span = info_span!("prove pushforward").entered();
        let PushForwardState{phase_2_comm, ..} = &state.beginning;
        let PipMSMPhase2Comm{ c_pull, d_pull } = phase_2_comm.as_ref().unwrap().clone();
        assert!(c_pull.len() == num_matrix_comms); //sanity
        assert!(d_pull.len() == num_matrix_comms); //sanity

        transcript.write_points::<<Ctx as Pairing>::G1>(&c_pull);
        transcript.write_points::<<Ctx as Pairing>::G1>(&d_pull);

        let (claims, (phase_1_data, phase_2_data)) = self.beginning.prove(transcript, claims, (state.beginning.phase_1_data, state.beginning.phase_2_data.unwrap()));
        span.exit();

        let span = info_span!("open").entered();

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


        let p_folded_point: Vec<_> = repeat_n(F::zero(), self.commitment_log_multiplicity)
            .chain(matrix_pt[self.beginning.y_logsize..].iter().map(|x|*x))
            .collect();
        let ac_c_point = repeat_n(F::zero(), self.commitment_log_multiplicity)
            .chain(claims_ac_c.point.iter().map(|x|*x))
            .collect();
        let ac_d_point = repeat_n(F::zero(), self.beginning.x_logsize + self.commitment_log_multiplicity - self.beginning.d_logsize)
            .chain(claims_ac_d.point.iter().map(|x|*x))
            .collect();
        let combined_opening_point = matrix_pt[self.beginning.y_logsize - self.commitment_log_multiplicity ..].to_vec();

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

        let multiopen = MultiOpenReduction::new(
            x_logsize + self.commitment_log_multiplicity,
            4,
        );

        let mut multiopen_witness = vec![
            phase_1_data.p_0.into_par_iter().zip(phase_1_data.p_1.into_par_iter()).map(|(x, y)| x + gamma * y).collect(),
            phase_1_data.ac_c,
            phase_1_data.ac_d,
            combined_witness,
        ];

        multiopen_witness.iter_mut().for_each(|a| a.extend(itertools::repeat_n(F::zero(), (1 << (x_logsize + self.commitment_log_multiplicity)) - a.len())));

        let (multiopen_claims, _) = multiopen.prove(
            transcript,
            vec![
                PointClaim {
                    point: p_folded_point,
                    ev: p_folded_ev - gamma * gamma,
                },
                PointClaim {
                    point: ac_c_point,
                    ev: claims_ac_c.evs[0],
                },
                PointClaim {
                    point: ac_d_point,
                    ev: claims_ac_d.evs[0],
                },
                PointClaim {
                    point: combined_opening_point,
                    ev: combined_evaluation,
                },
            ],
            multiopen_witness.clone(),
        );

        let q = transcript.challenge(128);
        let qs = make_gamma_pows(q, 4);

        let folded_commitment = qs.iter().zip([
            (p_0 + p_1 * gamma).into(),
            ac_c,
            ac_d,
            combined_matrix_commitment.into(),
        ].iter()).map(|(a, b)| {
            b * a
        }).sum::<Ctx::G1>();

        let folded_witness = (0..multiopen_witness[0].len()).into_par_iter().map(|i| {
            multiopen_witness[0][i] * qs[0] +
            multiopen_witness[1][i] * qs[1] +
            multiopen_witness[2][i] * qs[2] +
            multiopen_witness[3][i] * qs[3]
        }).collect();

        let _ps_pair = opener.prove(
            transcript,
            OpeningClaim{
                commitment: folded_commitment.into(),
                point: multiopen_claims.point,
                ev: gamma_rlc(q, &multiopen_claims.evs)
            },
            folded_witness,
        );

        span.exit();

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

        let p_folded_point = repeat_n(F::zero(), self.commitment_log_multiplicity)
            .chain(matrix_pt[self.beginning.y_logsize..].iter().map(|x|*x))
            .collect();
        let ac_c_point = repeat_n(F::zero(), self.commitment_log_multiplicity)
            .chain(claims_ac_c.point.iter().map(|x|*x))
            .collect();
        let ac_d_point = repeat_n(F::zero(), self.beginning.x_logsize + self.commitment_log_multiplicity - self.beginning.d_logsize)
            .chain(claims_ac_d.point.iter().map(|x|*x))
            .collect();
        let combined_opening_point = matrix_pt[self.beginning.y_logsize - self.commitment_log_multiplicity ..].to_vec();


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
        let combined_evaluation = c_ev + d_ev * us[1] + c_pull_ev * us[2] + d_pull_ev * us[3];

        let x_logsize = self.beginning.x_logsize;

        let multiopen = MultiOpenReduction::new(
            x_logsize + self.commitment_log_multiplicity,
            4,
        );

        let multiopen_claims = multiopen.verify(
            transcript,
            vec![
                PointClaim {
                    point: p_folded_point,
                    ev: p_folded_ev - gamma * gamma,
                },
                PointClaim {
                    point: ac_c_point,
                    ev: claims_ac_c.evs[0],
                },
                PointClaim {
                    point: ac_d_point,
                    ev: claims_ac_d.evs[0],
                },
                PointClaim {
                    point: combined_opening_point,
                    ev: combined_evaluation,
                },
            ],
        );

        let q = transcript.challenge(128);
        let qs = make_gamma_pows(q, 4);

        let folded_commitment = qs.iter().zip([
            (p_0 + p_1 * gamma).into(),
            ac_c,
            ac_d,
            combined_matrix_commitment.into(),
        ].iter()).map(|(a, b)| {
            b * a
        }).sum::<Ctx::G1>();

        let ps_pair = opener.verify(
            transcript,
            OpeningClaim{
                commitment: folded_commitment.into(),
                point: multiopen_claims.point,
                ev: gamma_rlc(q, &multiopen_claims.evs)
            },
        );

        self.vkey.kzg_vk.verify_pair(ps_pair);
    }
}

pub mod benchutils {
    use super::*;
    use crate::cleanup::protocol2::Protocol2;
    use crate::cleanup::protocols::gkrs::triangle_add;
    use crate::cleanup::protocols::pippenger::{Pippenger, PippengerWG};
    use crate::cleanup::protocols::splits::SplitIdx;
    use crate::cleanup::protocols::sumcheck::SinglePointClaims;
    use crate::cleanup::utils::arith::evaluate_poly;
    use crate::commitments::knuckles::KnucklesProvingKey;
    use crate::commitments::kzg::random_kzg_pk;
    use ark_bls12_381::Fr;
    use ark_bls12_381::{Bls12_381 as Ctx, Bls12_381};
    use ark_ec::pairing::Pairing;
    use ark_ec::twisted_edwards::{Affine, Projective};
    use ark_ec::{CurveConfig, Group};
    use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
    use ark_std::{log2, UniformRand};
    use itertools::Itertools;
    use rand::Rng;
    use std::fmt::Display;
    use ark_ff::{BigInt, BigInteger256};
    use num_traits::Pow;
    use tracing::{instrument, span, Level};
    use crate::cleanup::polys::common::Densify;
    use crate::utils::build_points;

    #[derive(Clone)]
    pub struct PippengerConfig {
        pub y_size: usize,
        pub y_logsize: usize,
        pub d_logsize: usize,
        pub x_logsize: usize,
        pub commitment_log_multiplicity: usize,
    }

    #[derive(Clone)]
    pub struct PippengerData {
        pub points: Vec<Affine<BandersnatchConfig>>,
        pub coefs: Vec<<BandersnatchConfig as CurveConfig>::ScalarField>,
        pub config: PippengerConfig,
        pub r: Vec<<BandersnatchConfig as CurveConfig>::BaseField>,

        pub commitment_key: KnucklesProvingKey<Ctx>,
        pub vkey: KnucklesVerifyingKey<Bls12_381>,
    }

    pub struct PippengerOutput {
        pub(crate) output: Vec<Vec<<BandersnatchConfig as CurveConfig>::BaseField>>,
        claims: SinglePointClaims<<BandersnatchConfig as CurveConfig>::BaseField>,
        pub vkey: KnucklesVerifyingKey<Bls12_381>,
    }

    #[instrument(skip_all)]
    pub fn build_pippenger_data<RNG: Rng>(rng: &mut RNG, d_logsize: usize, x_logsize: usize, num_bits: usize, commitment_log_multiplicity: usize) -> PippengerData {
        let points = (0..(1 << x_logsize)).map(|_| Affine::<BandersnatchConfig>::rand(rng)).collect_vec();
        let coefs = (0..(1 << x_logsize)).map(|_| <BandersnatchConfig as CurveConfig>::ScalarField::from_le_bytes_mod_order(
            &BigInteger256::rand(rng).to_bytes_le()[..num_bits / 8]
        )).collect_vec();

        let size_x = points.len();
        let y_size = (num_bits + d_logsize - 1) / d_logsize;
        let x_logsize = log2(size_x) as usize;
        let y_logsize = log2(y_size) as usize;

        let r = (0..y_logsize).map(|_| <BandersnatchConfig as CurveConfig>::BaseField::rand(rng)).collect_vec();

        let comm_n_vars = commitment_log_multiplicity + x_logsize;
        let comm_size = 1 << comm_n_vars;

        let kzg_pk  = random_kzg_pk(2*comm_size - 1, rng);

        let commitment_key = KnucklesProvingKey::new(kzg_pk, commitment_log_multiplicity + x_logsize, Fr::from(2));


        PippengerData {
            points,
            coefs,
            config: PippengerConfig {
                y_size,
                y_logsize,
                d_logsize,
                x_logsize,
                commitment_log_multiplicity,
            },
            r,
            vkey: commitment_key.verifying_key(),
            commitment_key,
        }
    }

    #[instrument(skip_all)]
    pub fn run_pippenger(p_transcript: &mut impl TProofTranscript2, data: PippengerData) -> PippengerOutput {
        let PippengerData {
            points,
            coefs,
            config: PippengerConfig {
                y_size,
                y_logsize,
                d_logsize,
                x_logsize,
                commitment_log_multiplicity,
            },
            r,
            vkey,
            commitment_key,
        } = data;

        let expected_msm = BandersnatchConfig::msm(&points, &coefs).unwrap();

        let span = info_span!("compute buckets and commit phase 1").entered();
        let pip_wg = PippengerWG::<<BandersnatchConfig as CurveConfig>::BaseField, Ctx, BandersnatchConfig>::new(
            &points,
            &coefs,
            y_size,
            y_logsize,
            d_logsize,
            x_logsize,

            commitment_log_multiplicity,
            commitment_key,
        );
        let claim_span = info_span!("claim computation").entered();
        let dense_output: Vec<Vec<_>> = triangle_add::builder::witness::last_step(
            pip_wg.ending.last().unwrap(),
            y_logsize + d_logsize - 2 - SplitIdx::HI(y_logsize).hi_usize(y_logsize + d_logsize - 2)
        );

        let claims = SinglePointClaims {
            evs: dense_output.iter().map(|output| evaluate_poly(output, &r)).collect(),
            point: r.clone(),
        };
        claim_span.exit();
        span.exit();

        let pippenger = Pippenger::new(
            y_size,
            y_logsize,
            d_logsize,
            x_logsize,
            vkey,
            commitment_log_multiplicity,
        );


        pippenger.prove(p_transcript, claims.clone(), pip_wg);
        PippengerOutput {
            output: dense_output,
            claims,
            vkey,
        }
    }

    #[instrument(skip_all)]
    pub fn verify_pippenger(transcript: &mut impl TProofTranscript2, config: PippengerConfig, output: PippengerOutput, expected_output: Option<Projective<BandersnatchConfig>>) -> () {
        let PippengerConfig {
            y_size,
            y_logsize,
            d_logsize,
            x_logsize,
            commitment_log_multiplicity,
        } = config;
        let PippengerOutput {
            output: results,
            claims,
            vkey,
        } = output;

        let pippenger = Pippenger::<Fr, Bls12_381, BandersnatchConfig, _>::new(
            y_size,
            y_logsize,
            d_logsize,
            x_logsize,

            vkey,
            commitment_log_multiplicity
        );

        pippenger.verify(transcript, claims);

        assert!((d_logsize + 1) * 3 == results.len());

        let results_points = build_points(&results);
        let mut transposed_points = vec![];
        for idx in 0..results_points[0].len() {
            for i in 1..results_points.len() {
                transposed_points.push(results_points[i][idx])
            }
        }

        let mut acc = Projective::<BandersnatchConfig>::zero();
        for i in (0..transposed_points.len()).rev() {
            acc = acc.double();
            acc += &transposed_points[i];
        }
        if let Some(expected_output) = expected_output {
            assert_eq!(acc, expected_output);
        }
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;
    use ark_ec::Group;
    use ark_ec::twisted_edwards::Projective;
    use super::*;
    use crate::cleanup::proof_transcript::ProofTranscript2;
    use ark_std::test_rng;

    use crate::cleanup::protocols::pippenger::benchutils::{build_pippenger_data, run_pippenger, verify_pippenger};
    use crate::utils::{build_points, prettify_coords, prettify_points};

    #[test]
    fn test_pippenger() {
        let rng = &mut test_rng();

        let d_logsize = 6;
        let num_bits = 128;
        let x_logsize = 10;
        let commitment_log_multiplicity = 0;

        let rng = &mut test_rng();
        let data = build_pippenger_data(rng, d_logsize, x_logsize, num_bits, commitment_log_multiplicity);
        let config = data.config.clone();

        let expected_msm = BandersnatchConfig::msm(&data.points, &data.coefs).unwrap();

        let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");
        transcript_p.record_current_time("Start");
        let output = run_pippenger(&mut transcript_p, data);
        let time_records = transcript_p.time_records();
        let proof = transcript_p.end();

        let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);
        verify_pippenger(&mut transcript_v, config, output, Some(expected_msm));
        transcript_v.end();
    }
}