use std::{fs::File, sync::Arc};
use std::iter::repeat;

use ark_ec::{CurveGroup};
use ark_ff::PrimeField;
use itertools::Itertools;
use liblasso::utils::math::Math;
#[cfg(feature = "prof")]
use profi::{prof, prof_guard};
use rayon::iter::{IntoParallelIterator, IntoParallelRefIterator, ParallelIterator, repeatn};

use crate::{
    binary_msm::{binary_msm, prepare_coefs},
    grand_add::{
        affine_twisted_edwards_add_l1, affine_twisted_edwards_add_l2,
        affine_twisted_edwards_add_l3, twisted_edwards_add_l1, twisted_edwards_add_l2,
        twisted_edwards_add_l3,
    },
    protocol::protocol::{PolynomialMapping, Protocol},
    transcript::{TranscriptReceiver, TranscriptSender},
    utils::TwistedEdwardsConfig,
};
use crate::poly::{NestedPoly, NestedPolynomial};
use crate::protocol::bintree::{Bintree, BintreeParams, BintreeProof, BintreeProver, Layer};
use crate::protocol::protocol::{EvalClaim, ProtocolProver};
use crate::protocol::sumcheck::to_multieval;
#[cfg(feature = "memprof")]
use crate::utils::memprof;

pub trait MSMCircuitConfig {
    type F: PrimeField;
    type Comm: CurveGroup<ScalarField = Self::F>;
    type G: CurveGroup<Config: TwistedEdwardsConfig>;
}

pub struct CommitmentKey<G: CurveGroup> {
    pub bases: Option<Vec<G::Affine>>,
    pub binary_extended_bases: Option<Vec<Vec<G::Affine>>>,
    pub gamma: usize,
}

impl<G: CurveGroup> CommitmentKey<G> {
    pub fn new() -> Self {
        Self {
            bases: None,
            binary_extended_bases: None,
            gamma: 0,
        }
    }

    pub fn load(file: &mut File) -> Self {
        todo!()
    }

    pub fn dump(&self, file: &mut File) {
        todo!()
    }

    pub fn commit_vec(&self, v: &[G::ScalarField]) -> G {
        G::msm(self.bases.as_ref().unwrap(), v).unwrap()
        // G::zero()
    }

    pub fn commit_bitvec(&self, v: impl Iterator<Item = bool>) -> G {
        binary_msm(
            &prepare_coefs(v, self.gamma),
            self.binary_extended_bases.as_ref().unwrap(),
        )
        // G::zero()
    }
}

pub struct MSMProof<G: CurveGroup> {
    bit_columns: Vec<G>,
    point_column: G,
    gkr_proof: BintreeProof<G::ScalarField>,
    output: Vec<G::ScalarField>,
}

// This function takes a bit and a point, parsed as b, p.x, p.y, and returns b ? p : zero_point

fn pt_bit_choice<F: PrimeField>(args: &[F]) -> Vec<F> {
    vec![args[0] * args[1], args[0] * (args[2] - F::one()) + F::one()]
}

pub fn gkr_msm_prove<
    F: PrimeField + TwistedEdwardsConfig,
    T: TranscriptReceiver<F> + TranscriptSender<F>,
    G: CurveGroup<ScalarField = F>,
>(
    scalars: Vec<Vec<bool>>,
    points: Vec<(F, F)>,
    log_num_points: usize,
    log_num_scalar_bits: usize,
    log_num_bit_columns: usize, // Logamount of columns that host the bitvector. Normally ~5-6 should be reasonable.
    ck: &CommitmentKey<G>,
    transcript: &mut T,
) -> (EvalClaim<F>, MSMProof<G>) {
    #[cfg(feature = "prof")]
    let mut guard = prof_guard!("gkr_msm_prove[bit_prep]");

    #[cfg(feature = "memprof")]
    memprof(&"gkr_msm_prove start");

    let num_points = 1 << log_num_points;
    let num_scalar_bits = 1 << log_num_scalar_bits;
    let num_vars = log_num_points + log_num_scalar_bits;
    let size = 1 << num_vars;
    let num_bit_columns = 1 << log_num_bit_columns;

    assert!(points.len() == num_points);
    assert!(scalars.len() == num_points);

    scalars
        .iter()
        .map(|s| assert!(s.len() == num_scalar_bits))
        .count();

    // COMMIT TO OUR STUFF AND ADD IT TO TRANSCRIPT
    let bits_flatten: Vec<_> = scalars.into_par_iter().flatten().collect();

    let col_size = size >> log_num_bit_columns;

    let bit_comms: Vec<G> = (0..num_bit_columns)
        .map(|i| {
            let point = ck.commit_bitvec(
                bits_flatten[col_size * i..col_size * (i + 1)]
                    .iter()
                    .map(|x| *x),
            );
            transcript.append_point::<G>(b"bit column", point);
            point
        })
        .collect();

    assert!(
        col_size >= 2 * points.len(),
        "Points should fit in a single column. Please reduce the amount of columns."
    );

    let (mut pts_prep, tmp): (Vec<_>, Vec<_>) = points.iter().map(|x| *x).unzip();
    pts_prep.extend(
        tmp.into_iter()
            .chain(repeat(F::zero()).take(col_size - num_points * 2)),
    );

    let pts_comm: G = ck.commit_vec(&pts_prep);
    transcript.append_point::<G>(b"point column", pts_comm);

    let bits_poly = NestedPolynomial::from_values(
        bits_flatten
            .par_iter()
            .map(|x| F::from(*x as u64))
            .collect(),
        bits_flatten.len().log_2(),
        F::zero(),
    );

    let _points_table_poly: (Vec<_>, Vec<_>) = points
        .par_iter()
        .map(|p| repeatn(*p, num_scalar_bits))
        .flatten()
        .unzip();

    
    let tmp = _points_table_poly.0.len().log_2();
    let points_table_poly = (
        NestedPolynomial::from_values(
            _points_table_poly.0,
            tmp,
            F::zero(),
        ),
        NestedPolynomial::from_values(
            _points_table_poly.1,
            tmp,
            F::zero(),
        ),
    );

    // layer0
    // bits_poly
    // points_table_poly

    let base_layer = vec![bits_poly, points_table_poly.0, points_table_poly.1];

    #[cfg(feature = "prof")]
    drop(guard);

    #[cfg(feature = "prof")]
    (guard = prof_guard!("gkr_msm_prove[gkr_wtns]"));


    #[cfg(feature = "memprof")]
    memprof(&"gkr_msm_prove before wtns");
    // layer1
    // filtered pts

    let f_base = PolynomialMapping {
        exec: Arc::new(pt_bit_choice),
        degree: 2,
        num_i: 3,
        num_o: 2,
    };

    // Now, we will compute GKR witness.

    let f_deg2 = PolynomialMapping {
        exec: Arc::new(twisted_edwards_add_l1::<F>),
        degree: 2,
        num_i: 6,
        num_o: 4,
    };
    let f_deg4 = PolynomialMapping {
        exec: Arc::new(twisted_edwards_add_l2::<F>),
        degree: 2,
        num_i: 4,
        num_o: 4,
    };
    let f_deg8 = PolynomialMapping {
        exec: Arc::new(twisted_edwards_add_l3::<F>),
        degree: 2,
        num_i: 4,
        num_o: 3,
    };
    let f_deg2_init = PolynomialMapping {
        exec: Arc::new(affine_twisted_edwards_add_l1::<F>),
        degree: 2,
        num_i: 4,
        num_o: 3,
    };
    let f_deg4_init = PolynomialMapping {
        exec: Arc::new(affine_twisted_edwards_add_l2::<F>),
        degree: 2,
        num_i: 3,
        num_o: 3,
    };
    let f_deg8_init = PolynomialMapping {
        exec: Arc::new(affine_twisted_edwards_add_l3::<F>),
        degree: 2,
        num_i: 3,
        num_o: 3,
    };

    let num_inner_layers = log_num_points - 1;

    let layers = vec![
        Layer::Mapping(f_base),
        Layer::new_split(2),
        Layer::Mapping(f_deg2_init),
        Layer::Mapping(f_deg4_init),
        Layer::Mapping(f_deg8_init),
    ]
    .into_iter()
    .chain(
        repeat(
            vec![
                Layer::new_split(3),
                Layer::Mapping(f_deg2.clone()),
                Layer::Mapping(f_deg4.clone()),
                Layer::Mapping(f_deg8.clone()),
            ]
            .into_iter(),
        )
        .take(num_inner_layers)
        .flatten(),
    )
    .collect_vec();

    let params = BintreeParams::new(layers, num_vars);

    let (trace, output) = Bintree::witness(base_layer, &params);

    #[cfg(feature = "prof")]
    drop(guard);
    #[cfg(feature = "prof")]
    (guard = prof_guard!("gkr_msm_prove[gkr_claims]"));

    #[cfg(feature = "memprof")]
    memprof(&"gkr_msm_prove after wtns");

    output
        .iter()
        .map(|p| transcript.append_scalars(b"output", &p.vec()))
        .count();
    output
        .iter()
        .map(|p| assert_eq!(p.num_vars(), log_num_scalar_bits))
        .count();

    let claim_point = (0..log_num_scalar_bits)
        .map(|_| transcript.challenge_scalar(b"output_claim_point").value)
        .collect_vec();

    let claim_evals = output
        .iter()
        .map(|p| p.evaluate(&claim_point))
        .collect_vec();

    let claim = to_multieval(EvalClaim {
        point: claim_point,
        evs: claim_evals,
    });

    #[cfg(feature = "prof")]
    drop(guard);
    #[cfg(feature = "prof")]
    (guard = prof_guard!("gkr_msm_prove[gkr_prover]"));

    let mut prover = BintreeProver::start(claim, trace, &params);

    let mut res = None;
    while res.is_none() {
        let challenge = transcript.challenge_scalar(b"challenge_nextround");
        res = prover.round(challenge, transcript);
    }

    let (gkr_evals, gkr_proof) = res.unwrap();


    #[cfg(feature = "memprof")]
    crate::utils::memprof(&"gkr_msm_prove after proof");

    (
        gkr_evals,
        MSMProof {
            bit_columns: bit_comms,
            point_column: pts_comm,
            gkr_proof,
            output: output
                .into_iter()
                .map(|p| p.vec().iter().map(|x| *x).collect_vec())
                .flatten()
                .collect_vec(),
        }
    )
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{G1Affine, G1Projective};
    use ark_std::{test_rng, UniformRand};
    use ark_std::rand::Rng;
    use merlin::Transcript;

    #[cfg(feature = "memprof")]
    use jemalloc_ctl::{epoch, stats};

    use crate::binary_msm::prepare_bases;
    #[cfg(feature = "memprof")]
    use crate::utils::memprof;

    use super::*;

    #[cfg(feature = "memprof")]
    #[global_allocator]
    static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

    #[test]
    fn small() {
        let gamma = 5;
        let log_num_points = 5;
        let log_num_scalar_bits = 8;
        let log_num_bit_columns = 6;

        let num_points = 1 << log_num_points;
        let num_scalar_bits = 1 << log_num_scalar_bits;
        let num_vars = log_num_points + log_num_scalar_bits;
        let size = 1 << num_vars;
        let num_bit_columns = 1 << log_num_bit_columns;
        let col_size = size >> log_num_bit_columns;

        dbg!(
            gamma,
            log_num_points,
            log_num_scalar_bits,
            log_num_bit_columns,
            num_points,
            num_scalar_bits,
            num_vars,
            size,
            num_bit_columns,
            col_size
        );
        let gen = &mut test_rng();
        let bases = (0..col_size).map(|_| G1Affine::rand(gen)).collect_vec();
        let coefs = (0..num_points)
            .map(|_| (0..256).map(|_| gen.gen_bool(0.5)).collect_vec())
            .collect_vec();
        let points = (0..num_points)
            .map(|_| ark_ed_on_bls12_381_bandersnatch::EdwardsAffine::rand(gen))
            .map(|p| (p.x, p.y))
            .collect_vec();
        let binary_extended_bases = prepare_bases::<_, G1Projective>(&bases, gamma);

        let comm_key = CommitmentKey::<G1Projective> {
            bases: Some(bases),
            binary_extended_bases: Some(binary_extended_bases),
            gamma,
        };

        let mut p_transcript = Transcript::new(b"test");

        gkr_msm_prove(
            coefs,
            points,
            log_num_points,
            log_num_scalar_bits,
            log_num_bit_columns,
            &comm_key,
            &mut p_transcript,
        );
    }
}
