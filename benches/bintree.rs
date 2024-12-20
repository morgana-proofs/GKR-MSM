use std::iter::repeat;
use std::ops::Range;
use std::sync::{Arc, OnceLock};

use ark_bls12_381::Fr;
use ark_ec::bn::TwistType::D;
use ark_std::{test_rng, UniformRand};
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use itertools::Itertools;
use liblasso::poly::dense_mlpoly::DensePolynomial;
use merlin::Transcript;

use GKR_MSM::cleanup::utils::twisted_edwards_ops::fns::{affine_twisted_edwards_add_l1, affine_twisted_edwards_add_l2, affine_twisted_edwards_add_l3, twisted_edwards_add_l1, twisted_edwards_add_l2, twisted_edwards_add_l3};
use GKR_MSM::polynomial::fragmented::{Fragment, FragmentContent, FragmentedPoly, Shape};
use GKR_MSM::protocol::bintree::{BintreeProtocol, BintreeParams, BintreeProver, Layer};
use GKR_MSM::protocol::protocol::{EvalClaim, MultiEvalClaim, PolynomialMapping, Protocol, ProtocolProver};
use GKR_MSM::protocol::sumcheck::to_multieval;
use GKR_MSM::transcript::TranscriptSender;

fn prepare_params(
    log_num_points: usize,
) -> (
    Vec<Fr>,
    Vec<FragmentedPoly<Fr>>,
    BintreeParams<Fr>,
) {
    let gen = &mut test_rng();

    let points = (0..(1 << log_num_points))
        .map(|_| ark_ed_on_bls12_381_bandersnatch::EdwardsAffine::rand(gen))
        .map(|p| (p.x, p.y))
        .unzip();

    let shape: Arc<OnceLock<Shape>> = Arc::new(Default::default());
    shape.get_or_init(|| Shape::new(vec![
        Fragment {
            mem_idx: 0,
            len: 1 << log_num_points,
            content: FragmentContent::Data,
            start: 0,
        }
    ], 0));
    let points_table_poly = vec![
        FragmentedPoly::new(points.0, vec![], shape.clone()).into(),
        FragmentedPoly::new(points.1, vec![], shape.clone()).into(),
    ];
    let point = (0..1).map(|_| Fr::rand(gen)).collect_vec();

    let f_deg2 = PolynomialMapping {
        exec: Arc::new(twisted_edwards_add_l1::<Fr>),
        degree: 2,
        num_i: 6,
        num_o: 4,
    };
    let f_deg4 = PolynomialMapping {
        exec: Arc::new(twisted_edwards_add_l2::<Fr>),
        degree: 2,
        num_i: 4,
        num_o: 4,
    };
    let f_deg8 = PolynomialMapping {
        exec: Arc::new(twisted_edwards_add_l3::<Fr>),
        degree: 2,
        num_i: 4,
        num_o: 3,
    };
    let f_deg2_init = PolynomialMapping {
        exec: Arc::new(affine_twisted_edwards_add_l1::<Fr>),
        degree: 2,
        num_i: 4,
        num_o: 3,
    };
    let f_deg4_init = PolynomialMapping {
        exec: Arc::new(affine_twisted_edwards_add_l2::<Fr>),
        degree: 2,
        num_i: 3,
        num_o: 3,
    };
    let f_deg8_init = PolynomialMapping {
        exec: Arc::new(affine_twisted_edwards_add_l3::<Fr>),
        degree: 2,
        num_i: 3,
        num_o: 3,
    };

    let num_inner_layers = log_num_points - 1;

    let layers = vec![
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
                .take(num_inner_layers - 1)
                .flatten(),
        )
        .collect_vec();

    (
        point,
        points_table_poly,
        BintreeParams::new(
            layers,
            log_num_points,
        )
    )
}
fn prepare_witness((
    point,
    points_table_poly,
    params,
): (
    Vec<Fr>,
    Vec<FragmentedPoly<Fr>>,
    &BintreeParams<Fr>,
)) -> (MultiEvalClaim<Fr>, Vec<Vec<FragmentedPoly<Fr>>>) {
    let (trace, output) = BintreeProtocol::witness(points_table_poly, &params);

    let claims_to_reduce = to_multieval(EvalClaim {
        evs: output.iter().map(|p| p.evaluate(&point)).collect(),
        point,
    });
    (claims_to_reduce, trace)
}

pub fn _bench_witness(c: &mut Criterion, log_num_points_s: Range<usize>) {
    let mut witness = c.benchmark_group("bintree/witness");
    log_num_points_s.clone()
        .map(|size| {
            witness.bench_with_input(
                BenchmarkId::from_parameter(size),
                &size,
                |b, &size| {
                    b.iter_batched(
                        || prepare_params(size),
                        |(point, tables, params)| {
                            prepare_witness((point, tables, &params))
                        },
                        BatchSize::PerIteration,
                    )
                }
            );
        }).count();
}
pub fn _bench_proof(c: &mut Criterion, log_num_points_s: Range<usize>) {
    let mut proof = c.benchmark_group("bintree/proof");
    log_num_points_s
        .map(|size| {
            proof.bench_with_input(
                BenchmarkId::from_parameter(size),
                &size,
                |b, &size| {
                    b.iter_batched(
                    || {
                        let (point, tables, params) = prepare_params(size);
                        let (claims_to_reduce, trace) = prepare_witness((point, tables, &params));
                        let p_transcript = Transcript::new(b"test");
                        (claims_to_reduce, trace, params, p_transcript)
                    },
                    |(
                            claims_to_reduce,
                            trace,
                            params,
                            mut p_transcript,
                        )| {
                            let mut prover = BintreeProver::start(claims_to_reduce, trace, &params);

                            let mut res = None;
                            while res.is_none() {
                                let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
                                res = prover.round(challenge, &mut p_transcript);
                            }
                        },
                        BatchSize::PerIteration,
                    )
                }
            );
        }).count();
}
pub fn _bench_both(c: &mut Criterion, log_num_points_s: Range<usize>) {
    let mut proof = c.benchmark_group("bintree/witness+proof");
    log_num_points_s
        .map(|size| {
            proof.bench_with_input(
                BenchmarkId::from_parameter(size),
                &size,
                |b, &size| {
                    b.iter_batched(
                        || (prepare_params(size), Transcript::new(b"test")),
                        |((point, tables, params), mut p_transcript)| {
                            let (claims_to_reduce, trace) = prepare_witness((point, tables, &params));

                            let mut prover = BintreeProver::start(claims_to_reduce, trace, &params);

                            let mut res = None;
                            while res.is_none() {
                                let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
                                res = prover.round(challenge, &mut p_transcript);
                            }
                        },
                        BatchSize::PerIteration,
                    )
                }
            );
        }).count();
}

pub fn bench_witness(c: &mut Criterion) {
    _bench_witness(c, 16..17);
}
pub fn bench_proof(c: &mut Criterion) {
    _bench_proof(c, 16..17);
}
pub fn bench_both(c: &mut Criterion) {
    _bench_both(c, 16..17);
}

criterion_group!(
    name = bintree;
    config = Criterion::default().sample_size(100).configure_from_args();
    targets = bench_witness, bench_proof, bench_both,
);
criterion_main!(bintree);

