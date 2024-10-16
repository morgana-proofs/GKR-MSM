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

use GKR_MSM::cleanup::utils::twisted_edwards_ops::{affine_twisted_edwards_add_l1, affine_twisted_edwards_add_l2, affine_twisted_edwards_add_l3, twisted_edwards_add_l1, twisted_edwards_add_l2, twisted_edwards_add_l3};
use GKR_MSM::polynomial::fragmented::{Fragment, FragmentContent, FragmentedPoly, Shape};
use GKR_MSM::protocol::bintree::{BintreeProtocol, BintreeParams, BintreeProver, Layer};
use GKR_MSM::protocol::protocol::{EvalClaim, MultiEvalClaim, PolynomialMapping, Protocol, ProtocolProver};
use GKR_MSM::protocol::sumcheck::{LameSumcheckPolyMap, LameSumcheckPolyMapProver, SumcheckPolyMap, SumcheckPolyMapParams, SumcheckPolyMapProof, SumcheckPolyMapProver, to_multieval};
use GKR_MSM::transcript::TranscriptSender;

fn prepare_params(
    num_vars: usize,
) -> (
    Vec<Fr>,
    Vec<FragmentedPoly<Fr>>,
    SumcheckPolyMapParams<Fr>,
) {
    let gen = &mut test_rng();

    let points = (0..(1 << num_vars))
        .map(|_| ark_ed_on_bls12_381_bandersnatch::EdwardsAffine::rand(gen))
        .map(|p| (p.x, p.y))
        .unzip();

    let points2 = (0..(1 << num_vars))
        .map(|_| ark_ed_on_bls12_381_bandersnatch::EdwardsAffine::rand(gen))
        .map(|p| (p.x, p.y))
        .unzip();

    let shape = Shape::full(1 << num_vars);
    let points_table_poly = vec![
        FragmentedPoly::new(points.0, vec![], shape.clone()).into(),
        FragmentedPoly::new(points.1, vec![], shape.clone()).into(),
        FragmentedPoly::new(points2.0, vec![], shape.clone()).into(),
        FragmentedPoly::new(points2.1, vec![], shape.clone()).into(),
    ];
    let point = (0..num_vars).map(|_| Fr::rand(gen)).collect_vec();

    let f_deg2_init = PolynomialMapping {
        exec: Arc::new(affine_twisted_edwards_add_l1::<Fr>),
        degree: 2,
        num_i: 4,
        num_o: 3,
    };

    (
        point,
        points_table_poly,
        SumcheckPolyMapParams {
            f: f_deg2_init,
            num_vars,
        },
    )
}
fn new_prepare_witness((
    point,
    points_table_poly,
    params,
): (
    Vec<Fr>,
    Vec<FragmentedPoly<Fr>>,
    &SumcheckPolyMapParams<Fr>,
)) -> (MultiEvalClaim<Fr>, Vec<Vec<FragmentedPoly<Fr>>>) {
    let (trace, output) = SumcheckPolyMap::witness(points_table_poly, &params);

    let claims_to_reduce = to_multieval(EvalClaim {
        evs: output.iter().map(|p| p.evaluate(&point)).collect(),
        point,
    });
    (claims_to_reduce, trace)
}

fn old_prepare_witness((
                       point,
                       points_table_poly,
                       params,
                   ): (
    Vec<Fr>,
    Vec<FragmentedPoly<Fr>>,
    &SumcheckPolyMapParams<Fr>,
)) -> (MultiEvalClaim<Fr>, Vec<Vec<FragmentedPoly<Fr>>>) {
    let (trace, output) = LameSumcheckPolyMap::witness(points_table_poly, &params);

    let claims_to_reduce = to_multieval(EvalClaim {
        evs: output.iter().map(|p| p.evaluate(&point)).collect(),
        point,
    });
    (claims_to_reduce, trace)
}

pub fn bench_witness(c: &mut Criterion, log_num_points_s: impl Iterator<Item=usize>) {
    let mut witness = c.benchmark_group("sumcheck/witness");
    log_num_points_s
        .map(|size| {
            let (point, tables, params) = prepare_params(size);
            witness.bench_with_input(
                BenchmarkId::from_parameter(format!("new {}",size)),
                &size,
                |b, &size| {
                    b.iter_batched(
                        || (point.clone(), tables.clone(), params.clone()),
                        |(point, tables, params)| {
                            new_prepare_witness((point, tables, &params))
                        },
                        BatchSize::PerIteration,
                    )
                }
            );
            witness.bench_with_input(
                BenchmarkId::from_parameter(format!("old {}",size)),
                &size,
                |b, &size| {
                    b.iter_batched(
                        || (point.clone(), tables.clone(), params.clone()),
                        |(point, tables, params)| {
                            old_prepare_witness((point, tables, &params))
                        },
                        BatchSize::PerIteration,
                    )
                }
            );
        }).count();
}
pub fn bench_proof(c: &mut Criterion, log_num_points_s: impl Iterator<Item=usize>) {
    let mut proof = c.benchmark_group("sumcheck/proof");
    log_num_points_s
        .map(|size| {
            let (point, tables, params) = prepare_params(size);
            let (claims_to_reduce, trace) = new_prepare_witness((point, tables, &params));
            proof.bench_with_input(
                BenchmarkId::from_parameter(format!("new {}",size)),
                &size,
                |b, &size| {
                    b.iter_batched(
                    || {
                        let p_transcript = Transcript::new(b"test");
                        (claims_to_reduce.clone(), trace.clone(), params.clone(), p_transcript)
                    },
                    |(
                            claims_to_reduce,
                            trace,
                            params,
                            mut p_transcript,
                        )| {
                            let mut prover = SumcheckPolyMapProver::start(claims_to_reduce, trace, &params);

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
            proof.bench_with_input(
                BenchmarkId::from_parameter(format!("old {}",size)),
                &size,
                |b, &size| {
                    b.iter_batched(
                        || {
                            let p_transcript = Transcript::new(b"test");
                            (claims_to_reduce.clone(), trace.clone(), params.clone(), p_transcript)
                        },
                        |(
                             claims_to_reduce,
                             trace,
                             params,
                             mut p_transcript,
                         )| {
                            let mut prover = LameSumcheckPolyMapProver::start(claims_to_reduce, trace, &params);

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
pub fn bench_both(c: &mut Criterion, log_num_points_s: impl Iterator<Item=usize>) {
    let mut proof = c.benchmark_group("sumcheck/witness+proof");
    log_num_points_s
        .map(|size| {
            let (point, tables, params) = prepare_params(size);
            proof.bench_with_input(
                BenchmarkId::from_parameter(format!("new {}",size)),
                &size,
                |b, &size| {
                    b.iter_batched(
                        || Transcript::new(b"test"),
                        |mut p_transcript| {
                            let (claims_to_reduce, trace) = new_prepare_witness((point.clone(), tables.clone(), &params));

                            let mut prover = SumcheckPolyMapProver::start(claims_to_reduce, trace, &params);

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
            proof.bench_with_input(
                BenchmarkId::from_parameter(format!("old {}",size)),
                &size,
                |b, &size| {
                    b.iter_batched(
                        || Transcript::new(b"test"),
                        |mut p_transcript| {
                            let (claims_to_reduce, trace) = old_prepare_witness((point.clone(), tables.clone(), &params));

                            let mut prover = LameSumcheckPolyMapProver::start(claims_to_reduce, trace, &params);

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


pub fn sumcheck() {
    let mut criterion: Criterion<_> = (Criterion::default().sample_size(100).configure_from_args())
        .configure_from_args();
    let range = 12..=13;

    // bench_witness(&mut criterion, range.clone());
    bench_proof(&mut criterion, range.clone());
    bench_both(&mut criterion, range.clone());
}

criterion_main!(sumcheck);

