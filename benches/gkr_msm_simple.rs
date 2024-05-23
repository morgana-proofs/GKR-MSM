use ark_bls12_381::{Fr, G1Affine, G1Projective};
use ark_std::rand::Rng;
use ark_std::{test_rng, UniformRand};
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use identconv::camel;
use itertools::Itertools;
use merlin::Transcript;
use std::fmt::{Debug, Display};
use std::io::Write;
use std::ops::Range;
use std::path::Path;
use GKR_MSM::binary_msm::prepare_bases;
use GKR_MSM::gkr_msm_simple::{gkr_msm_prove, CommitmentKey};

extern crate cpuprofiler;
use cpuprofiler::PROFILER;
use criterion::profiler::Profiler;
use profi::{print_on_exit, prof};

fn prepare_data(
    (gamma, log_num_points): (usize, usize),
) -> (
    Vec<Vec<bool>>,
    Vec<(Fr, Fr)>,
    usize,
    usize,
    usize,
    CommitmentKey<G1Projective>,
    Transcript,
) {
    let log_num_scalar_bits = 8;
    let log_num_bit_columns = 7;

    let num_points = 1 << log_num_points;
    let num_vars = log_num_points + log_num_scalar_bits;
    let size = 1 << num_vars;
    let col_size = size >> log_num_bit_columns;

    let gen = &mut test_rng();
    let bases = (0..col_size).map(|i| G1Affine::rand(gen)).collect_vec();
    let coefs = (0..num_points)
        .map(|_| (0..256).map(|_| gen.gen_bool(0.5)).collect_vec())
        .collect_vec();
    let points = (0..num_points)
        .map(|i| ark_ed_on_bls12_381_bandersnatch::EdwardsAffine::rand(gen))
        .map(|p| (p.x, p.y))
        .collect_vec();
    let binary_extended_bases = prepare_bases::<_, G1Projective>(&bases, gamma);

    let comm_key = CommitmentKey::<G1Projective> {
        bases: Some(bases),
        binary_extended_bases: Some(binary_extended_bases),
        gamma,
    };

    let p_transcript = Transcript::new(b"test");

    (
        coefs,
        points,
        log_num_points,
        log_num_scalar_bits,
        log_num_bit_columns,
        comm_key,
        p_transcript,
    )
}

pub fn _simple_bench(c: &mut Criterion, gammas: Range<usize>, log_num_points_s: Range<usize>) {
    let mut grp = c.benchmark_group("gkr_msm_simple");
    gammas
        .map(|i| log_num_points_s.clone().map(|j| (i, j)).collect_vec())
        .flatten()
        .map(|params| {
            grp.bench_function(&format!("case::{:?}", params), |b| {
                b.iter_batched(
                    || prepare_data(params.clone()),
                    |(
                        coefs,
                        points,
                        log_num_points,
                        log_num_scalar_bits,
                        log_num_bit_columns,
                        comm_key,
                        mut p_transcript,
                    )| {
                        gkr_msm_prove(
                            coefs,
                            points,
                            log_num_points,
                            log_num_scalar_bits,
                            log_num_bit_columns,
                            &comm_key,
                            &mut p_transcript,
                        )
                    },
                    BatchSize::LargeInput,
                )
            });
        })
        .count();
}

pub fn bench(c: &mut Criterion) {
    _simple_bench(c, (4..9), (10..18));
}

criterion_group!(
    name = gkr_msm_simple;
    config = Criterion::default().sample_size(30).configure_from_args();
    targets =
        bench,
);
criterion_main!(gkr_msm_simple,);

