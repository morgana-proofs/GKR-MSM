use ark_bls12_381::{Fr, G1Affine, G1Projective};
use ark_std::rand::Rng;
use ark_std::{test_rng, UniformRand};
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use itertools::Itertools;
use merlin::Transcript;
use std::io::Write;
use std::path::Path;
use GKR_MSM::binary_msm::prepare_bases;
use GKR_MSM::gkr_msm_simple::{gkr_msm_prove, CommitmentKey};
use identconv::camel;

extern crate cpuprofiler;
use cpuprofiler::PROFILER;
use criterion::profiler::Profiler;
use profi::{print_on_exit, prof};

fn prepare_data(
   gamma: usize,
   log_num_points: usize,
) -> (
    Vec<Vec<bool>>,
    Vec<(Fr, Fr)>,
    usize,
    usize,
    usize,
    CommitmentKey<G1Projective>,
    Transcript,
) {
    // let gamma = 6;
    // let log_num_points = 16;
    let log_num_scalar_bits = 8;
    let log_num_bit_columns = 7;

    let num_points = 1 << log_num_points;
    let num_scalar_bits = 1 << log_num_scalar_bits;
    let num_vars = log_num_points + log_num_scalar_bits;
    let size = 1 << num_vars;
    let num_bit_columns = 1 << log_num_bit_columns;
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

pub fn _simple_bench<
    F: Fn() -> (
        Vec<Vec<bool>>,
        Vec<(Fr, Fr)>,
        usize,
        usize,
        usize,
        CommitmentKey<G1Projective>,
        Transcript,
    ),
>(
    c: &mut Criterion,
    f: F,
) {
// }
// pub fn simple_bench(c: &mut Criterion) {
    let mut grp = c.benchmark_group("group");
    grp.sample_size(20);

    grp.bench_function("gkr_msm_simple", |b| {
        b.iter_batched(
            || f(),
            // prepare_data,
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
            BatchSize::NumIterations(1),
        )
    });
    grp.finish();
}



pub fn bench_3_16(c: &mut Criterion) {
    _simple_bench(c, || prepare_data(3, 16));
}
pub fn bench_4_16(c: &mut Criterion) {
    _simple_bench(c, || prepare_data(4, 16));
}
pub fn bench_5_16(c: &mut Criterion) {
    _simple_bench(c, || prepare_data(5, 16));
}
pub fn bench_6_16(c: &mut Criterion) {
    _simple_bench(c, || prepare_data(6, 16));
}
pub fn bench_1_20(c: &mut Criterion) {
    _simple_bench(c, || prepare_data(1, 20));
}

criterion_group!(gkr_msm_simple_bench_gamma_3_logpoints_16, bench_3_16);
criterion_group!(gkr_msm_simple_bench_gamma_4_logpoints_16, bench_4_16);
criterion_group!(gkr_msm_simple_bench_gamma_5_logpoints_16, bench_5_16);
criterion_group!(gkr_msm_simple_bench_gamma_6_logpoints_16, bench_6_16);
criterion_group!(gkr_msm_simple_bench_gamma_6_logpoints_20, bench_1_20);

criterion_main!(
    // gkr_msm_simple_bench_gamma_3_logpoints_16,
    // gkr_msm_simple_bench_gamma_4_logpoints_16,
    // gkr_msm_simple_bench_gamma_5_logpoints_16,
    // gkr_msm_simple_bench_gamma_6_logpoints_16,
    gkr_msm_simple_bench_gamma_6_logpoints_20,
);