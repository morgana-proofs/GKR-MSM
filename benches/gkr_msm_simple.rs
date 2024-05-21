use std::io::Write;
use std::path::Path;
use ark_bls12_381::{Fr, G1Affine, G1Projective};
use ark_std::rand::Rng;
use ark_std::{test_rng, UniformRand};
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion, };
use itertools::Itertools;
use merlin::Transcript;
use GKR_MSM::binary_msm::prepare_bases;
use GKR_MSM::gkr_msm_simple::{gkr_msm_prove, CommitmentKey};

extern crate cpuprofiler;
use cpuprofiler::PROFILER;
use criterion::profiler::Profiler;
use profi::{print_on_exit, prof};

struct MyCustomProfiler {

}

impl Profiler for MyCustomProfiler{
    fn start_profiling(&mut self, benchmark_id: &str, benchmark_dir: &Path) {
        std::fs::create_dir_all(benchmark_dir).unwrap();
        let f = benchmark_dir.join(Path::new(&format!("my-prof.{}.profile", benchmark_id.replace("/", "_"))));
        if f.exists() {
            std::fs::remove_file(f.clone()).unwrap();
        }
        println!("{:#?}", f);
        let mut file = std::fs::File::create(f.clone()).unwrap();
        file.write(b"").unwrap();
        drop(file);
        PROFILER.lock().unwrap().start(f.as_os_str().as_encoded_bytes()).unwrap();
    }

    fn stop_profiling(&mut self, benchmark_id: &str, benchmark_dir: &Path) {
        PROFILER.lock().unwrap().stop().unwrap()
    }
}
fn profiled() -> Criterion {
    Criterion::default().with_profiler(MyCustomProfiler{})
}
fn prepare_data() -> (
    Vec<Vec<bool>>,
    Vec<(Fr, Fr)>,
    usize,
    usize,
    usize,
    CommitmentKey<G1Projective>,
    Transcript,
) {
    let gamma = 5;
    let log_num_points = 16;
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

    let mut p_transcript = Transcript::new(b"test");

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

pub fn simple_bench(c: &mut Criterion) {
    let mut grp = c.benchmark_group("group");
    grp.sample_size(20);

    grp.bench_function("gkr_msm_simple", |b| {
        b.iter_batched(
            prepare_data,
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
                    black_box(coefs),
                    black_box(points),
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
    grp.finish();
}

criterion_group!(gkr_msm_simple, simple_bench);
criterion_main!(gkr_msm_simple);
