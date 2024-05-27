use std::io::Write;
use std::path::Path;

use ark_bls12_381::{Fr, G1Affine, G1Projective};
use ark_std::{test_rng, UniformRand};
use ark_std::rand::Rng;
use criterion::{BatchSize, black_box, Criterion, criterion_group, criterion_main};
//extern crate cpuprofiler;
//use cpuprofiler::PROFILER;
use criterion::profiler::Profiler;
use itertools::Itertools;
use merlin::Transcript;
use profi::{print_on_exit, prof, prof_guard};

use GKR_MSM::binary_msm::prepare_bases;
use GKR_MSM::gkr_msm_simple::{CommitmentKey, gkr_msm_prove};

struct MyCustomProfiler {}

impl Profiler for MyCustomProfiler {
    fn start_profiling(&mut self, benchmark_id: &str, benchmark_dir: &Path) {
        std::fs::create_dir_all(benchmark_dir).unwrap();
        let f = benchmark_dir.join(Path::new(&format!(
            "my-prof.{}.profile",
            benchmark_id.replace("/", "_")
        )));
        if f.exists() {
            std::fs::remove_file(f.clone()).unwrap();
        }
        println!("{:#?}", f);
        let mut file = std::fs::File::create(f.clone()).unwrap();
        file.write(b"").unwrap();
        drop(file);
        // PROFILER
        //     .lock()
        //     .unwrap()
        //     .start(f.as_os_str().as_encoded_bytes())
        //     .unwrap();
    }

    fn stop_profiling(&mut self, benchmark_id: &str, benchmark_dir: &Path) {
        // PROFILER.lock().unwrap().stop().unwrap()
    }
}
fn profiled() -> Criterion {
    Criterion::default().with_profiler(MyCustomProfiler {})
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
    #[cfg(feature = "prof")]
    prof!("test-case-gen");
    
    let gamma = 6;
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

pub fn simple_bench() {
    let (
        coefs,
        points,
        log_num_points,
        log_num_scalar_bits,
        log_num_bit_columns,
        comm_key,
        mut p_transcript,
    ) = prepare_data();
    
    #[cfg(feature = "prof")]
    prof!("test-case");
    
    gkr_msm_prove(
        black_box(coefs),
        black_box(points),
        log_num_points,
        log_num_scalar_bits,
        log_num_bit_columns,
        &comm_key,
        &mut p_transcript,
    );
}

fn main() {
    print_on_exit!();
    simple_bench();
}

// Current timings:
// ┌────────────────────────────────────────────────────┬────────────────────┬───────────┬────────────┬──────────┬───────────────┬───────────┐
// │ Name                                               ┆ % Application Time ┆ Real Time ┆ % CPU Time ┆ CPU Time ┆ Average time  ┆ Calls     │
// ╞════════════════════════════════════════════════════╪════════════════════╪═══════════╪════════════╪══════════╪═══════════════╪═══════════╡
// │ gkr_msm_simple_prof::main                          ┆ 100.00%            ┆ 63.31s    ┆ 9.45%      ┆ 63.31s   ┆       -       ┆         1 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │  test-case-gen                                     ┆ 26.90%             ┆ 17.03s    ┆ 2.54%      ┆ 17.03s   ┆       -       ┆         1 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │  test-case                                         ┆ 72.93%             ┆ 46.17s    ┆ 6.89%      ┆ 46.17s   ┆       -       ┆         1 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │   gkr_msm_prove[bit_prep]                          ┆ 4.04%              ┆ 2.56s     ┆ 0.38%      ┆ 2.56s    ┆       -       ┆         1 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │   gkr_msm_prove[gkr_wtns]                          ┆ 12.43%             ┆ 7.87s     ┆ 1.17%      ┆ 7.87s    ┆       -       ┆         1 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │    map_over_poly                                   ┆ 10.76%             ┆ 6.81s     ┆ 1.02%      ┆ 6.81s    ┆ 139.06ms/call ┆        49 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │   gkr_msm_prove[gkr_claims]                        ┆ 0.00%              ┆ 338.10µs  ┆ 0.00%      ┆ 338.10µs ┆       -       ┆         1 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │   gkr_msm_prove[gkr_prover]                        ┆ 56.46%             ┆ 35.74s    ┆ 5.34%      ┆ 35.74s   ┆       -       ┆         1 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │    BintreeProver::round                            ┆ 56.45%             ┆ 35.73s    ┆ 5.33%      ┆ 35.73s   ┆ 42.90ms/call  ┆       833 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │     SumcheckPolyMapProver::round                   ┆ 50.90%             ┆ 32.22s    ┆ 4.81%      ┆ 32.22s   ┆ 39.44ms/call  ┆       817 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │      SumcheckPolyMapProver::eval_points_collection ┆ 1.85%              ┆ 1.17s     ┆ 0.17%      ┆ 1.17s    ┆ 1.52ms/call   ┆       768 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │      SumcheckPolyMapProver::accum_aggr             ┆ 0.00%              ┆ 177.85µs  ┆ 0.00%      ┆ 177.85µs ┆ 3.63µs/call   ┆        49 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │       SumcheckPolyMapProver::folded_f              ┆ 0.00%              ┆ 124.17µs  ┆ 0.00%      ┆ 124.17µs ┆ 633.00ns/call ┆       196 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │     SplitProver::round                             ┆ 0.00%              ┆ 24.86µs   ┆ 0.00%      ┆ 24.86µs  ┆ 1.55µs/call   ┆        16 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │ SumcheckPolyMapProver::accum_aggr                  ┆ 29.18%             ┆ 18.48s    ┆ 41.91%     ┆ 280.76s  ┆ 4.04µs/call   ┆  67107998 │
// ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┼╌╌╌╌╌╌╌╌╌╌╌┤
// │  SumcheckPolyMapProver::folded_f                   ┆ 14.18%             ┆ 8.98s     ┆ 20.98%     ┆ 140.57s  ┆ 526.00ns/call ┆ 268431992 │
// └────────────────────────────────────────────────────┴────────────────────┴───────────┴────────────┴──────────┴───────────────┴───────────┘
