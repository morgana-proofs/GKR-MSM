use ark_ec::pairing::Pairing;
use ark_std::test_rng;
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use std::fmt::{Display, Formatter};
use std::ops::Range;
use GKR_MSM::cleanup::proof_transcript::{ProofTranscript2, TProofTranscript2};
use GKR_MSM::cleanup::protocols::pippenger::benchutils::{build_pippenger_data, run_pippenger, PippengerData, PippengerOutput};

struct PipGridSearchParams {
    num_vars: usize,
    d_logsize: usize,
    commitment_log_multiplicity: usize,
}
impl Display for PipGridSearchParams {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[N={:02}, d={:02}, clm={}]", self.num_vars, self.d_logsize, self.commitment_log_multiplicity)
    }
}


struct PipGridSearchBounds {
    num_vars: Range<usize>,
    d_logsize: Range<usize>,
    commitment_log_multiplicity: Range<usize>,
}

impl PipGridSearchBounds {
    fn into_iter(self) -> impl Iterator<Item=PipGridSearchParams> {
        self.num_vars.clone().into_iter().map(move |num_vars| {
            let _commitment_log_multiplicity = self.commitment_log_multiplicity.clone();
            self.d_logsize.clone().into_iter().map(move |d_logsize|
                _commitment_log_multiplicity.clone().into_iter().map(move |commitment_log_multiplicity|
                PipGridSearchParams { num_vars, d_logsize, commitment_log_multiplicity }
            )
            ).flatten()
        }).flatten()
    }
}

fn pippenger_benchmark(data: PippengerData) -> PippengerOutput {
    let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");
    let ret = run_pippenger(&mut transcript_p, data);
    transcript_p.end();
    ret
}

fn bench_pippenger(c: &mut Criterion) {
    let mut group = c.benchmark_group("Pippenger");
    let rng = &mut test_rng();
    let grid_search = PipGridSearchBounds {
        num_vars: 10..16,
        d_logsize: 2..10,
        commitment_log_multiplicity: 1..3,
    };
    for params in grid_search.into_iter() {
        let PipGridSearchParams { num_vars, d_logsize, commitment_log_multiplicity } = params;
        let pipdata = build_pippenger_data(rng, d_logsize, num_vars, 128, commitment_log_multiplicity);
        group.bench_with_input(
            BenchmarkId::new("wtns+prover", format!("{}", params)),
            &num_vars,
            |b, i| {
                b.iter_batched(
                    || pipdata.clone(),
                    pippenger_benchmark,
                    BatchSize::SmallInput,
                )
            }
        );
    }

    group.finish();
}

criterion_group!(benches, bench_pippenger);
criterion_main!(benches);