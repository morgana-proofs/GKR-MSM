use std::fmt::{Display, Formatter};
use ark_ec::CurveConfig;
use ark_ec::pairing::Pairing;
use ark_ec::twisted_edwards::{Affine, TECurveConfig};
use ark_ed_on_bls12_381_bandersnatch::{BandersnatchConfig, Fq};
use ark_ff::{BigInteger, PrimeField};
use ark_std::{log2, test_rng, UniformRand};
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use itertools::Itertools;
use num_traits::{One, Zero};
use rand::Rng;
use GKR_MSM::cleanup::polys::dense::MIN_PAR_CHUNK_INPUT;
use GKR_MSM::cleanup::polys::vecvec::VecVecPolynomial;
use GKR_MSM::cleanup::proof_transcript::{ProofTranscript2, TProofTranscript2};
use GKR_MSM::cleanup::protocol2::Protocol2;
use GKR_MSM::cleanup::protocols::gkrs::triangle_add;
use GKR_MSM::cleanup::protocols::pippenger::{Pippenger, PippengerWG};
use GKR_MSM::cleanup::protocols::splits::SplitIdx;
use GKR_MSM::cleanup::protocols::sumcheck::SinglePointClaims;
use GKR_MSM::cleanup::utils::arith::evaluate_poly;
use GKR_MSM::utils::TwistedEdwardsConfig;
use ark_bls12_381::Bls12_381 as Ctx;
use GKR_MSM::commitments::knuckles::KnucklesProvingKey;
use GKR_MSM::commitments::kzg::random_kzg_pk;
use ark_bls12_381::Fr;


fn bench_pippenger(c: &mut Criterion) {
    let mut group = c.benchmark_group("Pippenger");
    let rng = &mut test_rng();
    for num_vars in 10..=10 {
        for d_logsize in 8..=8 {
            let pipdata = build_pippenger_data(rng, d_logsize, num_vars);
            group.bench_with_input(
                BenchmarkId::new("wtns+prover", format!("{:02} vars, {:02} d_logsize", num_vars, d_logsize)),
                &num_vars,
                |b, i| {
                    b.iter_batched(
                        || pipdata.clone(),
                        pippenger,
                        BatchSize::SmallInput,
                    )
                }
            );
        }
    }
    group.finish();
}

criterion_group!(benches, bench_pippenger);
criterion_main!(benches);