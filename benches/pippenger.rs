use std::fmt::{Display, Formatter};
use ark_ec::CurveConfig;
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

#[derive(Clone)]
struct PippengerData {
    pub points: Vec<Affine<BandersnatchConfig>>,
    pub coefs: Vec<<BandersnatchConfig as CurveConfig>::ScalarField>,
    pub y_size: usize,
    pub y_logsize: usize,
    pub d_logsize: usize,
    pub x_logsize: usize,
    pub r: Vec<<BandersnatchConfig as CurveConfig>::BaseField>,
}
fn build_pippenger_data<RNG: Rng>(rng: &mut RNG, d_logsize: usize, x_logsize: usize) -> PippengerData {
    let points = (0..(1 << x_logsize)).map(|_| Affine::<BandersnatchConfig>::rand(rng)).collect_vec();
    let coefs = (0..(1 << x_logsize)).map(|_| <BandersnatchConfig as CurveConfig>::ScalarField::rand(rng)).collect_vec();

    let num_bits = <<BandersnatchConfig as CurveConfig>::ScalarField as PrimeField>::BigInt::NUM_LIMBS * 8;
    let size_x = points.len();
    let y_size = (num_bits + d_logsize - 1) / d_logsize;
    let x_logsize = log2(size_x) as usize;
    let y_logsize = log2(y_size) as usize;

    let r = (0..y_logsize).map(|_| <BandersnatchConfig as CurveConfig>::BaseField::rand(rng)).collect_vec();


    PippengerData {
        points,
        coefs,
        y_size,
        y_logsize,
        d_logsize,
        x_logsize,
        r,
    }
}

fn pippenger(data: &mut PippengerData) -> (Vec<Vec<<BandersnatchConfig as CurveConfig>::BaseField>>, SinglePointClaims<<BandersnatchConfig as CurveConfig>::BaseField>, Vec<u8>) {
    let PippengerData {
        points,
        coefs,
        y_size,
        y_logsize,
        d_logsize,
        x_logsize,
        r,
    } = data;

    let pip_wg = PippengerWG::<BandersnatchConfig>::new(
        &points,
        &coefs,
        *y_size,
        *y_logsize,
        *d_logsize,
        *x_logsize,
    );


    let dense_output: Vec<Vec<_>> = triangle_add::builder::witness::last_step(
        pip_wg.ending.advices.last().unwrap().into(),
        *y_logsize + *d_logsize - 2 - SplitIdx::HI(*y_logsize).hi_usize(*y_logsize + *d_logsize - 2)
    );

    let claims = SinglePointClaims {
        evs: dense_output.iter().map(|output| evaluate_poly(output, &r)).collect(),
        point: r.clone(),
    };

    let pippenger = Pippenger::new(
        *y_size,
        *y_logsize,
        *d_logsize,
        *x_logsize,
    );


    let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");

    let (prover_claims, _) = pippenger.prove(&mut transcript_p, claims.clone(), pip_wg);
    let proof = transcript_p.end();
    (dense_output, prover_claims, proof)

}

fn bench_pippenger(c: &mut Criterion) {
    let mut group = c.benchmark_group("Pippenger");
    let rng = &mut test_rng();
    for num_vars in 10..=19 {
        for d_logsize in 2..=10 {
            let pipdata = build_pippenger_data(rng, d_logsize, num_vars);
            group.bench_with_input(
                BenchmarkId::new("wtns+prover", format!("{:02} vars, {:02} d_logsize", num_vars, d_logsize)),
                &num_vars,
                |b, i| {
                    b.iter_batched_ref(
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