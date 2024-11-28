use std::fmt::{Display, Formatter};
use ark_ed_on_bls12_381_bandersnatch::Fq;
use ark_std::{test_rng, UniformRand};
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use itertools::Itertools;
use num_traits::{One, Zero};
use GKR_MSM::cleanup::polys::vecvec::VecVecPolynomial;

struct VecVecGrp {
    num_vars: usize,
    num_vertical_vars: usize,
}

impl Display for VecVecGrp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {}]", self.num_vars, self.num_vertical_vars)
    }
}

mod maps {
    use ark_ed_on_bls12_381_bandersnatch::Fq;
    use ark_ff::PrimeField;
    use itertools::Itertools;
    use GKR_MSM::cleanup::polys::common::MapSplit;
    use GKR_MSM::cleanup::polys::vecvec::VecVecPolynomial;
    use GKR_MSM::cleanup::utils::algfn::AlgFn;
    use GKR_MSM::cleanup::utils::twisted_edwards_ops::{algfns::twisted_edwards_add_l3, fns::twisted_edwards_add_l3 as twisted_edwards_add_l3_fn};
    use GKR_MSM::utils::TwistedEdwardsConfig;

    pub fn naive<F: PrimeField + TwistedEdwardsConfig>(polys: &[Vec<F>]) -> Vec<Vec<F>> {
        let mut out = vec![Vec::with_capacity(polys[0].len()); twisted_edwards_add_l3::<Fq>().n_outs()];

        for i in 0..polys[0].len() {
            for (idx, o) in twisted_edwards_add_l3_fn(&polys.iter().map(|p| p[i]).collect_vec()).into_iter().enumerate() {
                out[idx].push(o);
            }
        }

        out
    }
    pub fn dense<F: PrimeField + TwistedEdwardsConfig>(polys: &[Vec<F>]) -> Vec<Vec<F>> {
        Vec::algfn_map(polys, twisted_edwards_add_l3())
    }
    pub fn vecvec<F: PrimeField + TwistedEdwardsConfig>(polys: &[VecVecPolynomial<F>]) -> Vec<VecVecPolynomial<F>> {
        VecVecPolynomial::algfn_map(polys, twisted_edwards_add_l3())
    }
}

mod splitmaps {
    fn naive() {

    }
    fn dense() {

    }
    fn vecvec() {

    }
}

fn bench_map(c: &mut Criterion) {
    let mut group = c.benchmark_group("PolyMap");
    let rng = &mut test_rng();
    for num_vars in 18..19 {
        let data = (0..4).map(|_| (0..1 << num_vars).map(|_| Fq::rand(rng)).collect_vec()).collect_vec();
        group.bench_with_input(
            BenchmarkId::new("Naive", num_vars),
            &num_vars,
            |b, i| {
                b.iter_batched_ref(
                    || data.clone(),
                    |data| maps::naive(data),
                    BatchSize::SmallInput,
                )
            }
        );
        group.bench_with_input(
            BenchmarkId::new("Dense", num_vars),
            &num_vars,
            |b, i| {
                b.iter_batched_ref(
                    || data.clone(),
                    |data| maps::dense(data),
                    BatchSize::SmallInput,
                )
            }
        );
        for num_vertical_vars in 2..(num_vars - 2) {
            let vvdata = data.iter().map(|p| {
                VecVecPolynomial::new(
                    p.chunks(1 << (num_vars - num_vertical_vars)).map(|p| p.to_vec()).collect_vec(),
                    Fq::one(),
                    Fq::one(),
                    num_vars - num_vertical_vars,
                    num_vertical_vars,
                )
            }).collect_vec();
            group.bench_with_input(
                BenchmarkId::new("VecVec", VecVecGrp { num_vars, num_vertical_vars }),
                &num_vars,
                |b, i| {
                    b.iter_batched_ref(
                        || vvdata.clone(),
                        |data| maps::vecvec(data),
                        BatchSize::SmallInput,
                    )
                }
            );
        }
    }
    group.finish();
}

// fn bench_splitmap(c: &mut Criterion) {
//     let mut group = c.benchmark_group("PolySplitMap");
//     for i in [20u64, 21u64].iter() {
//         group.bench_with_input(BenchmarkId::new("Naive", i), i,
//                                |b, i| b.iter(|| fibonacci_slow(*i)));
//         group.bench_with_input(BenchmarkId::new("Dense", i), i,
//                                |b, i| b.iter(|| fibonacci_fast(*i)));
//         group.bench_with_input(BenchmarkId::new("VecVec", i), i,
//                                |b, i| b.iter(|| fibonacci_fast(*i)));
//     }
//     group.finish();
// }

criterion_group!(benches, bench_map);
criterion_main!(benches);