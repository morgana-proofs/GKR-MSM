#![feature(iter_map_windows)]

use std::ops::Range;
use std::sync::Arc;

use ark_bls12_381::Fr;
use ark_std::{test_rng, UniformRand};
use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use itertools::Itertools;
use liblasso::poly::dense_mlpoly::DensePolynomial;
use GKR_MSM::nested_poly::{Polynomial, RandParams};
use GKR_MSM::protocol::protocol::PolynomialMapping;
use GKR_MSM::utils::{map_over_poly, map_over_poly_legacy};

fn prepare_data(
    (filled, num_ins, num_vars): (bool, usize, usize),
) -> (
    Vec<Polynomial<Fr>>, PolynomialMapping<Fr>
) {
    let gen = &mut test_rng();
    let mut params = RandParams::default();
    if filled {
        params = params.replace_gen_fill(Arc::new(|rng, layer_size, _| {
            layer_size
        }));
    }

    let mut ins = vec![Polynomial::<Fr>::rand_conf(
        gen,
        num_vars,
        params,
    )];
    while ins.len() < num_ins {
        ins.push(Polynomial::rand_fixed_structure(gen, &ins[0].layer_num_vars).0);
    }

    fn mapper(ins: &[Fr]) -> Vec<Fr> {
        ins.iter().map_windows(|[a, b]| *a * *b).collect_vec()
    }

    let f = PolynomialMapping {
        exec: Arc::new(mapper),
        degree: 2,
        num_i: num_ins,
        num_o: num_ins - 1,
    };
    (ins, f)
}

pub fn _simple_bench(c: &mut Criterion, num_ins: Range<usize>, num_vars: Range<usize>) {
    let mut grp = c.benchmark_group("map_over_poly");
    num_ins.clone().map(|i| num_vars.clone().map(|j| (i, j)).collect_vec())
        .flatten()
        .map(|params| {
            grp.bench_function(&format!("new::[sparse; ins: {}; vars: {}]", params.0, params.1), |b| {
                b.iter_batched(
                    || prepare_data((false, params.0, params.1)),
                    |(ins, f)| {
                        map_over_poly(
                            &ins,
                            f,
                        )
                    },
                    BatchSize::LargeInput,
                )
            });
            grp.bench_function(&format!("new::[dense; ins: {}; vars: {}]", params.0, params.1), |b| {
                b.iter_batched(
                    || prepare_data((true, params.0, params.1)),
                    |(ins, f)| {
                        map_over_poly(
                            &ins,
                            f,
                        )
                    },
                    BatchSize::LargeInput,
                )
            });
            grp.bench_function(&format!("old::[ins: {}; vars: {}]", params.0, params.1), |b| {
                b.iter_batched(
                    || {
                        let (ins, f) = prepare_data((false, params.0, params.1));
                        (ins.into_iter().map(|p| p.into()).collect::<Vec<DensePolynomial<Fr>>>(), f.exec)
                    },
                    |(ins, f)| {
                        map_over_poly_legacy(
                            &ins,
                            |i| f(i),
                        )
                    },
                    BatchSize::LargeInput,
                )
            });
        })
        .count();
}

pub fn bench(c: &mut Criterion) {
    _simple_bench(c, 2..3, 14..17);
}

criterion_group!(
    name = map_over_poly_bench;
    config = Criterion::default().sample_size(1000).configure_from_args();
    targets =
        bench,
);
criterion_main!(map_over_poly_bench,);

