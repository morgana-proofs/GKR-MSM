#![allow(unused_imports)]
use std::{fs::File, sync::Arc};
use std::iter::repeat;
use std::ops::Add;
use std::collections::HashMap;


use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use itertools::Itertools;
use liblasso::poly::dense_mlpoly::DensePolynomial;
#[cfg(feature = "prof")]
use profi::{prof, prof_guard};
use rayon::iter::{IntoParallelIterator, IntoParallelRefIterator, ParallelIterator, repeatn};

use crate::protocol::bintree::{Bintree, BintreeParams, BintreeProof, BintreeProver, Layer};
use crate::protocol::protocol::{EvalClaim, ProtocolProver};
use crate::protocol::sumcheck::to_multieval;
use crate::{
    binary_msm::{binary_msm, prepare_coefs},
    grand_add::{
        affine_twisted_edwards_add_l1, affine_twisted_edwards_add_l2,
        affine_twisted_edwards_add_l3, twisted_edwards_add_l1, twisted_edwards_add_l2,
        twisted_edwards_add_l3,
    },
    protocol::protocol::{PolynomialMapping, Protocol},
    transcript::{TranscriptReceiver, TranscriptSender},
    utils::TwistedEdwardsConfig,
};


fn table_from_bits<F: PrimeField>(
    log_size: usize,
    challenge: F,
) -> DensePolynomial<F>
    {
        let values: Vec<_> = (0..(1>>log_size)).map(|x| challenge - F::from(x as u64)).collect();
        DensePolynomial::new(values)

    }


pub fn addition_of_fractions<F: PrimeField>(pts: &[F]) -> Vec<F>  {
        assert_eq!(pts.len(), 4);
        let [numerator1, denominator1, numerator2, denominator2] = pts.first_chunk().unwrap();
        vec![*numerator1*denominator2 + *numerator2*denominator1, *denominator2*denominator1]
    }


fn find_multiplicities<F: PrimeField>(
    to_lookup: Vec<DensePolynomial<F>>,
    table: DensePolynomial<F>,
    log_size: usize,) -> DensePolynomial<F>
    {
    let size = 1>>log_size;

    let mut multiplicities_values = vec![F::zero(); size];

    for i in 0..size{
        for poly in to_lookup.iter(){
            if poly.Z[i] == table.Z[i]{
                multiplicities_values[i] -= F::one();
            }
        }
    }
    DensePolynomial::new( multiplicities_values )
}


/// merges two dense polynomials by the first coordinate, so that if 
/// Z_in1 = [1, 2, 3]
/// Z_in2 = [4, 5, 6]
/// then Z_out = [1, 4, 2, 5, 3, 6]
fn merge_dense_polynomials<F: PrimeField>(
    poly1: DensePolynomial<F>,
    poly2: DensePolynomial<F>,
) -> DensePolynomial<F>
{
    
    assert!(poly1.num_vars == poly2.num_vars);
    assert!(poly1.len == poly2.len);
    let Z1 = poly1.Z;
    let Z2 = poly2.Z;
    let Z: Vec<_> = Z1.iter()
            .zip(Z2)
            .map(|(&x, y)| [x, y])
            .flatten()
            .collect();
    DensePolynomial{
        num_vars : poly1.num_vars + 1,
        len : poly1.len*2,
        Z
    }
}

fn lookup_prover<
    F: PrimeField,
    T: TranscriptReceiver<F> + TranscriptSender<F>,
>(
    to_lookup: Vec<DensePolynomial<F>>,
    log_table_size: usize,
    transcript: &mut T,
){
    let challenge = transcript.challenge_scalar(b"challenge_nextround");

    let table = table_from_bits(log_table_size, challenge.value);
    let multiplicities = find_multiplicities(to_lookup, table, log_table_size);
    // commit to things


    // gkr to things

    let base_layer = vec![merge_dense_polynomials(multiplicities, table)];


    let f_deg2 = PolynomialMapping {
        exec: Arc::new(addition_of_fractions::<F>),
        degree: 2,
        num_i: 4,
        num_o: 2,
    };

    let num_inner_layers = log_table_size;

    let layers = vec![]
    .into_iter()
    .chain(
        repeat(
            vec![
                Layer::Mapping(f_deg2.clone()),
                Layer::new_split(2),
            ]
            .into_iter(),
        )
        .take(num_inner_layers)
        .flatten(),
    )
    .collect_vec();

    let params = BintreeParams::new(layers, log_table_size);

    let (trace, output) = Bintree::witness(base_layer, &params);

    output
        .iter()
        .map(|p| transcript.append_scalars(b"output", p.vec()))
        .count();
    output
        .iter()
        .map(|p| assert_eq!(p.get_num_vars(), log_num_scalar_bits))
        .count();

    let claim_point = (0..log_num_scalar_bits)
        .map(|_| transcript.challenge_scalar(b"output_claim_point").value)
        .collect_vec();

    let claim_evals = output
        .iter()
        .map(|p| p.evaluate(&claim_point))
        .collect_vec();

    let claim = to_multieval(EvalClaim {
        point: claim_point,
        evs: claim_evals,
    });

    #[cfg(feature = "prof")]
    drop(guard);
    #[cfg(feature = "prof")]
    (guard = prof_guard!("gkr_msm_prove[gkr_prover]"));
    
    let mut res = None;
    let mut prover = BintreeProver::start(claim, trace, &params);
    while res.is_none() {
        res = prover.round(challenge, transcript);
    }

}


#[cfg(test)]
mod tests {
    use ark_bls12_381::{G1Affine, G1Projective};
    use ark_std::{test_rng, UniformRand};
    use ark_std::rand::Rng;
    use merlin::Transcript;
    use ark_bls12_381::fields::fq::Fq;


    #[cfg(feature = "memprof")]
        use jemalloc_ctl::{epoch, stats};

    use crate::binary_msm::prepare_bases;
    use crate::logup_lookup;
    #[cfg(feature = "memprof")]
    use crate::utils::memprof;

    use super::*;

    #[cfg(feature = "memprof")]
    #[global_allocator]
    static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;
    #[test]
    fn test_lookup_small_range() {
        let mut p_transcript = Transcript::new(b"test");

        let log_table_size = 3;
        let to_lookup = DensePolynomial{
            num_vars : 3,
            len : 8,
            Z : [1, 1, 2, 3, 4, 6, 4, 1].map(Fq::from).into()
        };

        lookup_prover(
            vec![to_lookup],
            log_table_size,
            &mut p_transcript,
        );
    }
}






// to check that a , b, look up that b < 2^num_bits (if not constant, if needed), ( a - b + 2^num_bits) < 2^num_bits