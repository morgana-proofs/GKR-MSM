use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use itertools::Itertools;
use rayon::iter::IndexedParallelIterator;
use rayon::iter::IntoParallelIterator;
use rayon::iter::IntoParallelRefIterator;
use rayon::iter::IntoParallelRefMutIterator;
use rayon::iter::ParallelIterator;
use rayon::prelude::*;

use crate::msm_nonaffine::VariableBaseMSM_Nonaffine;

/// This structure hosts a counter 'mapping', an array 'image',
/// and represents a pullback, i.e. a table
/// T[i] = image[mapping[i]]

fn into_u8(it: impl Iterator<Item=bool>) -> u8 {
    let mut s = 0;
    it.take(8).map(|b| s = (s << 1) + if b {1} else {0}).last();
    s
}

pub fn binary_msm<F, G: CurveGroup<ScalarField=F>>(coefs: &[u8], bases: &[Vec<G::Affine>]) -> G
{
    assert_eq!(coefs.len(), bases.len());
    bases.par_iter().zip(coefs.par_iter()).filter(|(_, &idx)| idx as usize != 0).map(|(base, idx)| base[(*idx) as usize - 1]).fold(
        G::zero,
        |acc, new| acc + new
    ).reduce(
        G::zero,
        |left, right| left + right
    )
}


pub fn prepare_chunk<F, G: CurveGroup<ScalarField=F>>(chunk: &[G::Affine], gamma: usize) -> Vec<G::Affine> {
    let proj = (1..(1 << gamma)).map(
        |i| {
            (0..gamma).zip(chunk.iter().rev())
                .filter(|(idx, _)| (1 << idx) & i != 0)
                .map(|(_, b): (_, &G::Affine)| *b)
                .fold(G::zero(), |acc, new| acc + new)
        }
    ).collect_vec();
    G::normalize_batch(&proj)

}
pub fn prepare_bases<F, G: CurveGroup<ScalarField=F>>(bases: &[G::Affine], gamma: usize) -> Vec<Vec<G::Affine>> {
    let a = bases.par_chunks(gamma);
    a.map(|chunk: &[G::Affine]| {
        prepare_chunk::<F, G>(chunk, gamma)
    }).collect()
}

pub fn prepare_coefs(coefs: impl Iterator<Item=bool>, gamma: usize) -> Vec<u8> {
    coefs.chunks(gamma).into_iter().map(|chunk| into_u8(chunk)).collect()
}

#[cfg(test)]
mod test {
    use ark_bls12_381::{G1Affine, G1Projective};
    use ark_std::{test_rng, UniformRand, Zero};
    use ark_std::rand::Rng;

    use super::*;

    #[test]
    fn bin_msm() {
        let num = 100;
        let gen = &mut test_rng();
        let coefs = (0..num).map(|_| gen.gen_bool(0.5)).collect_vec();
        let pcoefs: Vec<u8> = prepare_coefs(coefs.clone().into_iter(), 8);
        let bases = (0..num).map(|i| G1Affine::rand(gen)).collect_vec();
        let pbases = prepare_bases::<_, G1Projective>(&bases, 8);

        println!("{:?}", coefs);
        println!("{:?}", pcoefs);

        let res = binary_msm::<_, G1Projective>(&pcoefs, &pbases);
        let expected = coefs.iter().zip_eq(bases.iter()).filter(|(&c, b)| c).map(|(c, b)| b).fold(G1Projective::zero(), |acc, new| acc + new);
        assert_eq!(res.into_affine(), expected.into_affine());
    }


    #[test]
    fn bin_msm_gamma_3() {
        let num = 100;
        let gen = &mut test_rng();
        let coefs = (0..num).map(|_| gen.gen_bool(0.5)).collect_vec();
        let pcoefs: Vec<u8> = prepare_coefs(coefs.clone().into_iter(), 3);
        let bases = (0..num).map(|i| G1Affine::rand(gen)).collect_vec();
        let pbases = prepare_bases::<_, G1Projective>(&bases, 3);

        println!("{:?}", coefs);
        println!("{:?}", pcoefs);

        let res = binary_msm::<_, G1Projective>(&pcoefs, &pbases);
        let expected = coefs.iter().zip_eq(bases.iter()).filter(|(&c, b)| c).map(|(c, b)| b).fold(G1Projective::zero(), |acc, new| acc + new);
        assert_eq!(res.into_affine(), expected.into_affine());
    }
}