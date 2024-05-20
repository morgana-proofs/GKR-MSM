use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use itertools::Itertools;
use liblasso::poly::dense_mlpoly::DensePolynomial;
use rayon::iter::IntoParallelIterator;
use rayon::iter::IndexedParallelIterator;
use rayon::iter::IntoParallelRefIterator;
use rayon::iter::IntoParallelRefMutIterator;
use rayon::iter::ParallelIterator;
use rayon::prelude::*;
use crate::msm_nonaffine::VariableBaseMSM_Nonaffine;

/// This structure hosts a counter 'mapping', an array 'image',
/// and represents a pullback, i.e. a table
/// T[i] = image[mapping[i]]

fn u8from(it: impl Iterator<Item=bool>) -> u8 {
    let mut s = 0;
    it.take(8).map(|b| s = (s << 1) + if b {1} else {0}).last();
    s
}

pub fn binary_msm<F, G: CurveGroup<ScalarField=F>>(coefs: &[u8], bases: &[Vec<G::MulBase>]) -> G
where
    G::MulBase: Send,
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


pub fn prepare_chunk<F, G: CurveGroup<ScalarField=F>>(chunk: &[G::MulBase]) -> Vec<G::MulBase> {
    let proj = (1..(1 << 8)).map(
        |i| {
            (0..8).zip(chunk.iter().rev())
                .filter(|(idx, _)| (1 << idx) & i != 0)
                .map(|(_, b): (_, &G::Affine)| *b)
                .fold(G::zero(), |acc, new| acc + new)
        }
    ).collect_vec();
    G::normalize_batch(&proj)

}
pub fn prepare_bases<F, G: CurveGroup<ScalarField=F>>(bases: &[G::MulBase]) -> Vec<Vec<G::MulBase>> {
    let a = bases.par_chunks(8);
    a.map(|chunk: &[G::MulBase]| {
        prepare_chunk::<F, G>(chunk)
    }).collect()
}

pub fn prepare_coefs(coefs: impl Iterator<Item=bool>) -> Vec<u8> {
    coefs.chunks(8).into_iter().map(|chunk| u8from(chunk)).collect()
}

#[cfg(test)]
mod test {
    use ark_bls12_381::Fr;
    use ark_bls12_381::{G1Projective, G1Affine};
    use ark_std::rand::Rng;
    use super::*;
    use ark_std::{test_rng, UniformRand, Zero};

    #[test]
    fn bin_msm() {
        let num = 100;
        let gen = &mut test_rng();
        let coefs = (0..num).map(|_| gen.gen_bool(0.5)).collect_vec();
        let pcoefs: Vec<u8> = prepare_coefs(coefs.clone().into_iter());
        let bases = (0..num).map(|i| G1Affine::rand(gen)).collect_vec();
        let pbases = prepare_bases::<_, G1Projective>(&bases);

        println!("{:?}", coefs);
        println!("{:?}", pcoefs);

        let res = binary_msm::<_, G1Projective>(&pcoefs, &pbases);
        let expected = coefs.iter().zip_eq(bases.iter()).filter(|(&c, b)| c).map(|(c, b)| b).fold(G1Projective::zero(), |acc, new| acc + new);
        assert_eq!(res.into_affine(), expected.into_affine());
    }
}