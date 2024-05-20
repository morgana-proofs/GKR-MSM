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

pub trait SmallBinType: Into<usize> + Sync + Send + Copy {
    const size: usize;

    fn from_bool_iter(it: impl Iterator<Item=bool>) -> Self;
}

impl SmallBinType for bool {
    const size: usize = 1;

    fn from_bool_iter(it: impl Iterator<Item=bool>) -> Self {
        it.take(Self::size).next().unwrap()
    }
}

impl SmallBinType for u8 {
    const size: usize = 8;

    fn from_bool_iter(it: impl Iterator<Item=bool>) -> Self {
        let mut s = 0;
        it.take(Self::size).map(|b| s = (s << 1) + if b {1} else {0}).last();
        s
    }
}
impl SmallBinType for u16 {
    const size: usize = 16;

    fn from_bool_iter(it: impl Iterator<Item=bool>) -> Self {
        let mut s = 0;
        it.take(Self::size).map(|b| s = (s << 1) + if b {1} else {0}).last();
        s
    }
}

pub fn binary_msm<F, G: CurveGroup<ScalarField=F>, T: SmallBinType>(coefs: &[T], bases: &[Vec<G::Affine>]) -> G {
    assert_eq!(coefs.len(), bases.len());
    bases.par_iter().zip(coefs.par_iter()).filter(|(_, &idx)| idx.into() != 0).map(|(base, idx)| base[(*idx).into() - 1]).fold(
        G::zero,
        |acc, new| acc + new
    ).reduce(
        G::zero,
        |left, right| left + right
    )
}


pub fn prepare_chunk<F, G: CurveGroup<ScalarField=F>, T: SmallBinType>(chunk: &[G::Affine]) -> Vec<G::Affine> {
    let proj = (1..(1 << T::size)).map(
        |i| {
            (0..T::size).zip(chunk.iter().rev())
                .filter(|(idx, _)| (1 << idx) & i != 0)
                .map(|(_, b): (_, &G::Affine)| *b)
                .fold(G::zero(), |acc, new| acc + new)
        }
    ).collect_vec();
    G::normalize_batch(&proj)

}
pub fn prepare_bases<F, G: CurveGroup<ScalarField=F>, T: SmallBinType>(bases: &[G::Affine]) -> Vec<Vec<G::Affine>> {
    let a = bases.par_chunks(T::size);
    a.map(|chunk: &[G::Affine]| {
        prepare_chunk::<F, G, T>(chunk)
    }).collect()
}

pub fn prepare_coefs<T: SmallBinType>(coefs: impl Iterator<Item=bool>) -> Vec<T> {
    coefs.chunks(T::size).into_iter().map(|chunk| T::from_bool_iter(chunk)).collect()
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
        let bases = (0..num).map(|_| G1Affine::rand(gen)).collect_vec();
        let pbases = prepare_bases::<_, G1Projective, u8>(&bases);

        println!("{:?}", coefs);
        println!("{:?}", pcoefs);

        let res = binary_msm::<_, G1Projective, u8>(&pcoefs, &pbases);
        let expected = coefs.iter().zip_eq(bases.iter()).filter(|(&c, b)| c).map(|(c, b)| b).fold(G1Projective::zero(), |acc, new| acc + new);
        assert_eq!(res.into_affine(), expected.into_affine());
    }
}