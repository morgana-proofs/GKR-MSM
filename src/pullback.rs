use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use rayon::iter::IndexedParallelIterator;
use rayon::iter::IntoParallelIterator;
use rayon::iter::IntoParallelRefIterator;
use rayon::iter::IntoParallelRefMutIterator;
use rayon::iter::ParallelIterator;

use crate::msm_nonaffine::VariableBaseMsmNonaffine;
use crate::utils::split_into_chunks_balanced;

/// This structure hosts a counter 'mapping', an array 'image',
/// and represents a pullback, i.e. a table
/// T[i] = image[mapping[i]]
pub struct Pullback<F: PrimeField> {
    pub mapping: Vec<usize>,
    pub image: Vec<F>,
}

impl<F: PrimeField> Pullback<F> {

    /// Computes the pullback.
    pub fn values(&self) -> Vec<F> {
        self.mapping.par_iter().map(|i|self.image[*i]).collect()
    }

    /// Computes pullback's MSM by first aggregating repeated elements, and then doing normal MSM.
    pub fn bucketed_msm<G: CurveGroup<ScalarField = F>>(&self, bases: &[G::Affine]) -> G {
        let Self{mapping, image} = self;
        
        assert!(mapping.len() == bases.len());

        let zero = G::zero();
        let num_threads = rayon::current_num_threads();
        
        let chunks = split_into_chunks_balanced(bases, num_threads)
            .zip(split_into_chunks_balanced(mapping, num_threads))
            .collect::<Vec<_>>();

        let thread_buckets : Vec<_> = chunks
            .into_par_iter()
            .map(|(bases, mapping)| {
                let mut buckets = vec![zero; image.len()];
                for (base, counter) in bases.iter().zip(mapping.iter()) {
                    buckets[*counter] += base;
                }
                buckets
            }).collect();

        let mut buckets = vec![zero; image.len()];

        
        for i in 0..num_threads {
            let buckets_iter = buckets.par_iter_mut();
            buckets_iter.zip(thread_buckets[i].par_iter()).map(|(acc, inc)| *acc += inc).count();
        }
        
        G::msm_nonaff(&buckets, &self.image).unwrap()
    }
}

mod tests{
    #[allow(unused_imports)]
    use std::iter::repeat_with;
    #[allow(unused_imports)]
    use std::time::Instant;

    use ark_bls12_381::Fr;
    #[allow(unused_imports)]
    use ark_ec::{CurveGroup, VariableBaseMSM};
    use ark_ec::{bls12::Bls12, pairing::Pairing};
    #[allow(unused_imports)]
    use ark_std::UniformRand;
    #[allow(unused_imports)]
    use ark_std::rand::RngCore;

    #[allow(unused_imports)]
    use super::Pullback;

    #[allow(dead_code)]
    type G = <Bls12<ark_bls12_381::Config> as Pairing>::G1;
    #[allow(dead_code)]
    type F = Fr;

    #[test]
    fn test_bucketed_msm(){
        let mut rng = ark_std::test_rng();
        let mapping : Vec<_> = repeat_with(|| (rng.next_u32()%64) as usize).take(1024).collect();
        let image : Vec<_> = repeat_with(|| F::rand(&mut rng)).take(64).collect();
        let bases : Vec<_> = repeat_with(|| G::rand(&mut rng).into_affine()).take(1024).collect();

        let pullback = Pullback{mapping, image};

        let values = pullback.values();

        let t1 = Instant::now();
        let lhs = G::msm(&bases, &values);
        let t2 = Instant::now();
        let rhs = pullback.bucketed_msm::<G>(&bases);
        let t3 = Instant::now();

        println!("Non-bucketed msm of size 1024 took {}ms", (t2-t1).as_millis());
        println!("Same msm with 64 different values bucketed took {}ms.", (t3-t2).as_millis());

        assert_eq!(lhs.unwrap().into_affine(), rhs.into_affine());
    }

}