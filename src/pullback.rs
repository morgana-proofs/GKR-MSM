use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use liblasso::poly::dense_mlpoly::DensePolynomial;
use crate::msm_nonaffine::VariableBaseMSM_Nonaffine;

/// This structure hosts a counter c, an array a,
/// and represents a pullback, i.e. a table
/// (c* a)[i] = a[c[i]]
pub struct Pullback<F: PrimeField> {
    pub mapping: Vec<usize>,
    pub image: Vec<F>,
}

impl<F: PrimeField> Pullback<F> {

    /// Computes the pullback.
    pub fn values(&self) -> Vec<F> {
        self.mapping.iter().map(|i|self.image[*i]).collect()
    }

    /// Computes pullback's MSM by first aggregating repeated elements, and then doing normal MSM.
    pub fn bucketed_msm<G: CurveGroup<ScalarField = F>>(&self, bases: &[G::MulBase]) -> G {
        let zero = G::zero();
        let mut buckets = vec![zero; self.image.len()];
        for (i, counter) in self.mapping.iter().enumerate() {
            buckets[*counter] += bases[i];
        }
        G::msm_nonaff(&buckets, &self.image).unwrap()
    }
}

mod tests{
    use std::iter::repeat_with;

    use super::*;
    use ark_bls12_381::Fr;
    use ark_ec::{bls12::{self, Bls12}, pairing::Pairing, short_weierstrass::Affine, CurveGroup};
    use ark_ff::UniformRand;
    use ark_std::rand::RngCore;
    use liblasso::msm::VariableBaseMSM;

    type G = <Bls12<ark_bls12_381::Config> as Pairing>::G1;
    type F = Fr;

    #[test]
    fn test_bucketed_msm(){
        let mut rng = ark_std::test_rng();
        let mapping : Vec<_> = repeat_with(|| (rng.next_u32()%64) as usize).take(1024).collect();
        let image : Vec<_> = repeat_with(|| F::rand(&mut rng)).take(64).collect();
        let bases : Vec<_> = repeat_with(|| G::rand(&mut rng).into_affine()).take(1024).collect();

        let pullback = Pullback{mapping, image};

        let values = pullback.values();

        let lhs = G::msm(&bases, &values);
        let rhs = pullback.bucketed_msm::<G>(&bases);

        assert!(lhs.unwrap() == rhs);
    }

}