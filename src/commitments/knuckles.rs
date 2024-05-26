// This is a non-hiding implementation of coboundary-based multivariate opening scheme.
// It is different (while inspired by) the coboundary univariate sumcheck trick from Marlin,
// and somewhat similar to Sonic because it also commits in coefficient form, and reduces
// inner product to the fact that a single coefficient of certain product vanishes.

// Approach:

// Note, that for vectors a, b, for polynomials
// A(x) = \sum_i a_i x^i     and     B(x) = \sum_i b_i x^{N-1-i}
// the product AB has (N-1)-th coefficient \sum_i a_i b_i

// For a multilinear polynomial, and opening point r, we use its representation P(x) = \sum p_i x^i,
// where p_i is evaluation of original polynomial in vertex(i).

// Reverted evaluations of eq(r, _) can be then expressed in a following closed form:
// (r_0 + (1 - r_0) x)*(r_1 + (1 - r_1) x^2)*(r_2 + (1 - r_2) x^4) ..., i.e.
// E(x) = prod_i (r_i + (1 - r_i) x^{2^i})

// We will commit to A(x)E(x), and then use the following argument (inspired by cohomological sumcheck of Marlin):

// Lemma: assume that multiplicative order of some constant k is > M. Then, polynomial S(x) of degree M has N-th
// coefficient = 0 if and only if S(x) = T(k*x) - k^N T(x) for some polynomial T.

// Proof: clearly, mapping T(x) -> T(kx) - k^N T(x) acts diagonally on coefficients, and multiplies each coefficient
// but N-th by nonzero element (k^s - k^N).

// So, full protocol is as follows: given commitment to A, opening point r, and evaluation claim c,
// we commit to T(x) such that T(kx) - k^(N-1)T(x) + c x^{N-1} = A(x)E_r(x)

// Then, we sample random s, and batch-open T in ks, s, and A in s
// Shplonk tricks are sadly almost useless here, because there are only 2 points to open.

use std::fs::File;

use ark_ec::pairing::Pairing;
use ark_ff::batch_inversion;
use rayon::iter::IntoParallelRefMutIterator;
use rayon::iter::ParallelIterator;
use rayon::iter::IntoParallelIterator;
use rayon::iter::IndexedParallelIterator;
use super::kzg::{KzgProvingKey, KzgVerifyingKey};
use ark_std::{Zero, One};
use ark_std::iter::repeat;

#[derive(Clone)]
pub struct KnucklesProvingKey<Ctx: Pairing> {
    kzg_pk: KzgProvingKey<Ctx>,
    num_vars: usize, // N = 2^num_vars, kzg_pk must have size at least 2N.
    k: Ctx::ScalarField, // Taking k = 2 should work in most cases.
    inverses: Vec<Ctx::ScalarField> // Precomputed inverses of (k^s - k^N), except for s = N (where it can be anything).
}

impl<Ctx: Pairing> KnucklesProvingKey<Ctx> {
    pub fn new(kzg_pk: KzgProvingKey<Ctx>, num_vars: usize, k: Ctx::ScalarField) -> Self {
        let N = (1 << num_vars);
        assert!(kzg_pk.ptau_1().len() >= 2*N - 1, "SRS is too short.");
        let mut k_pows = Vec::with_capacity(2*N - 1);
        let mut power = Ctx::ScalarField::one();
        for _ in 0..2*N - 1 {
            k_pows.push(power);
            power *= k;
        };
        let k_n = k_pows[N-1];

        (&mut k_pows).par_iter_mut().map(|x| *x -= k_n ).count();
        k_pows[N-1] += Ctx::ScalarField::one(); // so inversion doesn't fail
        batch_inversion(&mut k_pows);

        Self { kzg_pk, num_vars, k, inverses: k_pows }
    }

    pub fn load(file: &mut File) -> Self {
        todo!()
    }

    pub fn dump(&self, file: &mut File) {
        todo!()
    }

    pub fn verifying_key(&self) -> KnucklesVerifyingKey<Ctx> {
        let kzg_vk = self.kzg_pk.verifying_key();
        KnucklesVerifyingKey { kzg_vk, num_vars: self.num_vars, k: self.k }
    }

    pub fn commit(&self, poly: &[Ctx::ScalarField]) -> Ctx::G1Affine {
        assert!(poly.len() == 1 << self.num_vars);
        self.kzg_pk.commit(poly)
    }

    /// Returns polynomial T and an opening c, such that T(kx) - k^{N-1}T(x) + c = P(x)E_r(x)
    /// This equation then can be checked by normal KZG means.
    pub fn compute_t(&self, poly: &[Ctx::ScalarField], point: &[Ctx::ScalarField]) -> (Vec<Ctx::ScalarField>, Ctx::ScalarField) {
        assert!(point.len() == self.num_vars);
        
        let mut pt = point.to_vec();
        pt.reverse(); // To keep on parity with liblasso's ordering.
        
        let N = 1 << self.num_vars;
        assert!(poly.len() == N);
        let mut t = Vec::<Ctx::ScalarField>::with_capacity(2*N - 1);
        let mut t_scaled = vec![Ctx::ScalarField::zero(); 2*N - 1];

        let pt_rev : Vec<_> = pt.iter().map(|x| Ctx::ScalarField::one() - *x).collect();
        // It is more convenient to multiply by 1-pt.

        t.extend(poly);
        t.extend(repeat(Ctx::ScalarField::zero()).take(N-1));

        let mut curr_size = N; // This will hold the size of our data 
        for i in 0..self.num_vars {
            t_scaled[0..curr_size].par_iter_mut().enumerate().map(|(idx, x)| *x = t[idx] * pt_rev[i]).count();
            
            let offset = 1 << i;
            curr_size += offset;
            t[0..curr_size].par_iter_mut().enumerate().map(|(idx, x)| {
                if idx < offset {
                    *x -= t_scaled[idx]; // x -= x*pt_rev[i], which is x -= (1-pt[i])x, which is x = pt[i] x 
                } else {
                    *x -= t_scaled[idx];
                    *x += t_scaled[idx - offset]; 
                }
            }).count();
        }

        let opening = t[N-1];
        t[N-1] = Ctx::ScalarField::zero();
        t.par_iter_mut().enumerate().map(|(idx, x)| *x *= self.inverses[idx]).count();
        (t, opening)
    }

}

#[derive(Clone)]
pub struct KnucklesVerifyingKey<Ctx: Pairing> {
    kzg_vk: KzgVerifyingKey<Ctx>,
    num_vars: usize,
    k: Ctx::ScalarField, 
}


#[cfg(test)]
mod tests {
    use std::iter::repeat_with;

    use ark_ff::{Field};
    use ark_bls12_381::Bls12_381 as Ctx;
    use ark_bls12_381::Fr;
    use ark_std::{test_rng, UniformRand};
    use liblasso::poly::dense_mlpoly::DensePolynomial;

    use crate::commitments::kzg::{random_kzg_pk, ev};
    use crate::commitments::kzg::KzgProvingKey;

    use super::*;

    #[test]
    fn knuckles_t () {
        let rng = &mut test_rng();
        let k = Fr::from(2);
        let num_vars = 10;
        let N = 1 << num_vars;
        let kzg_pk : KzgProvingKey<Ctx>  = random_kzg_pk(2*N - 1, rng);
        let knuckles_pk = KnucklesProvingKey::new(kzg_pk, num_vars, k);

        let poly : Vec<_> = repeat_with(||Fr::rand(rng)).take(1 << num_vars).collect();
        let point : Vec<_> = repeat_with(||Fr::rand(rng)).take(num_vars).collect();
        
        let (t, opening) = knuckles_pk.compute_t(&poly, &point);

        let legacy_poly = DensePolynomial::new(poly.clone());
        assert!(legacy_poly.evaluate(&point) == opening); // Check that opening is correct.

        let x = Fr::rand(rng);

        let lhs = ev(&t, x*k) - k.pow([(N-1) as u64]) * ev(&t, x) + opening * x.pow([(N-1) as u64]);
        
        let mut xpow = x;
        let eq_ev = (0..num_vars).map(|i| {
            let r = point[num_vars - i - 1];
            let ret = r + (Fr::one() - r) * xpow;
            xpow *= xpow;
            ret
        }).fold(Fr::one(), |a, b| a*b);

        let rhs = ev(&poly, x) * eq_ev;

        assert!(lhs == rhs);
    }
}