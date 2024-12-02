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
use ark_ff::{batch_inversion, Field};


use crate::{commitments::kzg::ev, transcript::{TranscriptReceiver, TranscriptSender}};
use rayon::prelude::*;

use super::kzg::{KzgProvingKey, KzgVerifyingKey};
use ark_std::{Zero, One};

#[derive(Clone)]
pub struct KnucklesProvingKey<Ctx: Pairing> {
    kzg_pk: KzgProvingKey<Ctx>,
    num_vars: usize, // N = 2^num_vars, kzg_pk must have size at least 2N.
    k: Ctx::ScalarField, // Taking k = 2 should work in most cases.
    inverses: Vec<Ctx::ScalarField> // Precomputed inverses of (k^s - k^N), except for s = N (where it can be anything).
}

#[derive(Clone)]
pub struct KnucklesProof<Ctx: Pairing> {
    pub t_comm: Ctx::G1Affine,
    pub t_x: Ctx::ScalarField,
    pub p_x: Ctx::ScalarField,
    pub p_lt_x_proof: Ctx::G1Affine,
    pub t_kx: Ctx::ScalarField,
    pub t_kx_proof: Ctx::G1Affine,

}

impl<Ctx: Pairing> KnucklesProvingKey<Ctx> {
    pub fn new(kzg_pk: KzgProvingKey<Ctx>, num_vars: usize, k: Ctx::ScalarField) -> Self {
        let n = 1 << num_vars;
        assert!(kzg_pk.ptau_1().len() >= 2 * n - 1, "SRS is too short.");
        let mut k_pows = Vec::<Ctx::ScalarField>::with_capacity(2 * n - 1);
        let mut power = Ctx::ScalarField::one();
        for _ in 0..2 * n - 1 {
            k_pows.push(power);
            power *= k;
        };
        let k_n = k_pows[n -1];

        (&mut k_pows).par_iter_mut().map(|x| *x -= k_n ).count();
        k_pows[n - 1] += Ctx::ScalarField::one(); // so inversion doesn't fail
        batch_inversion(&mut k_pows);

        Self { kzg_pk, num_vars, k, inverses: k_pows }
    }

    pub fn num_vars(&self) -> usize {
        self.num_vars
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
        assert!(poly.len() <= 1 << self.num_vars);
        self.kzg_pk.commit(poly)
    }

    pub fn kzg_basis(&self) -> &[Ctx::G1Affine] {
        self.kzg_pk.ptau_1()
    }

    /// Returns polynomial T and an opening c, such that T(kx) - k^{N-1}T(x) + c = P(x)E_r(x)
    /// This equation then can be checked by normal KZG means.
    pub fn compute_t(&self, poly: &[Ctx::ScalarField], point: &[Ctx::ScalarField]) -> (Vec<Ctx::ScalarField>, Ctx::ScalarField) {
        assert_eq!(point.len(), self.num_vars);
        
        let mut pt = point.to_vec();
        pt.reverse(); // To keep on parity with liblasso's ordering.
        
        let n = 1 << self.num_vars;
        assert_eq!(poly.len(), n);
        let mut t : Vec<Ctx::ScalarField> = Vec::with_capacity(2 * n - 1);
        let mut t_scaled = vec![Ctx::ScalarField::zero(); 2 * n - 1];

        let pt_rev : Vec<_> = pt.par_iter().map(|x| Ctx::ScalarField::one() - *x).collect();
        // It is more convenient to multiply by 1-pt.

        t.extend(poly);
        t.extend(std::iter::repeat(Ctx::ScalarField::zero()).take(n - 1));

        let mut curr_size = n; // This will hold the size of our data
        for i in 0..self.num_vars {
            t_scaled[0..curr_size]
                .par_iter_mut()
                .enumerate()
                .map(|(idx, x)| *x = t[idx] * pt_rev[i]).count();
            
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

        let opening = t[n - 1];
        t[n - 1] = Ctx::ScalarField::zero();

        t.par_iter_mut()
            .enumerate()
            .map(|(idx, x)| *x *= self.inverses[idx]).count();
        (t, opening)
    }

    /// Creates Knuckles proof. Takes as an input a polynomial, a point to open, and an opening.
    /// All three must be already committed to the transcript, or derived deterministically from other
    /// prover messages. (we do not add them to transcript manually to accomodate for possibility
    /// of the commitment being derived as linear combination of other commitments).
    /// This is somewhat similar to our protocol API, with commitment having a role of a "claim",
    /// though we do not implement it for now.
    pub fn prove<
        T: TranscriptReceiver<Ctx::ScalarField>
          + TranscriptSender<Ctx::ScalarField>>(
            &self,
            poly: &[Ctx::ScalarField],
            point: &[Ctx::ScalarField],
            claimed_opening: Ctx::ScalarField,
            transcript: &mut T,
          ) -> KnucklesProof<Ctx> {
            let a = self.compute_t(poly, point);
            let (t, opening) = a;
            assert!(opening == claimed_opening, "Incorrect opening claim.");
            let t_comm = self.kzg_pk.commit(&t);
            transcript.append_point::<Ctx::G1>(b"T commitment", t_comm);
            let x = transcript.challenge_scalar(b"x opening point").value;

            let kx = x * self.k;
            let t_x = ev(&t, x);
            let p_x = ev(&poly, x);

            transcript.append_scalar(b"T(x) claim", &t_x);
            transcript.append_scalar(b"P(x) claim", &p_x);

            let lambda = transcript.challenge_scalar(b"Lambda challenge").value;

            let poly_iter_padded = poly
                                    .par_iter()
                                    .map(|x|*x)
                                    .chain(
                                        rayon::iter::repeat(Ctx::ScalarField::zero()).take(t.len()-poly.len())
                                    );

            let p_lt : Vec<_> = poly_iter_padded
                            .zip(t.par_iter())
                            .map(|(a, b)| lambda * b + a)
                            .collect();
            
            let (p_lt_x_proof, _) = self.kzg_pk.open(&p_lt, x);
            transcript.append_point::<Ctx::G1>(b"(P + l T)(x) proof", p_lt_x_proof); // probably unnecessary. will do it anyway

            let (t_kx_proof, t_kx) = self.kzg_pk.open(&t, kx);

            transcript.append_scalar(b"T(kx) claim", &t_kx);
            transcript.append_point::<Ctx::G1>(b"T(kx) proof", t_kx_proof);

            // We are adding these challenges to transcript so that verifier can sample randomness for
            // proof combination for it. (otherwise, it would not be necessary, as we are not making new claims
            // - but if we want verifier's randomness for final check to be deterministic, it should be done).
            
            let _ = transcript.challenge_scalar(b"Final combinator").value;

            KnucklesProof{ t_comm, t_x, p_x, p_lt_x_proof, t_kx, t_kx_proof }

        }
}

#[derive(Clone)]
pub struct KnucklesVerifyingKey<Ctx: Pairing> {
    kzg_vk: KzgVerifyingKey<Ctx>,
    num_vars: usize,
    k: Ctx::ScalarField, 
}

impl<Ctx: Pairing> KnucklesVerifyingKey<Ctx> {
    
    /// Reduces a proof to deferred pair (a, b), allegedly satisfying <a, h0> == <b, h1>.
    /// poly_comm, point and opening MUST already be in transcript (they are not added
    /// to give user opportunity to derive them deterministically from other components of the protocol).
    /// This is in line with our general convention of ClaimsToReduce being added to transcript outside
    /// of the function.
    pub fn verify_reduce_to_pair<
        T: TranscriptReceiver<Ctx::ScalarField>
           + TranscriptSender<Ctx::ScalarField>   
    > (
        &self,
        poly_comm: Ctx::G1Affine,
        point: &[Ctx::ScalarField],
        claimed_opening: Ctx::ScalarField,
        proof: KnucklesProof<Ctx>,
        transcript: &mut T,
    ) -> (Ctx::G1Affine, Ctx::G1Affine) {
        let KnucklesProof { t_comm, t_x, p_x, p_lt_x_proof, t_kx, t_kx_proof } = proof;
        transcript.append_point::<Ctx::G1>(b"T commitment", t_comm);
        let x = transcript.challenge_scalar(b"x opening point").value;

        let kx = x * self.k;
        transcript.append_scalar(b"T(x) claim", &t_x);
        transcript.append_scalar(b"P(x) claim", &p_x);
        let lambda = transcript.challenge_scalar(b"Lambda challenge").value;

        let p_lt_comm = t_comm * lambda + poly_comm;
        let p_lt_open = t_x * lambda + p_x;

        let (a0, b0) = self.kzg_vk.verify_reduce_to_pair(p_lt_comm, p_lt_x_proof, x, p_lt_open);

        transcript.append_point::<Ctx::G1>(b"(P + l T)(x) proof", p_lt_x_proof); 

        let (a1, b1) = self.kzg_vk.verify_reduce_to_pair(t_comm, t_kx_proof, kx, t_kx);

        transcript.append_scalar(b"T(kx) claim", &t_kx);
        transcript.append_point::<Ctx::G1>(b"T(kx) proof", t_kx_proof);

        let k_pow_n_1 = self.k.pow([(1 << self.num_vars) - 1]); // Can  be precomputed if necessary.

        let mut xpow = x;
        let eq_ev = (0..self.num_vars).map(|i| {
            let r = point[self.num_vars - i - 1];
            let ret = r + (Ctx::ScalarField::one() - r) * xpow;
            xpow *= xpow;
            ret
        }).fold(Ctx::ScalarField::one(), |a, b| a*b);
        
        let x_pow_n = xpow;

        let lhs = x * (t_kx - k_pow_n_1 * t_x) + x_pow_n * claimed_opening; // x(T(kx) - k^{N-1} T(x) + x^{N-1} * claim)
        
        let rhs = x * p_x * eq_ev; // x * P(x) Eq_point (x)


        assert!(lhs == rhs);

        let fin = transcript.challenge_scalar(b"Final combinator").value;

        ((a0 + a1 * fin).into(), (b0 + b1 * fin).into())

    }

    pub fn verify_directly<
        T: TranscriptReceiver<Ctx::ScalarField>
         + TranscriptSender<Ctx::ScalarField>   
    > (
        &self,
        poly_comm: Ctx::G1Affine,
        point: &[Ctx::ScalarField],
        claimed_opening: Ctx::ScalarField,
        proof: KnucklesProof<Ctx>,
        transcript: &mut T,
    ) -> () {
        let pair = self.verify_reduce_to_pair(poly_comm, point, claimed_opening, proof, transcript);
        self.kzg_vk.verify_pair(pair);
    }
}





#[cfg(test)]
mod tests {
    use std::iter::repeat_with;

    use ark_bls12_381::Bls12_381 as Ctx;
    use ark_bls12_381::Fr;
    use ark_ff::{Field, PrimeField};
    use ark_std::{test_rng, UniformRand};
    use liblasso::poly::dense_mlpoly::DensePolynomial;
    use merlin::Transcript;

    use crate::commitments::kzg::{ev, random_kzg_pk};
    use crate::commitments::kzg::KzgProvingKey;

    use super::*;

    #[test]
    fn knuckles_prove_and_verify () {
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


        let mut p_transcript = Transcript::new(b"test knuckles") ;
        let poly_comm = knuckles_pk.commit(&poly);
        <Transcript as TranscriptReceiver<<Ctx as Pairing>::ScalarField>>::append_point::<<Ctx as Pairing>::G1>(&mut p_transcript, b"poly_comm", poly_comm);
        p_transcript.append_scalar(b"opening claim", &opening);

        let proof = knuckles_pk.prove(&poly, &point, opening, &mut p_transcript);
        
        drop(p_transcript);
        
        let knuckles_vk = knuckles_pk.verifying_key();

        let mut v_transcript = Transcript::new(b"test knuckles") ;
        <Transcript as TranscriptReceiver<<Ctx as Pairing>::ScalarField>>::append_point::<<Ctx as Pairing>::G1>(&mut v_transcript, b"poly_comm", poly_comm);
        v_transcript.append_scalar(b"opening claim", &opening);

        knuckles_vk.verify_directly(poly_comm, &point, opening, proof, &mut v_transcript);

    }

}