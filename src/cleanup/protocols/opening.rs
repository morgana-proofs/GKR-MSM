// This file re-implements Knuckles opening with our new Protocol API (not that it actually needs global Fiat-Shamir, but it is easier to express it
// this way),

use ark_ec::pairing::Pairing;
use ark_ff::Field;
use num_traits::{Zero, One};
use rayon::prelude::*;
use crate::{cleanup::{proof_transcript::TProofTranscript2, protocol2::Protocol2}, commitments::{knuckles::{KnucklesProvingKey, KnucklesVerifyingKey}, kzg::ev}};

#[derive(Clone)]
pub struct KnucklesOpeningProtocol<Ctx: Pairing> {
    pk: Option<KnucklesProvingKey<Ctx>>, // optional because verifier does not need it
    vk: KnucklesVerifyingKey<Ctx>,
}

impl<Ctx: Pairing> KnucklesOpeningProtocol<Ctx> {
    pub fn new(vk: KnucklesVerifyingKey<Ctx>, pk: Option<KnucklesProvingKey<Ctx>>) -> Self {
        Self { pk, vk }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct OpeningClaim<Ctx: Pairing> {
    pub commitment: Ctx::G1Affine,
    pub point: Vec<Ctx::ScalarField>,
    pub ev: Ctx::ScalarField,
}

impl<Ctx: Pairing, Transcript: TProofTranscript2> Protocol2<Transcript> for KnucklesOpeningProtocol<Ctx> {
    type ProverInput = Vec<Ctx::ScalarField>; // Hints the polynomial to prover

    type ProverOutput = ();

    type ClaimsBefore = OpeningClaim<Ctx>;

    type ClaimsAfter = (Ctx::G1Affine, Ctx::G1Affine); // Deferred pair (A, B) satisfying <A, H0> = <B, H1>.

    fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        transcript.record_current_time(">> OPENING");

        let pk = self.pk.as_ref().unwrap();
        
        let a = pk.compute_t(&advice, &claims.point);
        
        transcript.record_current_time(">> OPENING: compute T");
        
        let (t, opening) = a;
        assert!(opening == claims.ev);
        let t_comm = pk.kzg_pk.commit(&t);
        
        transcript.record_current_time(">> OPENING: commit T");
        
        transcript.write_points::<Ctx::G1>(&[t_comm]);
        let x = transcript.challenge(128);

        let kx = x * pk.k;
        let t_x = ev(&t, x);
        let p_x = ev(&advice, x);

        transcript.write_scalars(&[t_x, p_x]);

        let lambda : Ctx::ScalarField = transcript.challenge(128);

        let poly_iter_padded = advice
                                .par_iter()
                                .map(|x|*x)
                                .chain(
                                    rayon::iter::repeat(Ctx::ScalarField::zero()).take(t.len() - advice.len())
                                );

        let p_lt : Vec<_> = poly_iter_padded
                        .zip(t.par_iter())
                        .map(|(a, b)| lambda * b + a)
                        .collect();
        
        let (p_lt_x_proof, _) = pk.kzg_pk.open(&p_lt, x);
        
        transcript.record_current_time(">> OPENING: kzg open p_lt in x");
        
        transcript.write_points::<Ctx::G1>(&[p_lt_x_proof]);

        let (t_kx_proof, t_kx) = pk.kzg_pk.open(&t, kx);

        transcript.record_current_time(">> OPENING: kzg open p in kx");

        transcript.write_scalars(&[t_kx]);
        transcript.write_points::<Ctx::G1>(&[t_kx_proof]);

        let fin = transcript.challenge::<Ctx::ScalarField>(128);


        let p_lt_comm = t_comm * lambda + claims.commitment;
        let p_lt_open = t_x * lambda + p_x;
        let (a0, b0) = self.vk.kzg_vk.verify_reduce_to_pair(p_lt_comm, p_lt_x_proof, x, p_lt_open);
        let (a1, b1) = self.vk.kzg_vk.verify_reduce_to_pair(t_comm, t_kx_proof, kx, t_kx);
        (((a0 + a1 * fin).into(), (b0 + b1 * fin).into()), ())
    }

    fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let vk = &self.vk;
        
        let t_comm = transcript.read_points::<Ctx::G1>(1)[0];
        let x = transcript.challenge(128);

        let kx = x * vk.k;
        let [t_x, p_x] = transcript.read_scalars::<Ctx::ScalarField>(2).try_into().unwrap();
        let lambda : Ctx::ScalarField = transcript.challenge(128);

        let p_lt_comm = t_comm * lambda + claims.commitment;
        let p_lt_open = t_x * lambda + p_x;

        let p_lt_x_proof = transcript.read_points::<Ctx::G1>(1)[0];

        let (a0, b0) = vk.kzg_vk.verify_reduce_to_pair(p_lt_comm, p_lt_x_proof, x, p_lt_open);

        let t_kx = transcript.read_scalars(1)[0];
        let t_kx_proof = transcript.read_points::<Ctx::G1>(1)[0];

        let (a1, b1) = vk.kzg_vk.verify_reduce_to_pair(t_comm, t_kx_proof, kx, t_kx);

        let k_pow_n_1 = vk.k.pow([(1 << vk.num_vars) - 1]); // Can  be precomputed if necessary.

        let mut xpow = x;
        let eq_ev = (0..vk.num_vars).map(|i| {
            let r = claims.point[vk.num_vars - i - 1];
            let ret = r + (Ctx::ScalarField::one() - r) * xpow;
            xpow *= xpow;
            ret
        }).fold(Ctx::ScalarField::one(), |a, b| a*b);
        
        let x_pow_n = xpow;

        let lhs = x * (t_kx - k_pow_n_1 * t_x) + x_pow_n * claims.ev; // x(T(kx) - k^{N-1} T(x) + x^{N-1} * claim)
        
        let rhs = x * p_x * eq_ev; // x * P(x) Eq_point (x)
        assert!(lhs == rhs);
        let fin = transcript.challenge::<Ctx::ScalarField>(128);
        ((a0 + a1 * fin).into(), (b0 + b1 * fin).into())
    }
}

#[cfg(test)]
mod tests {
    use std::iter::repeat_with;

    use ark_bls12_381::Bls12_381 as Ctx;
    use ark_bls12_381::Fr;
    use ark_ff::{Field, PrimeField};
    use ark_std::{test_rng, UniformRand};

    use crate::cleanup::proof_transcript::ProofTranscript2;
    use crate::cleanup::protocols::verifier_polys::{EqPoly, VerifierPoly};
    use crate::commitments::kzg::{ev, random_kzg_pk};
    use crate::commitments::kzg::KzgProvingKey;

    use super::*;

    #[test]
    fn knuckles_prove_and_verify () {
        let rng = &mut test_rng();
        let k = Fr::from(2);
        let num_vars = 10;
        let poly_size = 719;
        let kzg_pk : KzgProvingKey<Ctx>  = random_kzg_pk(2*(1 << num_vars) - 1, rng);
        let pk = KnucklesProvingKey::new(kzg_pk, num_vars, k);
        let vk = pk.verifying_key();

        let poly : Vec<_> = repeat_with(||Fr::rand(rng)).take(poly_size).collect();
        let pt : Vec<_> = repeat_with(||Fr::rand(rng)).take(num_vars).collect();
        
        let e_p = EqPoly::new(num_vars,&pt);
        let ev = poly.iter().zip(e_p.evals().iter()).map(|(&a, b)| a * b).sum::<Fr>(); // evaluate 0-padded

        let commitment = pk.commit(&poly);

        let mut p_transcript = ProofTranscript2::start_prover(b"knucklestest");

        let knuckles_opening_prover = KnucklesOpeningProtocol::new(vk, Some(pk));

        let claims = OpeningClaim{ commitment, point: pt, ev };
        let (pair, _) = knuckles_opening_prover.prove(&mut p_transcript, claims.clone(), poly);
        let proof = p_transcript.end();

        let mut v_transcript = ProofTranscript2::start_verifier(b"knucklestest", proof);

        let knuckles_opening_verifier = KnucklesOpeningProtocol::new(vk, None);

        let pair2 = knuckles_opening_verifier.verify(&mut v_transcript, claims);

        assert!(pair == pair2);

        vk.kzg_vk.verify_pair(pair);

    }



}