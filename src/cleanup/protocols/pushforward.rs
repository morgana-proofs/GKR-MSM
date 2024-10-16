use std::{cmp::min, iter::repeat_n, marker::PhantomData};
use ark_ff::PrimeField;
use hashcaster::ptr_utils::{AsSharedMutPtr, UnsafeIndexRawMut};
use itertools::Itertools;
use liblasso::poly::unipoly::UniPoly;
use rayon::{current_num_threads, iter::{repeatn, IndexedParallelIterator, IntoParallelIterator, ParallelIterator}, slice::{ParallelSlice, ParallelSliceMut}};

use crate::{cleanup::{proof_transcript::TProofTranscript2, protocol2::Protocol2}, polynomial::vecvec::VecVecPolynomial, protocol::sumcheckv2::Sumcheckable};

use super::sumcheck::{compress_coefficients, evaluate_poly, AlgFnSO, DenseSumcheckObjectSO, SinglePointClaims, SumClaim, SumcheckVerifierConfig};

#[derive(Clone)]
pub struct Prod3Fn<F: PrimeField> {
    _marker: PhantomData<F>
}

impl<F: PrimeField> Prod3Fn<F> {
    pub fn new() -> Self {
        Self { _marker: PhantomData }
    }
}

impl<F: PrimeField> AlgFnSO<F> for Prod3Fn<F> {
    fn exec(&self, args: &impl std::ops::Index<usize, Output = F>) -> F {
        args[0] * args[1] * args[2]
    }

    fn deg(&self) -> usize {
        3
    }

    fn n_ins(&self) -> usize {
        3
    }
}

// We need to figure out to generate these things in an optimized way and without too much copypasta.

/// This is a sumcheck object for sumcheck P(x) A(x, y) B(x, y). It treats y-s as lower coordinates, and sumchecks by them first.
/// Currently, it is implemented naively through dense sumcheck. An optimized implementation should be deployed later.
pub struct LayeredProd3SumcheckObject<F: PrimeField> {
    n_vars_x: usize,
    n_vars_y: usize,
    object: DenseSumcheckObjectSO<F, Prod3Fn<F>>,
}

impl<F: PrimeField> LayeredProd3SumcheckObject<F> {
    pub fn new(p: Vec<F>, a: Vec<F>, b: Vec<F>, n_vars_x: usize, n_vars_y: usize, claim_hint: F) -> Self {
        assert!(p.len() == 1 << n_vars_x);
        assert!(a.len() == 1 << (n_vars_x + n_vars_y));
        assert!(a.len() == b.len());
        let p = p.into_par_iter().map(|x| repeatn(x, 1 << n_vars_y)).flatten().collect();
        let f = Prod3Fn::new();
        let object = DenseSumcheckObjectSO::new(vec![p, a, b], f, n_vars_x + n_vars_y, claim_hint);
        Self { n_vars_x, n_vars_y, object }
    }
}

impl<F: PrimeField> Sumcheckable<F> for LayeredProd3SumcheckObject<F> {
    fn bind(&mut self, t: F) {
        self.object.bind(t);
    }

    fn unipoly(&mut self) -> UniPoly<F> {
        let mut u = self.object.unipoly().as_vec();
        if self.object.current_round() < self.n_vars_y {
            let s = u.pop().unwrap();
            assert!(s == F::zero());
        }
        UniPoly::from_coeff(u)
    }

    fn final_evals(&self) -> Vec<F> {
        self.object.final_evals()
    }

    fn challenges(&self) -> &[F] {
        self.object.challenges()
    }

    fn current_round(&self) -> usize {
        self.object.current_round()
    }
}

#[derive(Clone, Copy)]
pub struct LayeredProd3Protocol<F: PrimeField> {
    n_vars_x: usize,
    n_vars_y: usize,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> LayeredProd3Protocol<F> {
    pub fn new(n_vars_x: usize, n_vars_y: usize) -> Self {
        Self { n_vars_x, n_vars_y, _marker: PhantomData }
    }
}

#[derive(Clone)]
pub struct LayeredProd3ProtocolInput<F: PrimeField> {
    pub p: Vec<F>,
    pub a: Vec<F>,
    pub b: Vec<F>,
}


impl<T: TProofTranscript2, F: PrimeField> Protocol2<T> for LayeredProd3Protocol<F> {
    type ProverInput = LayeredProd3ProtocolInput<F>;

    type ProverOutput = ();

    type ClaimsBefore = SumClaim<F>;

    type ClaimsAfter = SinglePointClaims<F>;

    fn prove(&self, transcript: &mut T, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let mut claim = claims.sum;
        let mut object = LayeredProd3SumcheckObject::new(advice.p, advice.a, advice.b, self.n_vars_x, self.n_vars_y, claim);
        for i in 0 .. (self.n_vars_x + self.n_vars_y) {
            let u = object.unipoly().as_vec();
            transcript.write_scalars(&compress_coefficients(&u));
            let t = transcript.challenge(128);
            claim = evaluate_poly(&u, t);
            object.bind(t);
        }
        let evs = object.final_evals();
        let mut point = object.challenges().to_vec();
        point.reverse();

        transcript.write_scalars(&evs);
    
        (SinglePointClaims {point, evs}, ())
    }

    fn verify(&self, transcript: &mut T, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let degrees = repeat_n(2, self.n_vars_y).chain(repeat_n(3, self.n_vars_x)).collect_vec();

        let verifier = SumcheckVerifierConfig::new(degrees.into_iter());

        let (final_claim, point) = verifier.main_cycle_sumcheck_verifier(transcript, claims.sum);

        let evs = transcript.read_scalars(3);

        assert!(evs[0] * evs[1] * evs[2] == final_claim);

        SinglePointClaims {point, evs}
    }
}

// assumes that digits are in range (1 << c).
pub fn compute_bucketing_image<F: PrimeField>(
    polys: Vec<Vec<F>>,
    digits: Vec<Vec<u32>>,
    c: usize,
    n_vars_x: usize,
    n_vars_y: usize,
    size_x: usize,
    size_y: usize,

    row_pad: Vec<F>,
    col_pad: Vec<F>,
) -> Vec<VecVecPolynomial<F>> {    
    for poly in &polys {
        assert!(poly.len() == size_x);
    }

    assert!(row_pad.len() == polys.len());
    assert!(col_pad.len() == polys.len());

    assert!(digits.len() == size_y);
    for row in &digits {
        assert!(row.len() == size_x);
    }

    assert!(1 << n_vars_x >= size_x);
    assert!(1 << n_vars_y >= size_y);

    let n_tasks = current_num_threads();
    let height = size_y / n_tasks; 
    
    let mut buckets : Vec<Vec<Vec<F>>> = vec![vec![vec![]; size_y << c]; polys.len()];

    let mut buckets_ptrs = buckets.iter_mut().map(|b|b.as_shared_mut_ptr()).collect_vec();

    let buckets_ptr = buckets_ptrs.as_shared_mut_ptr();
    
    (0..n_tasks).into_par_iter().map(|task_idx|{
        (task_idx * height .. min((task_idx + 1) * height, size_y)).map(|y| {
            for id_p in 0..polys.len() {
                for x in 0..size_x {
                    unsafe{
                        let b = buckets_ptr.clone();
                        let b2 = b.get_mut(id_p);
                        (b2.clone().get_mut((y << c) + digits[y][x] as usize)).push(polys[id_p][x])
                    }
                }
            }
        })
    }).count();


    buckets.into_iter().enumerate().map(|(i, buckets)| VecVecPolynomial::new(buckets, row_pad[i], col_pad[i], n_vars_x, n_vars_y)).collect_vec()

}


#[cfg(test)]
mod tests {
    use ark_bls12_381::{G1Affine, G1Projective, g1::Config};
    use ark_ec::{CurveConfig, Group};
    use ark_std::{test_rng, UniformRand, Zero, One};
    use ark_ff::Field;
    use itertools::Itertools;
    use liblasso::{poly::eq_poly::{self, EqPolynomial}, utils::transcript};
    use crate::cleanup::proof_transcript::ProofTranscript2;

    use super::*;

    type Fr = <Config as CurveConfig>::ScalarField;

    #[test]
    fn layered_prod3_verifies() {
        // currently this test does nothing, as layered3 actually IS naive implementation
        let rng = &mut test_rng();

        let n_vars_x = 3;
        let n_vars_y = 4;

        let p = (0 .. 1 << n_vars_x).map(|_| Fr::rand(rng)).collect_vec();
        let a = (0 .. 1 << (n_vars_x + n_vars_y)).map(|_| Fr::rand(rng)).collect_vec();
        let b = (0 .. 1 << (n_vars_x + n_vars_y)).map(|_| Fr::rand(rng)).collect_vec();

        let mut claim_hint = Fr::zero();

        for i in 0 .. (1 << n_vars_x) {
            for j in 0 .. (1 << n_vars_y) {
                claim_hint += p[i] * a[(i << n_vars_y) + j] * b[(i << n_vars_y) + j]
            }
        }

        let protocol = LayeredProd3Protocol::new(n_vars_x, n_vars_y);

        let mut transcript = ProofTranscript2::start_prover(b"meow");

        let output = protocol.prove(&mut transcript, SumClaim { sum : claim_hint }, LayeredProd3ProtocolInput { p, a, b } ).0;

        let proof = transcript.end();

        let mut transcript = ProofTranscript2::start_verifier(b"meow", proof);

        let output2 = protocol.verify(&mut transcript, SumClaim { sum : claim_hint });

        assert_eq!(output, output2);
    }
}
