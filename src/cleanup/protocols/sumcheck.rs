use std::{cmp::min, iter::repeat, marker::PhantomData, ops::Index, process::Output, ptr};

use ark_ff::PrimeField;
use bytemuck::cast_slice_mut;
use hashcaster::ptr_utils::{AsSharedMutPtr, UnsafeIndexRaw, UnsafeIndexRawMut};
use itertools::Itertools;
use liblasso::poly::unipoly::UniPoly;
use rayon::{current_num_threads, current_thread_index, iter::{Fold, IntoParallelIterator, ParallelIterator}};
use crate::{cleanup::{proof_transcript::{TProverTranscript, TVerifierTranscript}, protocol2::Protocol2}, protocol::sumcheckv2::Sumcheckable};


/// Given polynomial in coefficient form with linear term skipped, and sum P(0) + P(1), recovers full polynomial.
pub fn decompress_coefficients<F: PrimeField>(coeffs_wo_lin_term: &[F], sum: F) -> Vec<F> {
    let l = coeffs_wo_lin_term.len();
    let mut sum_minus_lterm = coeffs_wo_lin_term[0].double();
    for i in 1..l {
        sum_minus_lterm += coeffs_wo_lin_term[i];
    }
    let mut ret = Vec::with_capacity(l+1);
    ret.push(coeffs_wo_lin_term[0]);
    ret.push(sum - sum_minus_lterm);
    ret.extend_from_slice(&coeffs_wo_lin_term[1..]);
    ret
}

pub fn compress_coefficients<F: PrimeField>(coeffs: &[F]) -> Vec<F> {
    let mut ret = coeffs.to_vec();
    ret.remove(1);
    ret
}

pub fn evaluate_poly<F: PrimeField>(coeffs: &[F], x: F) -> F {
    let l = coeffs.len();
    if l == 0 {return F::zero()}
    let mut ret = coeffs[l-1];

    for i in 0..l-1 {
        ret *= x;
        ret += coeffs[l-2-i];
    }

    ret
}


/// A standard sumcheck verifier. To obtain real verifier, one needs to append it with combinator, and prepend (potentially) with folding round.
#[derive(Clone)]
pub struct SumcheckVerifierConfig<I: ExactSizeIterator<Item = usize> + Clone + Send + Sync> {
    pub degrees: I,
}

impl<I: ExactSizeIterator<Item = usize> + Clone + Send + Sync> SumcheckVerifierConfig<I> {

    pub fn new(degrees: impl IntoIterator<IntoIter = I>) -> Self {
        Self { degrees : degrees.into_iter() }
    }

    pub fn num_vars(&self) -> usize {
        self.degrees.len()
    }

    pub fn main_cycle_sumcheck_verifier<PT: TVerifierTranscript, F: PrimeField>(&self, transcript: &mut PT, sum_claim: F) -> (F, Vec<F>) {
        let degrees = self.degrees.clone().into_iter();
        let mut claim = sum_claim;
        let mut r = Vec::with_capacity(self.degrees.len());
        for d in degrees {
            let msg = transcript.read_scalars(d); // polynomial of degree d has d+1 coefficient, but the linear term is ignored
            let poly = decompress_coefficients(&msg, claim);

            let x = transcript.challenge(128);
            r.push(x);
            claim = evaluate_poly(&poly, x);
        }
        r.reverse();
        (claim, r)
    }
}

pub struct GenericSumcheckProtocol<F: PrimeField, I: ExactSizeIterator<Item = usize> + Clone + Send + Sync, S: Sumcheckable<F>> {
    pub config: SumcheckVerifierConfig<I>,
    pub _marker: PhantomData<(F, S)>
}

impl<F: PrimeField, I: ExactSizeIterator<Item = usize> + Clone + Send + Sync, S: Sumcheckable<F>> GenericSumcheckProtocol<F, I, S> {
    pub fn new(degrees: impl IntoIterator<IntoIter = I>) -> Self {
        Self { config: SumcheckVerifierConfig::new(degrees), _marker: PhantomData }
    }

    pub fn num_vars(&self) -> usize {
        self.config.num_vars()
    }
}

impl<F: PrimeField, I: ExactSizeIterator<Item = usize> + Clone + Send + Sync, S: Sumcheckable<F>> Protocol2 for GenericSumcheckProtocol<F, I, S> {
    type ProverInput = S;
    type ProverOutput = Vec<F>;
    type ClaimsBefore = F;
    type ClaimsAfter = (F, Vec<F>);

    fn prove<PT: TProverTranscript>(&self, transcript: &mut PT, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let degrees = self.config.degrees.clone().into_iter();
        let mut claim = claims;
        let mut sumcheck_object = advice;

        let mut r = Vec::with_capacity(degrees.len());

        for d in degrees {

            let poly = sumcheck_object.unipoly().as_vec(); // we should get our own type for compressed polys, or just switch to vectors
            let msg = compress_coefficients(&poly);
            assert!(msg.len() == d);
            transcript.write_scalars(&msg);
            let x = transcript.challenge(128);
            r.push(x);
            sumcheck_object.bind(x);
            claim = evaluate_poly(&poly, x);
        }

        r.reverse();
        ((claim, r), sumcheck_object.final_evals())

    }

    fn verify<PT: TVerifierTranscript>(&self, transcript: &mut PT, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        self.config.main_cycle_sumcheck_verifier(transcript, claims)
    }
}



pub trait AlgFnSO<F: PrimeField> : Clone + Sync + Send {
    /// Executes function.
    fn exec(&self, args: &impl Index<usize, Output = F>) -> F;
    /// Declares the degree.
    fn deg(&self) -> usize;
    /// Declares the expected number of inputs.
    fn n_ins(&self) -> usize;
}

pub trait AlgFn<F: PrimeField> : Clone + Sync + Send {
    /// Executes function
    fn exec(&self, args: &impl Index<usize, Output = F>) -> impl Iterator<Item = F>;
    /// Declares the degree.
    fn deg(&self) -> usize;
    /// Declares the expected number of inputs.
    fn n_ins(&self) -> usize;
    /// Declares the expected number of outputs.
    fn n_outs(&self) -> usize;
}

/// A simple sumcheck object.
/// Not parallelized, not optimized, dumb as rock.
/// Use to test agreement with other protocols.
#[derive(Clone, Debug)]
pub struct ExampleSumcheckObjectSO<F: PrimeField, Fun: AlgFnSO<F>> {
    polys: Vec<Vec<F>>,
    challenges: Vec<F>,
    f: Fun,
    num_vars: usize,
    round_idx: usize,
    cached_unipoly: Option<UniPoly<F>>,
}

impl<F: PrimeField, Fun: AlgFnSO<F>> ExampleSumcheckObjectSO<F, Fun> {
    pub fn new(polys: Vec<Vec<F>>, f: Fun, num_vars: usize) -> Self {
        let l = polys.len();
        assert!(l == f.n_ins());
        for i in 0..l {
            assert!(polys[i].len() == 1 << num_vars);
        }
        Self { polys, f, num_vars, round_idx: 0, cached_unipoly: None, challenges: vec![] }
    }
}

pub fn bind_dense_poly<F: PrimeField>(poly: &mut Vec<F>, t: F) {
    let half = poly.len() / 2;
    *poly = (0..half).into_par_iter().map(|i| poly[2*i] + t * (poly[2*i + 1] - poly[2*i])).collect();
}

impl<F: PrimeField, Fun: AlgFnSO<F>> Sumcheckable<F> for ExampleSumcheckObjectSO<F, Fun> {
    fn bind(&mut self, t: F) {
        assert!(self.round_idx < self.num_vars, "the protocol has already ended");
        self.challenges.push(t);
        for poly in &mut self.polys {
            bind_dense_poly(poly, t);
        }
        self.round_idx += 1;
        match self.cached_unipoly.take() {
            None => {panic!("should evaluate unipoly before binding - it has an opportunity to change the state due to in-place evaluation")}
            Some(_) => ()
        }
    }

    fn unipoly(&mut self) -> UniPoly<F> {
        assert!(self.round_idx < self.num_vars, "the protocol has already ended");

        match self.cached_unipoly.as_ref() {
            Some(p) => {return p.clone()},
            None => {
                let half = 1 << (self.num_vars - self.round_idx - 1);
                let n_polys = self.polys.len();
                let offset_deg = self.f.deg() + 1;

                let mut difs = vec![F::zero(); n_polys];
                let mut args = vec![F::zero(); n_polys];

                let mut acc = vec![F::zero(); self.f.deg() + 1];

                for i in 0..half {
                    for j in 0..n_polys {
                        args[j] = self.polys[j][2 * i];
                    }

                    acc[0] += self.f.exec(&args);

                    for j in 0..n_polys {
                        args[j] = self.polys[j][2 * i + 1]
                    }

                    acc[1] += self.f.exec(&args);

                    for j in 0..n_polys {
                        difs[j] = self.polys[j][2 * i + 1] - self.polys[j][2 * i]
                    }

                    for s in 2..offset_deg {
                        for j in 0..n_polys {
                            args[j] += difs[j];
                        }

                        acc[s] += self.f.exec(&args);
                    }
                }

                self.cached_unipoly = Some(UniPoly::from_evals(&acc));
            }
        }
        self.cached_unipoly.as_ref().unwrap().clone()

    }

    fn final_evals(&self) -> Vec<F> {
        assert!(self.round_idx == self.num_vars, "can only call final evals after the last round");
        self.polys.iter().map(|poly| poly[0]).collect()
    }

    fn challenges(&self) -> &[F] {
        &self.challenges
    }
}




#[derive(Clone, Debug)]
pub struct DenseSumcheckObjectSO<F: PrimeField, Fun: AlgFnSO<F>> {
    polys: Vec<Vec<F>>,
    challenges: Vec<F>,
    f: Fun,
    num_vars: usize,
    round_idx: usize,
    cached_unipoly: Option<UniPoly<F>>,

    claim: F,
}

impl<F: PrimeField, Fun: AlgFnSO<F>> DenseSumcheckObjectSO<F, Fun> {
    pub fn new(polys: Vec<Vec<F>>, f: Fun, num_vars: usize, claim_hint: F) -> Self {
        let l = polys.len();
        assert!(l == f.n_ins());
        for i in 0..l {
            assert!(polys[i].len() == 1 << num_vars);
        }
        Self { polys, f, num_vars, round_idx: 0, cached_unipoly: None, challenges: vec![], claim: claim_hint }
    }
}

impl<F: PrimeField, Fun: AlgFnSO<F>> Sumcheckable<F> for DenseSumcheckObjectSO<F, Fun> {
    fn bind(&mut self, t: F) {
        assert!(self.round_idx < self.num_vars, "the protocol has already ended");
        self.challenges.push(t);
        for poly in &mut self.polys {
            bind_dense_poly(poly, t);
        }
        self.round_idx += 1;
        match self.cached_unipoly.take() {
            None => {panic!("should evaluate unipoly before binding - it has an opportunity to change the state due to in-place evaluation")}
            Some(u) => {self.claim = u.evaluate(&t)}
        }
    }

    fn unipoly(&mut self) -> UniPoly<F> {
        assert!(self.round_idx < self.num_vars, "the protocol has already ended");
        
        match self.cached_unipoly.as_ref() {
            Some(p) => {return p.clone()},
            None => {
                let half = 1 << (self.num_vars - self.round_idx - 1);
                let n_polys = self.polys.len();

                let num_tasks = 8 * current_num_threads();

                let task_size = (half + num_tasks - 1) / num_tasks;

                let acc: Vec<Vec<F>> = (0..num_tasks).into_par_iter().map(|task_idx| {
                    let mut difs = vec![F::zero(); n_polys];
                    let mut args = vec![F::zero(); n_polys];
                    let mut acc = vec![F::zero(); self.f.deg()];
    
                    (task_idx * task_size .. min((task_idx + 1) * task_size, half)).map(|i| {
                        for j in 0..n_polys {
                            args[j] = self.polys[j][2 * i + 1];
                        }
    
                        acc[0] += self.f.exec(&args);
    
                        for j in 0..n_polys {
                            difs[j] = self.polys[j][2 * i + 1] - self.polys[j][2 * i]
                        }
    
                        for s in 1..self.f.deg() {
                            for j in 0..n_polys {
                                args[j] += difs[j];
                            }
    
                            acc[s] += self.f.exec(&args);
                        }                    
                    }).count();

                    acc
                }).collect();

                let mut total_acc = vec![F::zero(); self.f.deg() + 1];

                for i in 0..acc.len() {
                    for j in 0..self.f.deg() {
                        total_acc[j+1] += acc[i][j]
                    }
                }
                total_acc[0] = self.claim - total_acc[1];

                self.cached_unipoly = Some(UniPoly::from_evals(&total_acc));
            }
        }
        self.cached_unipoly.as_ref().unwrap().clone()
        
    }


    fn final_evals(&self) -> Vec<F> {
        assert!(self.round_idx == self.num_vars, "can only call final evals after the last round");
        self.polys.iter().map(|poly| poly[0]).collect()
    }

    fn challenges(&self) -> &[F] {
        &self.challenges
    }
}


//pub type DenseSumcheckObject<F, Fun> = ExampleSumcheckObject<F, Fun>; // To be replaced with optimized implementation.

pub struct ExampleSumcheckObject<F: PrimeField, Fun: AlgFn<F>> {
    polys: Vec<Vec<F>>,
    f: Fun,
    num_vars: usize,
}

impl<F: PrimeField, Fun: AlgFn<F>> ExampleSumcheckObject<F, Fun> {
    pub fn new(polys: Vec<Vec<F>>, f: Fun, num_vars: usize) -> Self {
        Self { polys, f, num_vars }
    }
}

impl<F: PrimeField, Fun: AlgFn<F>> FoldToSumcheckable<F> for ExampleSumcheckObject<F, Fun> {
    type Target = ExampleSumcheckObjectSO<F, GammaWrapper<F, Fun>>;

    fn rlc(self, gamma: F) -> Self::Target {
        Self::Target::new(self.polys, GammaWrapper::new(self.f, gamma), self.num_vars)
    }
}

pub fn gamma_rlc<F: PrimeField>(gamma: F, vals: &[F]) -> F {
    let l = vals.len();
    if l == 0 {
        return F::zero();
    }
    let mut ret = vals[l-1];
    for i in 0..l-1 {
        ret *= gamma;
        ret += vals[l-i-2];
    }
    ret
}

pub struct DenseSumcheckObject<F: PrimeField, Fun: AlgFn<F>> {
    polys: Vec<Vec<F>>,
    f: Fun,
    num_vars: usize,
    claim_hint: Vec<F>,
}

impl<F: PrimeField, Fun: AlgFn<F>> DenseSumcheckObject<F, Fun> {
    pub fn new(polys: Vec<Vec<F>>, f: Fun, num_vars: usize, claim_hint: Vec<F>) -> Self {
        Self { polys, f, num_vars, claim_hint }
    }
}

impl<F: PrimeField, Fun: AlgFn<F>> FoldToSumcheckable<F> for DenseSumcheckObject<F, Fun> {
    type Target = DenseSumcheckObjectSO<F, GammaWrapper<F, Fun>>;
    
    fn rlc(self, gamma: F) -> Self::Target {
        Self::Target::new(self.polys, GammaWrapper::new(self.f, gamma), self.num_vars, gamma_rlc(gamma, &self.claim_hint))
    }
}

/// Evaluation of a polynomial in a point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PointClaim<F: PrimeField> {
    pub point: Vec<F>,
    pub ev: F,
}

/// Evaluations of multiple polynomials in a single point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SinglePointClaims<F: PrimeField> {
    pub point: Vec<F>,
    pub evs: Vec<F>,
}

/// Sum of a polynomial over hypercube.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SumClaim<F: PrimeField> {
    pub sum: F,
}


/// A sumcheck with single output, without eq multiplier.
#[derive(Clone)]
pub struct BareSumcheckSO<F: PrimeField, Fun: AlgFnSO<F>, S: Sumcheckable<F>> {
    f: Fun,
    num_vars: usize,
    _marker: PhantomData<(F, S)>,
}

impl<F: PrimeField, Fun: AlgFnSO<F>, S: Sumcheckable<F>> BareSumcheckSO<F, Fun, S> {
    pub fn new(f: Fun, num_vars: usize) -> Self {
        Self { f, num_vars, _marker: PhantomData }
    }
}

impl<F: PrimeField, Fun: AlgFnSO<F>, S: Sumcheckable<F>> Protocol2 for BareSumcheckSO<F, Fun, S> {
    type ProverInput = S;

    type ProverOutput = ();

    type ClaimsBefore = SumClaim<F>;

    type ClaimsAfter = SinglePointClaims<F>;

    fn prove<PT: TProverTranscript>(&self, transcript: &mut PT, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let degrees = repeat(self.f.deg()).take(self.num_vars);
        let generic_protocol_config = GenericSumcheckProtocol::new(degrees);

        let ((ev, point), poly_evs) = generic_protocol_config.prove(transcript, claims.sum, advice);

        transcript.write_scalars(&poly_evs);

        (SinglePointClaims {point, evs: poly_evs}, ())
    }

    fn verify<PT: TVerifierTranscript>(&self, transcript: &mut PT, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let degrees = repeat(self.f.deg()).take(self.num_vars);
        let generic_protocol_config = GenericSumcheckProtocol::<F, _, S>::new(degrees);

        let (ev, point) = generic_protocol_config.verify(transcript, claims.sum);

        let poly_evs = transcript.read_scalars(self.f.n_ins());

        assert_eq!(self.f.exec(&poly_evs), ev, "Final combinator check has failed.");
        SinglePointClaims {point, evs: poly_evs}    }
}

#[derive(Clone)]
pub struct BareSumcheck<F: PrimeField, Fun: AlgFn<F>, S: FoldToSumcheckable<F>> {
    f: Fun,
    num_vars: usize,
    _marker: PhantomData<(F, S)>,
}

impl<F: PrimeField, Fun: AlgFn<F>, S: FoldToSumcheckable<F>> BareSumcheck<F, Fun, S> {
    pub fn new(f: Fun, num_vars: usize) -> Self {
        Self { f, num_vars, _marker: PhantomData }
    }
}

#[derive(Clone)]
pub struct GammaWrapper<F: PrimeField, Fun: AlgFn<F>> {
    f: Fun,
    gamma_pows: Vec<F>,
}

impl<F: PrimeField, Fun: AlgFn<F>> GammaWrapper<F, Fun> {
    pub fn new(f: Fun, gamma: F) -> Self {
        assert!(f.n_outs() > 1);
        let mut gamma_pows = Vec::with_capacity(f.n_outs() - 1);
        gamma_pows.push(gamma);
        for i in 0..f.n_outs() - 2 {
            let tmp = gamma_pows.last().unwrap();
            gamma_pows.push(gamma * tmp);
        }

        Self {f, gamma_pows}
    }
}

impl <F: PrimeField, Fun: AlgFn<F>> AlgFnSO<F> for GammaWrapper<F, Fun> {
    fn exec(&self, args: &impl Index<usize, Output = F>) -> F {
        let mut out = self.f.exec(args);
        let mut ret = out.next().unwrap();
        out.zip(self.gamma_pows.iter()).map(|(a, b)| a * b).map(|x| ret += x).count();
        ret
    }

    fn deg(&self) -> usize {
        self.f.deg()
    }

    fn n_ins(&self) -> usize {
        self.f.n_ins()
    }
}

pub trait FoldToSumcheckable<F: PrimeField> {
    type Target : Sumcheckable<F>;

    fn rlc(self, gamma: F) -> Self::Target;
}

impl<F: PrimeField, Fun: AlgFn<F>, S: FoldToSumcheckable<F>> Protocol2 for BareSumcheck<F, Fun, S> {
    type ProverInput = S;

    type ProverOutput = ();

    type ClaimsBefore = Vec<SumClaim<F>>;

    type ClaimsAfter = SinglePointClaims<F>;

    fn prove<PT: TProverTranscript>(&self, transcript: &mut PT, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        assert!(claims.len() == self.f.n_outs());

        let gamma = transcript.challenge(128);
        let f = GammaWrapper::new(self.f.clone(), gamma);
        let folded_protocol = BareSumcheckSO::<F, _, S::Target>::new(f, self.num_vars);
        let mut folded_claim = claims.last().unwrap().sum;
        let l = claims.len();

        for i in 0 .. (l - 1) {
            folded_claim *= gamma;
            folded_claim += claims[l-i-2].sum;
        };

        let folded_claim = SumClaim {sum: folded_claim};

        let sumcheckable = advice.rlc(gamma);

        folded_protocol.prove(transcript, folded_claim, sumcheckable)

    }

    fn verify<PT: TVerifierTranscript>(&self, transcript: &mut PT, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        assert!(claims.len() == self.f.n_outs());

        let gamma = transcript.challenge(128);
        let f = GammaWrapper::new(self.f.clone(), gamma);
        let folded_protocol = BareSumcheckSO::<F, _, S::Target>::new(f, self.num_vars);

        let mut folded_claim = claims.last().unwrap().sum;
        let l = claims.len();

        for i in 0 .. (l - 1) {
            folded_claim *= gamma;
            folded_claim += claims[l-i-2].sum;
        };

        let folded_claim = SumClaim {sum: folded_claim};

        folded_protocol.verify(transcript, folded_claim)
    }
}



#[cfg(test)]
mod tests {
    use ark_bls12_381::{G1Affine, G1Projective, g1::Config};
    use ark_ec::{CurveConfig, Group};
    use ark_std::{test_rng, UniformRand, Zero, One};
    use ark_ff::Field;
    use liblasso::poly::eq_poly::{self, EqPolynomial};
    use crate::cleanup::proof_transcript::ProofTranscript2;

    use super::*;

    type Fr = <Config as CurveConfig>::ScalarField;

    #[derive(Clone, Copy)]
    pub struct TestFunctionSO {}

    impl AlgFnSO<Fr> for TestFunctionSO {
        fn exec(&self, args: &impl Index<usize, Output = Fr>) -> Fr {
            args[0]*args[2] + args[0]*args[1]*args[2] + (args[0] - args[2]).pow([4])
        }

        fn deg(&self) -> usize {
            4
        }

        fn n_ins(&self) -> usize {
            3
        }
    }

    #[derive(Clone, Copy)]
    pub struct TestFunction {}

    impl AlgFn<Fr> for TestFunction {
        fn exec(&self, args: &impl Index<usize, Output = Fr>) -> impl Iterator<Item = Fr> {
            [args[0] * args[1] - Fr::one(), args[0]*args[2], (args[0] + args[2]).pow([4]), (args[1] - Fr::one()).pow([3])].into_iter()
        }

        fn deg(&self) -> usize {
            4
        }

        fn n_ins(&self) -> usize {
            3
        }

        fn n_outs(&self) -> usize {
            4
        }
    }

    fn evaluate<F: PrimeField>(poly: &[F], pt: &[F]) -> F {
        let e_p = EqPolynomial::new(pt.to_vec());
        poly.iter().zip_eq(e_p.evals().iter()).map(|(&a, b)| a * b).sum::<F>()
    }


    #[test]
    fn example_sumcheck_verifier_accepts_prover_so() {
        let rng = &mut test_rng();
        let dim = 6;
        let polys : Vec<Vec<Fr>> = (0..3).map(|_| (0 .. 1 << dim).map(|_|Fr::rand(rng)).collect()).collect();

        let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");

        let f = TestFunctionSO{};

        let sum_claim = (0 .. 1 << dim).map(|i| f.exec(& [0, 1, 2].map(|j| polys[j][i]))).sum::<Fr>();
        let sum_claim = SumClaim {sum: sum_claim};

        let sumcheckable = ExampleSumcheckObjectSO::new(polys.clone(), f, dim);

        let simple_combinator_sumcheck  = BareSumcheckSO::new(f, dim);
        let (output_claims, _) = simple_combinator_sumcheck.prove(&mut transcript_p, sum_claim, sumcheckable);

        let proof = transcript_p.end();

        let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);

        let expected_output_claims = simple_combinator_sumcheck.verify(&mut transcript_v, sum_claim);

        assert_eq!(output_claims, expected_output_claims);

        let SinglePointClaims { point, evs } = output_claims;
        assert_eq!(polys.iter().map(|poly| evaluate(poly, &point)).collect_vec(), evs);
    }

    #[test]
    fn example_sumcheck_verifier_accepts_prover_mo() {
        let rng = &mut test_rng();
        let dim = 6;
        let polys : Vec<Vec<Fr>> = (0..3).map(|_| (0 .. 1 << dim).map(|_|Fr::rand(rng)).collect()).collect();

        let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");

        let f = TestFunction{};

        let mut sum_claims = vec![Fr::zero(); 4];

        (0 .. 1 << dim).map(|i| f.exec(& [0, 1, 2].map(|j| polys[j][i])).zip_eq(sum_claims.iter_mut()).map(|(x, y)| *y += x).count() ).count();

        let sum_claims = sum_claims.into_iter().map(|x| SumClaim{sum: x}).collect_vec();

        let sumcheckable = ExampleSumcheckObject::new(polys.clone(), f, dim);

        let simple_combinator_sumcheck  = BareSumcheck::new(f, dim);
        let (output_claims, _) = simple_combinator_sumcheck.prove(&mut transcript_p, sum_claims.clone(), sumcheckable);

        let proof = transcript_p.end();

        let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);

        let expected_output_claims = simple_combinator_sumcheck.verify(&mut transcript_v, sum_claims);

        assert_eq!(output_claims, expected_output_claims);

        let SinglePointClaims { point, evs } = output_claims;
        assert_eq!(polys.iter().map(|poly| evaluate(poly, &point)).collect_vec(), evs);

    }


    #[test]
    fn dense_sumcheck_verifier_accepts_prover_mo() {
        let rng = &mut test_rng();
        let dim = 6;
        let polys : Vec<Vec<Fr>> = (0..3).map(|_| (0 .. 1 << dim).map(|_|Fr::rand(rng)).collect()).collect();
                
        let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");

        let f = TestFunction{};

        let mut sum_claims = vec![Fr::zero(); 4];

        (0 .. 1 << dim).map(|i| f.exec(& [0, 1, 2].map(|j| polys[j][i])).zip_eq(sum_claims.iter_mut()).map(|(x, y)| *y += x).count() ).count();

        let sumcheckable = DenseSumcheckObject::new(polys.clone(), f, dim, sum_claims.clone());

        let sum_claims = sum_claims.into_iter().map(|x| SumClaim{sum: x}).collect_vec();

        let simple_combinator_sumcheck  = BareSumcheck::new(f, dim);
        let (output_claims, _) = simple_combinator_sumcheck.prove(&mut transcript_p, sum_claims.clone(), sumcheckable);
        
        let proof = transcript_p.end();

        let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);
        
        let expected_output_claims = simple_combinator_sumcheck.verify(&mut transcript_v, sum_claims);

        assert_eq!(output_claims, expected_output_claims);

        let SinglePointClaims { point, evs } = output_claims;
        assert_eq!(polys.iter().map(|poly| evaluate(poly, &point)).collect_vec(), evs);

    }


    #[test]

    fn gamma_wrapper_works() {
        let f = TestFunction{};
        let rng = &mut test_rng();
        let input = (0..3).map(|_|Fr::rand(rng)).collect_vec();
        let gamma = Fr::rand(rng);
        let output = f.exec(&input);
        let f_folded = GammaWrapper::new(f, gamma);
        let folded_output = f_folded.exec(&input);
        let expected_folded_output = output.enumerate().map(|(i, x)| gamma.pow([i as u64]) * x).sum::<Fr>();

        assert_eq!(folded_output, expected_folded_output);
    }

}