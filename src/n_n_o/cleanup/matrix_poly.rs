// Implements partial inner products of dense vector-arranged and matrix arranged polynomials.
#[allow(unused_imports)]
#[allow(non_snake_case)]


use std::{iter::repeat, marker::PhantomData, ops::{Add, AddAssign, SubAssign, Sub, Mul, MulAssign}, sync::Arc, u64};

use ark_ff::{PrimeField, Zero, One};
use ark_ff::biginteger::BigInteger;
use ark_std::log2;
use itertools::Itertools;
use liblasso::{poly::{eq_poly::EqPolynomial, unipoly::UniPoly}, utils::gaussian_elimination::gaussian_elimination};
use rayon::{current_num_threads, iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator}, slice::ParallelSlice};

use crate::{cleanup::{protocol2::Protocol2, protocols::{sumcheck::{BareSumcheckSO, DenseSumcheckObjectSO, PointClaim, SinglePointClaims, SumClaim}//, verifier_polys::EqPoly
}, utils::algfn::AlgFnSO}, n_n_o::{cleanup::non_native_evs::native_repr, non_native_equalizer}};
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocols::sumchecks::vecvec_eq::Sumcheckable;

use super::utils::overflow_multiplication_utils::*;
use super::utils::polynomial_utils::*;
use super::utils::bit_utils::*;
use super::non_native_evs::Eqpoly;

/// Splits large vector of length n into chunks of small size (length m) and computes inner products, arranging them in a vector of size n/m. n%m must be zero.
/// Supports an additional padding parameter - large vector can actually be of length < n, and will be formally padded with zeros to length n. This does not actually allocate zeros. 
pub fn inner_prod_lo<F: PrimeField>(large: &[F], small: &[F], pad_large_to_length: usize) -> Vec<F> {
    let m = small.len();
    assert!(large.len() <= pad_large_to_length);
    let n = pad_large_to_length;
    assert!(m > 0);
    assert!(n % m == 0);
    let mut ret = large.par_chunks(m).map(|chunk| {
        let mut acc = chunk[0] * small[0];
        for i in 1..chunk.len() {
            acc += chunk[i] * small[i]
        }
        acc
    }).collect::<Vec<F>>();
    let l = ret.len();
    ret.extend(repeat(F::zero()).take(n / m - l));
    ret
}

/// Assumes that pad_large_to_length >= large.len(), and pad_large_to_length % small.len == 0.
fn inner_prod_hi_nonpar_unchecked<F: PrimeField>(large: &[F], small: &[F], pad_large_to_length: usize) -> Vec<F> {
    let m = small.len();
    let n = pad_large_to_length;
    
    if (n/m) >= large.len() {
        return large.iter().map(|x| *x * small[0]).chain(repeat(F::zero())).take(n/m).collect()
    }

    let (first, large) = large.split_at(n/m);
    let mut ret = first.iter().map(|x| *x * small[0]).collect_vec();
    large.chunks(n / m).enumerate().map(|(i, chunk)| for j in 0..chunk.len() {ret[j] += chunk[j] * small[i + 1]}).count();
    ret
}

/// For large vector of length n and small vector of length m, such that m | n,
/// splits it into m chunks, multiplies i-th chunk by small[i], and adds them together
pub fn inner_prod_hi<F: PrimeField>(large: &[F], small: &[F], pad_large_to_length: usize) -> Vec<F> {
    let m = small.len();
    assert!(large.len() <= pad_large_to_length);
    let n = pad_large_to_length;
    assert!(m > 0);
    assert!(n % m == 0);
    if n == 0 {return vec![]}
    
    let factor = 8 * current_num_threads(); // somewhat ad hoc, chunks a bit finer than num_threads to improve load balancing in case m is not divisible by num_threads
    
    let by = (m + factor - 1) / factor;

    let mut results: Vec<Vec<F>> = small.par_chunks(by).zip(large.par_chunks(by * (n / m))).map(|(small, large)| inner_prod_hi_nonpar_unchecked(large, small, by * (n / m))).collect();

    let mut acc = results.pop().unwrap_or(vec![F::zero(); n / m]);

    for i in 0..results.len() {
        results[i].par_iter().zip(acc.par_iter_mut()).map(|(res, acc)| *acc += res).count();
    }

    acc
}

fn add_with_carry(acc: [u64;3], x: (u64, u64)) -> [u64;3]{
    let [a0, a1, carry] = acc;
    let (x0, x1) = x;

    let (b0, c0) = a0.overflowing_add(x0);
    let (b1, c1) = a1.overflowing_add(x1);
    let (b1, c1) = b1.overflowing_add(c0 as u64);
    let carry = carry + c1 as u64;

    [b0, b1, carry]
}

fn make_prover_response<F: PrimeField>(Pxy: &[u64], Px: &[u64], Py: &[u64], num_limbs: usize) -> Vec<F> 
// num_limbs should be 6...
{

    assert_eq!(Px.len()% num_limbs, 0);
    assert_eq!(Py.len()% num_limbs, 0);
    
    let n = Px.len() / num_limbs;
    let m = Py.len() / num_limbs;
    assert_eq!(Pxy.len(), m*n);

    // multiplying Pxy by Px and summing by x

    let mut acc = vec![[0_u64; 3]; Py.len()];
    let mut b = false;
    for i in (0..n){
        for j in (0..num_limbs){
            for k in (0..m){
                let incr = Px[i*num_limbs + j].widening_mul( Pxy[i + n*k]);
                acc[k*num_limbs + j] = add_with_carry(acc[k*num_limbs + j] , incr);
            }
        }
    }

    let mut res = vec![F::zero(); 2*num_limbs - 1];

    for k in 0..m{
        let P1 = acc[k*num_limbs .. k*num_limbs + num_limbs].iter().map(|limbs| limbs_to_fe(limbs)).collect_vec();
        let P2 = Py[k*num_limbs.. k*num_limbs + num_limbs].iter().map(|limb| F::from(*limb)).collect_vec();
        let product = multiply_two_polys_coeffs(&P1, &P2);
        for j in 0..res.len(){
            res[j] += product[j];
        }
    }
    println!("{:?}", acc);
    println!("{:?}", res);
    res
}


/// Takes a vector of F-elements, interprets each of these as BigInt, multiplies k-th limb by 2^{64k}, and casts to NNF. 
/// Assumes the limb representation is valid; that is, if NNF is smaller than F, then the last limbs need to be zero
pub fn normalize_and_cast_to_nn<F: PrimeField, NNF: PrimeField>(limbs: &[F]) -> NNF 
{
    let ans_bigint = limbs.iter()
                        .enumerate()
                        .fold(NNF::BigInt::from(0_u64), |acc, (k, x)| {
                            let mut temp = acc;
                            let mut x = NNF::BigInt::from(fe_to_limbs(x)[0]);
                            x.muln((64*k) as u32);
                            temp.add_with_carry({
                                &x
                            });
                            temp
                        });
    NNF::from(ans_bigint)
}

pub mod test{
    #[allow(unused_imports)]

    use super::*;
    use crate::n_n_o::cleanup::utils::polynomial_utils;
    use crate::n_n_o::cleanup::utils::overflow_multiplication_utils;

    use ark_bls12_381::Fr;
    use ark_bls12_381::Fq;
    use ark_bls12_381::G1Projective;
    use ark_ff::{MontBackend};
    use ark_ff::{biginteger::BigInteger, biginteger::BigInt};
    use ark_std::{test_rng, UniformRand};
    use ark_std::rand::Rng;
    use itertools::Itertools;
    use liblasso::utils::math::Math;
    use crate::protocol::protocol::MultiEvalClaim;
    use crate::protocol::protocol::{ProtocolVerifier, ProtocolProver};
    use crate::protocol::sumcheck::{*, SumcheckPolyMapVerifier, SumcheckPolyMapProver};
    use crate::transcript::Challenge;
    use crate::transcript::IndexedProofTranscript;
    use liblasso::utils::test_lib::TestTranscript;


    #[test]
    //TODO: better test
    fn test_normalize_and_cast_to_nn(){

        let nnf : Fq = normalize_and_cast_to_nn(&[Fr::from(1), Fr::from(5),Fr::from(4),Fr::from(3),Fr::from(2),Fr::from(1)]);

        println!("{:?}", nnf);
    }

        
    #[test]
    //TODO: this doesn't really test anything now
    fn test_nn_provers_response(){
        let rng = &mut test_rng();
        let num_limbs = 4;
        let len1: u64 = 2*3;
        let len2: u64 = num_limbs*2;
        let len3: u64 = num_limbs*3;
        // let coeffs1 = (0..len1).map(|_| rng.gen_range(0..5)).collect_vec();
        // let coeffs2 = (0..len2).map(|_| rng.gen_range(0..5)).collect_vec();
        // let coeffs3 = (0..len3).map(|_| rng.gen_range(0..5)).collect_vec();

        
        let coeffs1 = (1..len1 + 1).map(|x| x*x).collect_vec();
        let coeffs2 = (1..len2 + 1).collect_vec();
        let coeffs3 = (len3..2*len3).collect_vec();
    
        let r = make_prover_response::<Fq>(&coeffs1, &coeffs2, &coeffs3, num_limbs as usize);
        println!("{:?}", (
            Fr::MODULUS_BIT_SIZE, Fq::MODULUS_BIT_SIZE));
    }
}

/// Matrix-arranged polynomial.
/// Columns are little-end, i.e. each column is a chunk of length y_size.
/// x_logsize and y_logsize are "true" log-dimensions of this polynomial, which is assumed to be formally appended with zeroes.
pub struct MatrixPoly<F> {
    pub x_size: usize,
    pub y_size: usize,
    pub x_logsize: usize,
    pub y_logsize: usize,

    pub values: Vec<F>,
}

impl<F> MatrixPoly<F> {
    pub fn new(x_size: usize, y_size: usize, x_logsize: usize, y_logsize: usize, values: Vec<F>) -> Self {
        assert!(1 << x_logsize >= x_size);
        assert!(1 << y_logsize >= y_size);
        assert!(values.len() == x_size * y_size);
        Self { x_size, y_size, x_logsize, y_logsize, values }
    }
}

/// Non-native opening protocol. Assumes that the transcript contains commitments to the oracle P(x, y) to 64-limb representation of evaluation table of NF-polynomial NN_P(x).
pub struct NNOProtocol<F: PrimeField, NNF: PrimeField> {
    pub x_logsize: usize,
    pub y_size: usize, // (NF_bitsize + 63) / 64, i.e. amount of 64-bit limbs that is enough to fit NF element
    pub y_logsize: usize,
    _marker: PhantomData<(F, NNF)>,
}

impl<F: PrimeField, NNF: PrimeField> NNOProtocol<F, NNF> {
    pub fn new(x_logsize: usize) -> Self {
        let y_size = (NNF::MODULUS_BIT_SIZE as usize + 63) / 64;
        let y_logsize = log2(y_size) as usize;
        Self { x_logsize, y_size, y_logsize, _marker: PhantomData }
    }
}


/// Output claim of non native opening protocol.
pub struct NNOOutputClaim<F: PrimeField, NNF: PrimeField> {
    pub nn_point_lo: Vec<NNF>, //
    pub nn_point_hi: Vec<NNF>, // point in which our original polynomial was evaluated, split into 2 parts
    pub r: Vec<F>, // evaluation point

    pub native_repr_eval: F, // evaluation of native representation P(r_x, r_y)

    pub native_repr_nn_eq_lo_eval: F, // evaluation of eq_{nn_point_lo}(r_x[.. (x_logsize+1)/2], r_y)
    pub native_repr_nn_eq_hi_eval: F, // evaluation of eq_{nn_point_hi}(r_x[(x_logsize+1)/2 ..], r_y)
}

impl<F: PrimeField, NNF: PrimeField, PT: TProofTranscript2> Protocol2<PT> for NNOProtocol<F, NNF> {
    type ProverInput = MatrixPoly<u64>;

    type ProverOutput = ();

    type ClaimsBefore = PointClaim<NNF>;

    type ClaimsAfter = NNOOutputClaim<F, NNF>;

    fn prove(&self, transcript: &mut PT, nn_opening_claim: Self::ClaimsBefore, native_repr: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let Pxy = &native_repr.values;
        let pt = nn_opening_claim.point;
        let num_limbs = (NNF::MODULUS_BIT_SIZE as usize + 63) / 64;
        let eq_poly: Eqpoly<u64>= Eqpoly::new(&pt, num_limbs);
        let mid = eq_poly.evals.len()/2;
        let (Px, Py) = eq_poly.evals.split_at(mid);
        let evaluation_with_nonflushed_limbs: Vec<F> = make_prover_response(Pxy, Px, Py, num_limbs);
        // some other length on the right 
        // assert!(evaluation_with_nonflushed_limbs.len() == 3 * (self.y_size-1) + 1);
        transcript.write_scalars(&evaluation_with_nonflushed_limbs);
        let t: F = transcript.challenge(128);
        // here, prover computes inner_prod_lo with 1, t, t^2 ...


        let sum_claim = UniPoly::from_coeff(evaluation_with_nonflushed_limbs).evaluate(&t);
        let n_vars_a = self.x_logsize / 2;
        let n_vars_b = self.x_logsize - n_vars_a;

        let triple_prod = TripleProductSumcheck::<F>::new(n_vars_a, n_vars_b);

        let Pxy = Pxy.iter().map(|x| F::from(*x)).collect();
        let Px = Px.iter().map(|x| F::from(*x)).collect();
        let Py = Py.iter().map(|x| F::from(*x)).collect();

        let (SinglePointClaims { point, evs }, p_o) = triple_prod.prove(transcript, SumClaim{sum: sum_claim}, (Arc::new(Pxy), Px, Py));

        let mid = n_vars_a;
        let (nn_point_lo, nn_point_hi) =  pt.split_at(mid);

        let output_claim = NNOOutputClaim::<F, NNF> {
            nn_point_hi: nn_point_hi.to_vec(),
            nn_point_lo: nn_point_lo.to_vec(),
            r: point,
            native_repr_eval: evs[0],
            native_repr_nn_eq_lo_eval: evs[1],
            native_repr_nn_eq_hi_eval: evs[2],
        };
        (output_claim, ())

        // todo!()
    }

    fn verify(&self, transcript: &mut PT, nn_opening_claim: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let pt = nn_opening_claim.point;
        let num_limbs = (NNF::MODULUS_BIT_SIZE as usize + 63) / 64;
        let eq_poly: Eqpoly<u64>= Eqpoly::new(&pt, num_limbs);
        let mid = eq_poly.evals.len()/2;
        let (Px, Py) = eq_poly.evals.split_at(mid);

        let evaluation_with_nonflushed_limbs = transcript.read_scalars::<F>(3 * (self.y_size - 1) + 1);
        //some other assert
        //assert!(nn_opening_claim.ev == normalize_and_cast_to_nn(&evaluation_with_nonflushed_limbs));

        let t : F = transcript.challenge(128);
        let sum_claim = UniPoly::from_coeff(evaluation_with_nonflushed_limbs).evaluate(&t);

        let n_vars_a = self.x_logsize / 2;
        let n_vars_b = self.x_logsize - n_vars_a;

        let triple_prod = TripleProductSumcheck::<F>::new(n_vars_a, n_vars_b);

        let SinglePointClaims { point, evs } = triple_prod.verify(transcript, SumClaim{sum: sum_claim});

        NNOOutputClaim::<F, NNF> {
            nn_point_hi: pt[.. n_vars_a].to_vec(),
            nn_point_lo: pt[n_vars_a ..].to_vec(),
            r: point,
            native_repr_eval: evs[0],
            native_repr_nn_eq_lo_eval: evs[1],
            native_repr_nn_eq_hi_eval: evs[2],
        }
    }
}


// Helpers

#[derive(Clone, Copy)]
pub struct ProdFn<F: PrimeField> {
    _marker: PhantomData<F>
}

impl<F: PrimeField> ProdFn<F> {
    pub fn new() -> Self {
        Self { _marker: PhantomData }
    }
}

impl<F: PrimeField> AlgFnSO<F> for ProdFn<F> {
    fn exec(&self, args: &impl std::ops::Index<usize, Output = F>) -> F {
        args[0] * args[1]
    }

    fn deg(&self) -> usize {
        2
    }

    fn n_ins(&self) -> usize {
        2
    }
}


/// Sumcheck for a triple product P(x_hi, x_lo) A(x_hi) B(x_lo)
pub struct TripleProductSumcheck<F: PrimeField> {
    pub n_vars_a: usize,
    pub n_vars_b: usize,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> TripleProductSumcheck<F> {
    pub fn new(n_vars_a: usize, n_vars_b: usize) -> Self {
        Self { n_vars_a, n_vars_b, _marker: PhantomData }
    }
}

/// Sumcheckable for a triple product P(x_hi, x_lo) A(x_hi) B(x_lo)
pub struct TripleProdSumcheckObject<'a, F: PrimeField> {
    n_vars_a: usize,
    n_vars_b: usize,
    a_len: usize,
    b_len: usize,

    p: &'a [F],
    a: Option<Vec<F>>,

    stage_object: DenseSumcheckObjectSO<F, ProdFn<F>>,

    b_ev: Option<F>,
    
    current_round: usize,
    
    challenges: Vec<F>,
}

impl<'a, F: PrimeField> TripleProdSumcheckObject<'a, F> {
    pub fn new(n_vars_a: usize, n_vars_b: usize, p: &'a [F], a: Vec<F>, b: Vec<F>, claim_hint: F) -> Self {
        let a_len = a.len();
        let b_len = b.len();

        assert!(1 << n_vars_a == a_len);
        assert!(1 << n_vars_b == b_len);

        assert!(a_len * b_len >= p.len());
        let current_round = 0;

        let pa = inner_prod_hi(p, &a, a_len * b_len);

        let f = ProdFn::new();
        let stage_object = DenseSumcheckObjectSO::<F, ProdFn<F>>::new(vec![pa, b], f, n_vars_b, claim_hint);
        let b_ev = None;

        let a = Some(a);

        Self { n_vars_a, n_vars_b, a_len, b_len, p, a, current_round, stage_object, b_ev, challenges: vec![]}
    }
}

impl<'a, F: PrimeField> Sumcheckable<F> for TripleProdSumcheckObject<'a, F> {
    fn bind(&mut self, t: F) {
        assert!(self.current_round < self.n_vars_a + self.n_vars_b);
        self.stage_object.bind(t);
        self.current_round += 1;
        self.challenges.push(t);

        if self.current_round == self.n_vars_b { // go to next stage
            let tmp = self.stage_object.final_evals();

            let mut pt_lo = self.stage_object.challenges().to_vec();
            pt_lo.reverse();
            

            let a = self.a.take().unwrap();
            let eq_b = EqPolynomial::new(pt_lo).evals();

            let p_subst= inner_prod_lo(&self.p, &eq_b, self.a_len * self.b_len);

            let pa_sum_hint = tmp[0]; // currently useless, will become useful when we optimize DenseSumcheck
            self.b_ev = Some(tmp[1]);

            let f = ProdFn::new();
            self.stage_object = DenseSumcheckObjectSO::new(vec![p_subst, a], f, self.n_vars_a, pa_sum_hint);
        }
    }

    fn unipoly(&mut self) -> UniPoly<F> {
        assert!(self.current_round < self.n_vars_a + self.n_vars_b);
        
        let mut ret = self.stage_object.unipoly().as_vec();

        match self.b_ev {
            None => (),
            Some(m) => {ret.iter_mut().map(|c| *c *= m).count();},
        }

        UniPoly::from_coeff(ret)
    }

    fn final_evals(&self) -> Vec<F> {
        assert!(self.current_round == self.n_vars_a + self.n_vars_b, "protocol did not finish yet");
        let tmp = self.stage_object.final_evals();
        let p_ev = tmp[0];
        let a_ev = tmp[1];
        let b_ev = self.b_ev.unwrap();

        vec![p_ev, a_ev, b_ev]
    }

    fn challenges(&self) -> &[F] {
        &self.challenges
    }
}

#[derive(Clone, Copy)]
pub struct MultiProd<const N: usize, F: PrimeField> {
    _marker: PhantomData<F>
}
impl<const N: usize, F: PrimeField> MultiProd<N, F> {
    pub fn new() -> Self {
        assert!(N > 0);
        Self { _marker: PhantomData }
    }
}

impl<const N: usize, F: PrimeField> AlgFnSO<F> for MultiProd<N, F> {
    fn exec(&self, args: &impl std::ops::Index<usize, Output = F>) -> F {
        let mut ret = args[0];
        for i in 1 .. N {
            ret *= args[i]
        }
        ret
    }

    fn deg(&self) -> usize {
        N
    }

    fn n_ins(&self) -> usize {
        N
    }
}

impl<F: PrimeField, PT: TProofTranscript2> Protocol2<PT> for TripleProductSumcheck<F> {
    type ProverInput = (Arc<Vec<F>>, Vec<F>, Vec<F>);

    type ProverOutput = ();

    type ClaimsBefore = SumClaim<F>;

    type ClaimsAfter = SinglePointClaims<F>; // 3 polynomials

    fn prove(&self, transcript: &mut PT, sum_claim: SumClaim<F>, p_a_b: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let f = MultiProd::<3, _>::new();
        let protocol = BareSumcheckSO::<_, MultiProd<3, F>, TripleProdSumcheckObject<F>>::new(f, self.n_vars_a + self.n_vars_b);

        let p = p_a_b.0;
        let a = p_a_b.1;
        let b = p_a_b.2;

        let object = TripleProdSumcheckObject::new(self.n_vars_a, self.n_vars_b, &p, a, b, sum_claim.sum);

        protocol.prove(transcript, sum_claim, object)
    }

    fn verify(&self, transcript: &mut PT, sum_claim: SumClaim<F>) -> Self::ClaimsAfter {
        let f = MultiProd::<3, _>::new();
        let protocol = BareSumcheckSO::<_, MultiProd<3, F>, TripleProdSumcheckObject<F>>::new(f, self.n_vars_a + self.n_vars_b);
        protocol.verify(transcript, sum_claim)
    }
}




#[cfg(test)]
mod tests {
    use ark_bls12_381::g1::Config;
    use ark_ec::{CurveConfig, Group};
    use ark_std::{test_rng, UniformRand, Zero};
    use super::*;
    type Fr = <Config as CurveConfig>::ScalarField;

    #[test]
    fn ips_work() {
        let rng = &mut test_rng();

        for c in 0..2 {

            let m = match c {0 => 13, 1 => 19, _ => panic!()};
            let n = match c {0 => m * 19, 1 => m * 13, _ => panic!()};

            let large = (0..n).map(|_|Fr::rand(rng)).collect_vec();
            let small = (0..m).map(|_|Fr::rand(rng)).collect_vec();

            for s in 0 .. large.len() + 1 {

                let mut expected_ip_lo = vec![Fr::zero(); n / m];
                for i in 0..s {
                    expected_ip_lo[i / m] += large[i] * small[i % m]
                }
                let ip_lo = inner_prod_lo(&large[..s], &small, n);
                assert_eq!(expected_ip_lo, ip_lo);

                let mut expected_ip_hi = vec![Fr::zero(); n / m];
                for i in 0..s {
                    expected_ip_hi[i % (n / m)] += large[i] * small[i / (n / m)]
                }
                let ip_hi = inner_prod_hi(&large[..s], &small, n);
                assert_eq!(expected_ip_hi, ip_hi);

            }
        }
    }


    #[test]

    fn triple_prod_sumcheck_object_works() {
        let rng = &mut test_rng();
        let n_vars_a = 5;
        let n_vars_b = 7;

        let l_a = 1 << n_vars_a;
        let l_b = 1 << n_vars_b;
        let l_p = l_a * l_b;

        let p = (0 .. l_p).map(|_|Fr::rand(rng)).collect_vec();
        let a = (0 .. l_a).map(|_|Fr::rand(rng)).collect_vec();
        let b = (0 .. l_b).map(|_|Fr::rand(rng)).collect_vec();

        let mut a_ext = Vec::with_capacity(l_p);
        let mut b_ext = Vec::with_capacity(l_p);

        for i in 0.. l_p {
            a_ext.push(a[i / l_b])
        }

        for i in 0..l_p {
            b_ext.push(b[i % l_b])
        }

        let claim_hint = p.iter().zip(a_ext.iter().zip(b_ext.iter())).map(|(p, (a, b))| *p * a * b).sum::<Fr>();

        #[derive(Clone)]
        struct TripleProd<F> {
            _marker: PhantomData<F>
        }

        impl<F: PrimeField> AlgFnSO<F> for TripleProd<F> {
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

        let f = TripleProd {_marker: PhantomData};

        let mut comparison_object = DenseSumcheckObjectSO::new(vec![p.clone(), a_ext, b_ext], f, n_vars_a + n_vars_b, claim_hint);
        let mut test_object = TripleProdSumcheckObject::new(n_vars_a, n_vars_b, &p, a, b, claim_hint);

        for i in 0..(n_vars_a + n_vars_b) {
            
            println!("Entering round {}", i);

            let r = Fr::rand(rng);
            let u = comparison_object.unipoly();
            let v = test_object.unipoly();

            for s in 0..4 {
                assert!(u.evaluate(&Fr::from(s as u64)) == v.evaluate(&Fr::from(s as u64)));
            }

            assert!(u.as_vec().len() == 4);
            assert!(v.as_vec().len() == 3);

            comparison_object.bind(r);
            test_object.bind(r);
        }

        assert_eq!(comparison_object.final_evals(), test_object.final_evals());

    }
}