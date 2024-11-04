use std::{cmp::min, iter::repeat_n, marker::PhantomData};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use hashcaster::ptr_utils::{AsSharedMutPtr, UnsafeIndexRawMut};
use itertools::Itertools;
use liblasso::poly::{eq_poly::EqPolynomial, unipoly::UniPoly};
use rayon::{current_num_threads, iter::{repeatn, IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator}, slice::{ParallelSlice, ParallelSliceMut}};

use crate::{cleanup::{proof_transcript::TProofTranscript2, protocol2::Protocol2, protocols::{pushforward::logup_mainphase::LogupMainphaseProtocol, splits::{SplitAt, SplitIdx}, sumcheck::{decompress_coefficients, DenseEqSumcheckObject, FoldToSumcheckable, PointClaim}}, utils::algfn::AlgFnUtils}, polynomial::vecvec::VecVecPolynomial, utils::{eq_eval, eq_sum, make_gamma_pows}};

use super::super::{sumcheck::{compress_coefficients, evaluate_univar, DenseSumcheckObjectSO, SinglePointClaims, SumClaim, SumcheckVerifierConfig}, sumchecks::vecvec_eq::Sumcheckable};
use crate::cleanup::utils::algfn::{AlgFn, AlgFnSO};

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

#[derive(Clone)]
pub struct Prod4Fn<F: PrimeField> {
    _marker: PhantomData<F>
}

impl<F: PrimeField> Prod4Fn<F> {
    pub fn new() -> Self {
        Self { _marker: PhantomData }
    }
}

impl<F: PrimeField> AlgFnSO<F> for Prod4Fn<F> {
    fn exec(&self, args: &impl std::ops::Index<usize, Output = F>) -> F {
        args[0] * args[1] * args[2] * args[3]
    }

    fn deg(&self) -> usize {
        4
    }

    fn n_ins(&self) -> usize {
        4
    }
}

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


pub type AddInversesSumcheckObject<F> = DenseEqSumcheckObject<F, AddInversesFn<F>>;
pub type AddInversesSumcheckObjectSO<F> = <DenseEqSumcheckObject<F, AddInversesFn<F>> as FoldToSumcheckable<F>>::Target;

pub struct Layer1CombinedObject<F: PrimeField> {
    prod3: LayeredProd3SumcheckObject<F>,
    add_inverses: AddInversesSumcheckObjectSO<F>,
}
pub struct LayeredProd4SumcheckObject<F: PrimeField> {
    n_vars_x: usize,
    n_vars_y: usize,
    object: DenseSumcheckObjectSO<F, Prod4Fn<F>>,
}

impl<F: PrimeField> LayeredProd4SumcheckObject<F> {
    pub fn new(p: Vec<F>, a: Vec<F>, b: Vec<F>, c: Vec<F>, n_vars_x: usize, n_vars_y: usize, claim_hint: F) -> Self {
        assert!(p.len() == 1 << n_vars_x);
        assert!(a.len() == 1 << (n_vars_x + n_vars_y));
        assert!(a.len() == b.len());
        let p = p.into_par_iter().map(|x| repeatn(x, 1 << n_vars_y)).flatten().collect();
        let f = Prod4Fn::new();
        let object = DenseSumcheckObjectSO::new(vec![p, a, b, c], f, n_vars_x + n_vars_y, claim_hint);
        Self { n_vars_x, n_vars_y, object }
    }
}

impl<F: PrimeField> Sumcheckable<F> for LayeredProd4SumcheckObject<F> {
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
pub struct LayeredProd4Protocol<F: PrimeField> {
    n_vars_x: usize,
    n_vars_y: usize,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> LayeredProd4Protocol<F> {
    pub fn new(n_vars_x: usize, n_vars_y: usize) -> Self {
        Self { n_vars_x, n_vars_y, _marker: PhantomData }
    }
}

#[derive(Clone)]
pub struct LayeredProd4ProtocolInput<F: PrimeField> {
    pub p: Vec<F>,
    pub a: Vec<F>,
    pub b: Vec<F>,
    pub c: Vec<F>,
}


impl<T: TProofTranscript2, F: PrimeField> Protocol2<T> for LayeredProd4Protocol<F> {
    type ProverInput = LayeredProd4ProtocolInput<F>;

    type ProverOutput = ();

    type ClaimsBefore = SumClaim<F>;

    type ClaimsAfter = SinglePointClaims<F>;

    fn prove(&self, transcript: &mut T, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let mut claim = claims.sum;
        let mut object = LayeredProd4SumcheckObject::new(advice.p, advice.a, advice.b, advice.c, self.n_vars_x, self.n_vars_y, claim);
        for i in 0 .. (self.n_vars_x + self.n_vars_y) {
            let u = object.unipoly().as_vec();
            transcript.write_scalars(&compress_coefficients(&u));
            let t = transcript.challenge(128);
            claim = evaluate_univar(&u, t);
            object.bind(t);
        }
        let evs = object.final_evals();
        let mut point = object.challenges().to_vec();
        point.reverse();

        assert!(evs.len() == 4);
        transcript.write_scalars(&evs);
    
        (SinglePointClaims {point, evs}, ())
    }

    fn verify(&self, transcript: &mut T, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let degrees = repeat_n(3, self.n_vars_y).chain(repeat_n(4, self.n_vars_x)).collect_vec();

        let verifier = SumcheckVerifierConfig::new(degrees.into_iter());

        let (final_claim, point) = verifier.main_cycle_sumcheck_verifier(transcript, claims.sum);

        let evs = transcript.read_scalars(4);

        assert!(evs[0] * evs[1] * evs[2] * evs[3] == final_claim);

        SinglePointClaims {point, evs}
    }
}

/// Returns bucketing image (i.e. sorting of values of poly by buckets) and a counter (counter[y][x] is and address where poly[y][x] lands after bucketing). Assumes that digits are in base 2^c.
/// Not optimized.
pub fn compute_bucketing_image<F: PrimeField>(
    polys: &Vec<Vec<F>>,
    digits: &Vec<Vec<u32>>,
    c: usize,
    n_vars_x: usize,
    n_vars_y: usize,
    size_x: usize,
    size_y: usize,

    row_pad: Vec<F>,
    col_pad: Vec<F>,
) -> (Vec<VecVecPolynomial<F>>, Vec<Vec<u32>>) {
    for poly in polys {
        assert!(poly.len() == size_x);
    }
    assert!(row_pad.len() == polys.len());
    assert!(col_pad.len() == polys.len());
    assert!(digits.len() == size_y);
    for row in digits {
        assert!(row.len() == size_x);
    }
    assert!(1 << n_vars_x >= size_x);
    assert!(1 << n_vars_y >= size_y);

    let mut counter = vec![vec![0u32; size_x]; size_y];
    let mut buckets = vec![vec![vec![]; size_y << c]; polys.len()];
    for x in 0..size_x {
        for y in 0..size_y {
            let d = (y << c) + digits[y][x] as usize; // target bucket index
            counter[y][x] = buckets[0][d].len() as u32;
            for poly_id in 0..polys.len() {
                buckets[poly_id][d].push(polys[poly_id][x]);
            }
        }
    }

    (
        buckets
            .into_iter()
            .enumerate()
            .map(|(i, buckets)| VecVecPolynomial::new(
                buckets,
                row_pad[i],
                col_pad[i],
                n_vars_x,
                n_vars_y + c)
            )
            .collect_vec(),
        counter
    )
}

// assumes that digits are in range (1 << c).
// parallelized version, TODO: finish and use as drop-in replacement
pub fn compute_bucketing_image_wip<F: PrimeField>(
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


pub struct PipMSMPhase1Data<F: PrimeField> {
    pub c: Vec<F>,
    pub d: Vec<F>,

    pub p_0: Vec<F>,
    pub p_1: Vec<F>,
    
    pub ac_c: Vec<F>, // access counts
    pub ac_d: Vec<F>, // access counts
}

pub struct PipMSMPhase2Data<F: PrimeField> {
    pub c_pull: Vec<F>,
    pub d_pull: Vec<F>,
}

pub trait PipMSMCommitmentEngine<F: PrimeField, G: CurveGroup<ScalarField = F>> {
    /// computes c, and access counts ac_c and ac_d, and commits them all (it is convenient to do both at the same time)
    fn compute_counters_and_commit_phase_1(&self, p_x: Vec<F>, p_y: Vec<F>, d: Vec<Vec<u32>>) -> (Vec<G::Affine>, PipMSMPhase1Data<F>);

    /// commits pullbacks
    fn commit_phase_2(&self, pullbacks: PipMSMPhase2Data<F>) -> Vec<G::Affine>;
}

#[derive(Clone, Copy, Debug)]
pub struct MatrixSelector<F: PrimeField> {
    pub x_size: usize,
    pub x_logsize: usize,
    pub y_size: usize,
    pub y_logsize: usize,
    _marker: PhantomData<F>
}

impl<F: PrimeField> MatrixSelector<F> {
    pub fn new(x_size: usize, x_logsize: usize, y_size: usize, y_logsize: usize) -> Self {
        assert!(x_size <= (1 << x_logsize));
        assert!(y_size <= (1 << y_logsize));
        Self { x_size, x_logsize, y_size, y_logsize, _marker: PhantomData }
    }

    pub fn verifier_evaluate(&self, point_x: &[F], point_y: &[F]) -> F {
        assert!(point_x.len() == self.x_logsize);
        assert!(point_y.len() == self.y_logsize);
        
        eq_sum(&point_x, self.x_size) * eq_sum(&point_y, self.y_size)
    }

    pub fn evaluation_table(&self) -> Vec<F> {
        let _x_size = 1 << self.x_logsize;
        let _y_size = 1 << self.y_logsize;

        (0 .. _x_size * _y_size).into_par_iter().map(|i| if (i % _y_size < self.y_size) && (i / _y_size < self.x_size) {F::one()} else {F::zero()}).collect()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct AddInversesFn<F: PrimeField> {
    _marker: PhantomData<F>
}

impl<F: PrimeField> AddInversesFn<F> {
    pub fn new() -> Self {
        Self { _marker: PhantomData }
    }
}

impl<F: PrimeField> AlgFn<F> for AddInversesFn<F> {
    fn exec(&self, a: &impl std::ops::Index<usize, Output = F>) -> impl Iterator<Item = F> {
        [a[0] + a[1], a[0] * a[1]].into_iter()
    }

    fn deg(&self) -> usize {
        2
    }

    fn n_ins(&self) -> usize {
        2
    }

    fn n_outs(&self) -> usize {
        2
    }
}


#[derive(Clone, Debug)]
pub struct PushforwardProtocol<F: PrimeField> {
    x_logsize: usize,
    y_logsize: usize,
    d_logsize: usize,

    _marker: PhantomData<F>,
}

impl<F: PrimeField, PT: TProofTranscript2> Protocol2<PT> for PushforwardProtocol<F> {
    type ProverInput = (PipMSMPhase1Data<F>, PipMSMPhase2Data<F>);

    type ProverOutput = ();

    type ClaimsBefore = SinglePointClaims<F>; // Full evaluation claim

    type ClaimsAfter = SinglePointClaims<F>;

    fn prove(&self, transcript: &mut PT, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {

        // Parse the point
        let (r_y, rest) = claims.point.split_at(self.y_logsize);
        let r_y = r_y.to_vec();
        let (r_c, rest) = rest.split_at(self.x_logsize);
        let r_c = r_c.to_vec();
        let (r_d, rest) = rest.split_at(self.d_logsize);
        let r_d = r_d.to_vec();
        assert!(rest.len() == 0);

        let (
            PipMSMPhase1Data { c, d, p_0, p_1, ac_c, ac_d },
            PipMSMPhase2Data { c_pull, d_pull }
        ) = advice;

        let matrix_size = 1 << (self.x_logsize + self.y_logsize);
        let x_size = 1 << self.x_logsize;
        let y_size = 1 << self.y_logsize;
        let x_logsize = self.x_logsize;
        let y_logsize = self.y_logsize;

        let f = AddInversesFn::new();

        assert!(c.len() == matrix_size);
        assert!(d.len() == matrix_size);
        assert!(p_0.len() == x_size);
        assert!(p_1.len() == x_size);
        assert!(ac_c.len() == x_size);
        assert!(ac_d.len() == 1 << self.d_logsize);
        assert!(c_pull.len() == matrix_size);
        assert!(d_pull.len() == matrix_size);

        // get challenges

        let [psi, tau_c, tau_d] = transcript.challenge_vec::<F>(3, 512).try_into().unwrap(); // can be smaller bitsize, but let's make it simple for now.
        let gamma : F = transcript.challenge(128);

        // gamma is a folding challenge, psi is a linear combination challenge, tau_c and tau_d are affine offset challenges
        // i.e. lhs of logup will look like sum 1 / (c_pull + psi * c - tau_c) + 1 / (d_pull + psi * d - tau_d)
        // it is more convenient to not perform these ops inside of the sumcheck, so we compute these linear combinations:

        let c_adj : Vec<F> = c_pull.par_iter().zip(c.par_iter()).map(|(&c_pull, &c)| c_pull + psi * c - tau_c).collect();
        let d_adj : Vec<F> = d_pull.par_iter().zip(d.par_iter()).map(|(&d_pull, &d)| d_pull + psi * d - tau_d).collect();

        // now, we will compute the result of this fractional addition

        let [left, right] = f.map_split_hi(&[&c_adj, &d_adj]);
        let [num_l, den_l] = left.try_into().unwrap();
        let [num_r, den_r] = right.try_into().unwrap();

        // synthesize tables (denominators of ac_c and ac_d)
        // this is relatively cheap, because the tables are small

        let eq_c = EqPolynomial::new(r_c.clone()).evals();
        let eq_d = EqPolynomial::new(r_d.clone()).evals();
        let table_c: Vec<F> = (0 .. x_size).into_par_iter().map(|i| eq_c[i] + psi * F::from(i as u64) - tau_c).collect();
        let table_d: Vec<F> = (0 .. 1 << self.d_logsize).into_par_iter().map(|i| eq_d[i] + psi * F::from(i as u64) - tau_d).collect();

        let mainphase = LogupMainphaseProtocol::<F>::new(vec![self.x_logsize + self.y_logsize - 1, self.x_logsize + self.y_logsize - 1, self.x_logsize, self.d_logsize]);

        let (mainphase_claims, ()) = mainphase.prove(
            transcript, 
            (),
            vec![[num_l, den_l], [num_r, den_r], [ac_c, table_c], [ac_d, table_d]]
        );

        assert!(mainphase_claims.len() == 3); // sanity.
        let [cd_claims, ac_c_claims, ac_d_claims] = mainphase_claims.try_into().unwrap();
        
        // VALIDATE AC CLAIMS !!
        println!("WARNING: WE ARE NOT VALIDATING AC CLAIMS YET, FIX");
        // VALIDATE AC CLAIMS !!

        let split = SplitAt::<F>::new(SplitIdx::HI(0), 2);

        let (cd_claims, ()) = split.prove(transcript, cd_claims, ());

        let gammas = make_gamma_pows(gamma, 5);
        let p_folded : Vec<F> = p_0.par_iter().zip(p_1.par_iter()).map(|(&p0, &p1)| p0 + gammas[1] * p1 + gammas[2]).collect();

        // (P0 + gamma * P1 + gamma^2 * 1) c_pull d_pull
        
        assert!(claims.evs.len() == 3); //sanity
        let ev_folded = claims.evs[0] + gammas[1] * claims.evs[1] + gammas[2] * claims.evs[2];

        let mut prod3_object = LayeredProd3SumcheckObject::new(p_folded, c_pull, d_pull, self.x_logsize, self.y_logsize, ev_folded);
        // eq(r, x) (c_adj + d_adj + gamma c_adj d_adj)
        let f = AddInversesFn::<F>::new();
        let SinglePointClaims { point: cd_point, evs: cd_evs } = cd_claims;

        // sanity:
        assert!(cd_evs.len() == 2);
        let mut claim = cd_evs[0] + gammas[1] * cd_evs[1] + gammas[2] * ev_folded;

        let frac_object = DenseEqSumcheckObject::new(vec![c_adj, d_adj], f, cd_point, cd_evs);
        let mut frac_object = frac_object.rlc(gamma);

        let mut output_point = vec![];

        // using combined responses of two sumchecks. probably need a sumcheck wrapper for this, someday.
        for i in 0 .. x_logsize + y_logsize {
            let prod3_response = prod3_object.unipoly().as_vec();
            let frac_response = frac_object.unipoly().as_vec();
            // Sanity:
            assert!(prod3_response.len() == if i < y_logsize {3} else {4});
            assert!(frac_response.len() == 4);

            let combined_response : Vec<F> = (0..4).map(|i| frac_response[i] + prod3_response.get(i).unwrap_or(&F::zero())).collect();

            //sanity:
            assert!(combined_response[0] + combined_response[1].double() + combined_response[2] + combined_response[3] == claim);

            let prover_msg = compress_coefficients(&combined_response);

            transcript.write_scalars(&prover_msg);
            let t = transcript.challenge::<F>(128);

            claim = evaluate_univar(&combined_response, t);
            output_point.push(t);
            prod3_object.bind(t);
            frac_object.bind(t);
        }

        output_point.reverse();

        let [p_folded_ev, c_pull_ev, d_pull_ev] = prod3_object.final_evals().try_into().unwrap();
        let [c_adj_ev, d_adj_ev] = frac_object.final_evals().try_into().unwrap();

        let output_evs = vec![p_folded_ev, c_pull_ev, d_pull_ev, c_adj_ev, d_adj_ev];

        transcript.write_scalars(&output_evs);

        (SinglePointClaims{ point: output_point, evs: output_evs }, ())

    }

    fn verify(&self, transcript: &mut PT, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        
        let (r_y, rest) = claims.point.split_at(self.y_logsize);
        let r_y = r_y.to_vec();
        let (r_c, rest) = rest.split_at(self.x_logsize);
        let r_c = r_c.to_vec();
        let (r_d, rest) = rest.split_at(self.d_logsize);
        let r_d = r_d.to_vec();
        assert!(rest.len() == 0);

        
        let [psi, tau_c, tau_d] = transcript.challenge_vec::<F>(3, 512).try_into().unwrap(); // can be smaller bitsize, but let's make it simple for now.
        let gamma : F= transcript.challenge(128);
        

        let mainphase = LogupMainphaseProtocol::<F>::new(vec![self.x_logsize + self.y_logsize - 1, self.x_logsize + self.y_logsize - 1, self.x_logsize, self.d_logsize]);

        let mainphase_claims = mainphase.verify(
            transcript, 
            (),
        );

        assert!(mainphase_claims.len() == 3); // sanity.
        let [cd_claims, ac_c_claims, ac_d_claims] = mainphase_claims.try_into().unwrap();
        

        // VALIDATE AC CLAIMS !!
        println!("WARNING: WE ARE NOT VALIDATING AC CLAIMS YET, FIX");
        // VALIDATE AC CLAIMS !!

        let split = SplitAt::<F>::new(SplitIdx::HI(0), 2);

        let cd_claims = split.verify(transcript, cd_claims);
        
        
        let gammas = make_gamma_pows(gamma, 5);

        assert!(claims.evs.len() == 3); //sanity
        let ev_folded = claims.evs[0] + gammas[1] * claims.evs[1] + gammas[2] * claims.evs[2];

        // sanity:
        assert!(cd_claims.evs.len() == 2);
        let mut claim = cd_claims.evs[0] + gammas[1] * cd_claims.evs[1] + gammas[2] * ev_folded;


        let mut output_point = vec![];

        for i in 0 .. self.x_logsize + self.y_logsize {
            
            let prover_msg = transcript.read_scalars(3);
            let combined_response = decompress_coefficients(&prover_msg, claim);
            
            let t = transcript.challenge::<F>(128);

            claim = evaluate_univar(&combined_response, t);
            output_point.push(t);
        }

        output_point.reverse();

        let [p_folded_ev, c_pull_ev, d_pull_ev, c_adj_ev, d_adj_ev] = transcript.read_scalars(5).try_into().unwrap();

        assert!(eq_eval(&cd_claims.point, &output_point) * (c_adj_ev + d_adj_ev + gammas[1] * c_adj_ev * d_adj_ev) + gammas[2] * p_folded_ev * c_pull_ev * d_pull_ev == claim);

        SinglePointClaims{ point: output_point, evs: vec![p_folded_ev, c_pull_ev, d_pull_ev, c_adj_ev, d_adj_ev] }

    }
}



#[cfg(test)]
mod tests {
    use ark_bls12_381::{G1Affine, G1Projective, g1::Config};
    use ark_ec::{CurveConfig, Group};
    use ark_std::{log2, test_rng, One, UniformRand, Zero};
    use ark_ff::Field;
    use itertools::Itertools;
    use liblasso::{poly::eq_poly::{self, EqPolynomial}, utils::transcript};
    use rand::RngCore;
    use crate::cleanup::proof_transcript::ProofTranscript2;

    use super::*;

    type Fr = <Config as CurveConfig>::ScalarField;

    #[test]
    fn layered_prod4_verifies() {
        // currently this test does almost nothing, as layered4 actually IS naive implementation (with some padding)
        let rng = &mut test_rng();

        let n_vars_x = 3;
        let n_vars_y = 4;

        let p = (0 .. 1 << n_vars_x).map(|_| Fr::rand(rng)).collect_vec();
        let a = (0 .. 1 << (n_vars_x + n_vars_y)).map(|_| Fr::rand(rng)).collect_vec();
        let b = (0 .. 1 << (n_vars_x + n_vars_y)).map(|_| Fr::rand(rng)).collect_vec();
        let c = (0 .. 1 << (n_vars_x + n_vars_y)).map(|_| Fr::rand(rng)).collect_vec();

        let mut claim_hint = Fr::zero();

        for i in 0 .. (1 << n_vars_x) {
            for j in 0 .. (1 << n_vars_y) {
                claim_hint += p[i] * a[(i << n_vars_y) + j] * b[(i << n_vars_y) + j] * c[(i << n_vars_y) + j]
            }
        }

        let protocol = LayeredProd4Protocol::new(n_vars_x, n_vars_y);

        let mut transcript = ProofTranscript2::start_prover(b"meow");

        let output = protocol.prove(&mut transcript, SumClaim { sum : claim_hint }, LayeredProd4ProtocolInput { p, a, b, c } ).0;

        let proof = transcript.end();

        let mut transcript = ProofTranscript2::start_verifier(b"meow", proof);

        let output2 = protocol.verify(&mut transcript, SumClaim { sum : claim_hint });

        assert_eq!(output, output2);
    }

    #[test]
    fn pushforward_image_works() {
        let rng = &mut test_rng();

        let mut polys = vec![];
        let size_x = 13783;
        let size_y = 32;

        let c = 8;

        for i in 0..3 {
            polys.push((0..size_x).map(|_| Fr::rand(rng)).collect_vec());
        }

        let mut digits = vec![vec![0u32; size_x]; size_y];

        for x in 0..size_x {
            for y in 0..size_y {
                digits[y][x] = rng.next_u32() % (1 << c);
            }
        }

        let (image, counter)
        = compute_bucketing_image(
            &polys,
            &digits,
            c,
            log2(size_x) as usize,
            log2(size_y) as usize,
            size_x,
            size_y,
            vec![Fr::zero(); 3],
            vec![Fr::zero(); 3]
        );

        let image = image.into_iter().map(|vv|vv.data).collect_vec();

        let mut image = image.into_iter().map(|vv|vv.into_iter().map(|v|v.into_iter().map(|x| Some(x)).collect_vec()).collect_vec()).collect_vec();

        for x in 0..size_x {
            for y in 0..size_y {
                let y_addr = (y << c) + digits[y][x] as usize;
                let x_addr = counter[y][x] as usize;

                for i in 0..3 {
                    let val = image[i][y_addr][x_addr].take().unwrap();
                    assert_eq!(val, polys[i][x]);
                }
            }
        }

        image.into_iter().map(|vv|vv.into_iter().map(|v| v.into_iter().map(|x|{
            match x {
                None => (),
                Some(x) => assert!(x == Fr::zero()),
            }
        }).count()).count()).count();

    }
}
