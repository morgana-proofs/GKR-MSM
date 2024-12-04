use std::cmp::max;
use std::{cmp::min, iter::repeat_n, marker::PhantomData};
use ark_ec::pairing::Pairing;
use ark_ec::CurveGroup;
use ark_ec::twisted_edwards::{Affine, TECurveConfig};
use ark_ff::{BigInteger, PrimeField};
use ark_std::log2;
use hashcaster::ptr_utils::{AsSharedMutPtr, UnsafeIndexRawMut};
use itertools::Itertools;
use liblasso::poly::{eq_poly::EqPolynomial, unipoly::UniPoly};
use rayon::iter::IntoParallelRefMutIterator;
use rayon::{current_num_threads, iter::{repeatn, IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator}, slice::{ParallelSlice, ParallelSliceMut}};

use num_traits::Zero;
use ark_ec::VariableBaseMSM;
use crate::msm_nonaffine::VariableBaseMsmNonaffine;

use crate::commitments::knuckles::KnucklesProvingKey;
use crate::msm_nonaffine;
use crate::{cleanup::{proof_transcript::TProofTranscript2, protocol2::Protocol2, protocols::{pushforward::logup_mainphase::LogupMainphaseProtocol, splits::{SplitAt, SplitIdx}, sumcheck::{decompress_coefficients, DenseEqSumcheckObject, FoldToSumcheckable, PointClaim}, verifier_polys::{EqPoly, EqTruncPoly, SelectorPoly, VerifierPoly}}, utils::{algfn::AlgFnUtils, arith::evaluate_poly}}, cleanup::polys::vecvec::VecVecPolynomial, utils::{eq_eval, eq_sum, make_gamma_pows, pad_vector}};
use crate::cleanup::polys::common::EvaluateAtPoint;
use super::super::{sumcheck::{compress_coefficients, evaluate_univar, DenseSumcheckObjectSO, SinglePointClaims, SumClaim, SumcheckVerifierConfig}, sumchecks::vecvec_eq::Sumcheckable};
use crate::cleanup::utils::algfn::{AlgFn, AlgFnSO};
use crate::utils::TwistedEdwardsConfig;

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


pub type AddInversesSumcheckObject<F> = DenseEqSumcheckObject<F, AddInversesFn<F>>;
pub type AddInversesSumcheckObjectSO<F> = <DenseEqSumcheckObject<F, AddInversesFn<F>> as FoldToSumcheckable<F>>::Target;

pub type Prod3SumcheckObjectSO<F> = DenseSumcheckObjectSO<F, Prod3Fn<F>>;

/// Returns bucketing image (i.e. sorting of values of poly by buckets) and a counter (counter[y][x] is and address where poly[y][x] lands after bucketing). Assumes that digits are in base 2^c.
pub fn compute_bucketing_image<F: PrimeField>(
    polys: &Vec<Vec<F>>,
    digits: &Vec<Vec<u32>>,
    c: usize,
    n_vars_x: usize,
    n_vars_y: usize,
    x_size: usize,
    y_size: usize,

    row_pad: Vec<F>,
    col_pad: Vec<F>,
) -> (Vec<VecVecPolynomial<F>>, Vec<Vec<u32>>) {
    for poly in polys {
        assert!(poly.len() == x_size);
    }
    assert!(row_pad.len() == polys.len());
    assert!(col_pad.len() == polys.len());
    assert!(digits.len() == y_size);
    for row in digits {
        assert!(row.len() == x_size);
    }
    assert!(1 << n_vars_x >= x_size);
    assert!(1 << n_vars_y >= y_size);

    let mut counter = vec![vec![0u32; x_size]; y_size];
    let mut buckets = vec![vec![vec![]; polys.len()]; y_size << c];

    buckets.par_chunks_mut(1 << c).into_par_iter().zip(counter.par_iter_mut()).enumerate().map(|(y, (bucket_chunk, counter_row))| {
        for x in 0..x_size {
            let d = digits[y][x] as usize;
            counter_row[x] = bucket_chunk[d][0].len() as u32;
            for poly_id in 0..polys.len() {
                bucket_chunk[d][poly_id].push(polys[poly_id][x])
            }
        }
    }).count();

    let mut buckets_transposed = vec![vec![]; polys.len()];

    for y in 0 .. y_size << c {
        for poly_id in 0 .. polys.len() {
            buckets_transposed[poly_id].push(std::mem::replace(&mut buckets[y][poly_id], vec![]))
        }
    }

    (
        buckets_transposed
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


pub struct BucketingData<F: PrimeField, Ctx: Pairing<ScalarField = F>> {
    pub image: Vec<VecVecPolynomial<F>>,
    pub counter: Vec<Vec<u32>>,

    pub phase_1_comm: PipMSMPhase1Comm<Ctx>,
    pub phase_2_comm: Option<PipMSMPhase2Comm<Ctx>>,

    pub d_bucketed_basis: Vec<Ctx::G1>,
    pub c_bucketed_basis: Vec<Ctx::G1>, 
}


pub fn compute_bucketing<F: PrimeField, Ctx: Pairing<ScalarField = F>>(
    polys: &Vec<Vec<F>>,
    digits: &Vec<Vec<u32>>,
    c: usize,
    n_vars_x: usize,
    n_vars_y: usize,
    x_size: usize,
    y_size: usize,

    row_pad: Vec<F>,
    col_pad: Vec<F>,

    commitment_log_multiplicity: usize,
    commitment_key: &KnucklesProvingKey<Ctx>,
) -> BucketingData<F, Ctx> {
    for poly in polys {
        assert!(poly.len() == x_size);
    }
    assert!(row_pad.len() == polys.len());
    assert!(col_pad.len() == polys.len());
    assert!(digits.len() == y_size);
    for row in digits {
        assert!(row.len() == x_size);
    }
    assert!(1 << n_vars_x >= x_size);
    assert!(1 << n_vars_y >= y_size);

    let mut counter = vec![vec![0u32; x_size]; y_size];
    let mut buckets = vec![vec![vec![]; polys.len()]; y_size << c];

    buckets.par_chunks_mut(1 << c).into_par_iter().zip(counter.par_iter_mut()).enumerate().map(|(y, (bucket_chunk, counter_row))| {
        for x in 0..x_size {
            let d = digits[y][x] as usize;
            counter_row[x] = bucket_chunk[d][0].len() as u32;
            for poly_id in 0..polys.len() {
                bucket_chunk[d][poly_id].push(polys[poly_id][x])
            }
        }
    }).count();

    let mut buckets_transposed = vec![vec![]; polys.len()];

    for y in 0 .. y_size << c {
        for poly_id in 0 .. polys.len() {
            buckets_transposed[poly_id].push(std::mem::replace(&mut buckets[y][poly_id], vec![]))
        }
    }

    let image = buckets_transposed
        .into_iter()
        .enumerate()
        .map(|(i, buckets)| VecVecPolynomial::new(
            buckets,
            row_pad[i],
            col_pad[i],
            n_vars_x,
            n_vars_y + c)
        )
        .collect_vec();


    let phase_1_comm = PipMSMPhase1Comm {
        c: todo!(),
        d: todo!(),
        p_0: todo!(),
        p_1: todo!(),
        ac_c: todo!(),
        ac_d: todo!(),
    };


    BucketingData {
        image,
        counter,
        phase_1_comm,
        phase_2_comm: todo!(),
        d_bucketed_basis: todo!(),
        c_bucketed_basis: todo!(),
        
    
    }
}


#[derive(Clone)]
pub struct PipMSMPhase1Data<F: PrimeField> {
    pub c: Vec<F>,
    pub d: Vec<F>,

    pub p_0: Vec<F>,
    pub p_1: Vec<F>,
    
    pub ac_c: Vec<F>, // access counts
    pub ac_d: Vec<F>, // access counts
}

#[derive(Clone)]
pub struct PipMSMPhase2Data<F: PrimeField> {
    pub c_pull: Vec<F>,
    pub d_pull: Vec<F>,
}

#[derive(Clone)]
pub struct PipMSMPhase1Comm<Ctx: Pairing> {
    pub c: Vec<Ctx::G1Affine>,
    pub d: Vec<Ctx::G1Affine>,

    pub p_0: Ctx::G1Affine,
    pub p_1: Ctx::G1Affine,

    pub ac_c: Ctx::G1Affine,
    pub ac_d: Ctx::G1Affine,
}

#[derive(Clone)]
pub struct PipMSMPhase2Comm<Ctx: Pairing> {
    pub c_pull: Vec<Ctx::G1Affine>,
    pub d_pull: Vec<Ctx::G1Affine>,
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
    pub x_logsize: usize,
    pub y_logsize: usize,

    // x_size is currently unsupported to protect our mental health, you are always adding 2^N points.
    pub y_size: usize,

    pub d_logsize: usize,

    _marker: PhantomData<F>,
}

impl<F: PrimeField> PushforwardProtocol<F> {
    pub fn new(x_logsize: usize, y_logsize: usize, y_size: usize, d_logsize: usize) -> Self {
        assert!(y_size <= (1 << y_logsize));
        Self { x_logsize, y_logsize, y_size, d_logsize, _marker: PhantomData }
    }
}

pub struct PushForwardState<F: PrimeField, Ctx:Pairing<ScalarField = F>> {
    pub phase_1_data: PipMSMPhase1Data<F>,
    pub phase_2_data: Option<PipMSMPhase2Data<F>>,
    pub y_logsize: usize,
    pub d_logsize: usize,
    pub x_logsize: usize,
    pub y_size: usize,
    pub x_size: usize,
    pub counter: Vec<Vec<u32>>,
    pub digits: Vec<Vec<u32>>,
    pub image: Option<Vec<VecVecPolynomial<F>>>,

    pub commitment_log_multiplicity: usize,
    pub commitment_key: KnucklesProvingKey<Ctx>,

    pub phase_1_comm: PipMSMPhase1Comm<Ctx>,
    pub phase_2_comm: Option<PipMSMPhase2Comm<Ctx>>,

    pub d_outer_buckets: Vec<Vec<Ctx::G1>>,
    pub c_outer_buckets: Vec<Vec<Ctx::G1>>,

}

impl<F: PrimeField, Ctx: Pairing<ScalarField = F>> PushForwardState<F, Ctx> {
    pub fn new<CC: TECurveConfig<BaseField=F>>(
        points: &[Affine<CC>],
        coefs: &[CC::ScalarField],
        y_size: usize,
        y_logsize: usize,
        d_logsize: usize,
        x_logsize: usize,

        commitment_log_multiplicity: usize, // log amount of digit rows that fit in a single commitment column. i.e. column size is 2^comm_log_mult * x_size
        commitment_key: KnucklesProvingKey<Ctx>,
    ) -> Self {
        let polys = vec![
            points.iter().map(|a| a.x).collect_vec(),
            points.iter().map(|a| a.y).collect_vec(),
            points.iter().map(|_| F::one()).collect_vec(),
        ];

        assert!(commitment_key.num_vars() == x_logsize + commitment_log_multiplicity);

        assert!(points.len() == 1 << x_logsize);
        let x_size = 1 << x_logsize;

        let mut digits = vec![vec![0u32; x_size]; y_size];

        for x in 0..x_size {
            let coef : <CC::ScalarField as PrimeField>::BigInt = coefs[x].into_bigint();
            let coef = coef.to_bits_be();
            for y in 0..y_size {
//                digits[y][x] = 0;
                for i in 0..d_logsize {
                    digits[y][x] += (coef[y * d_logsize + i] as u32) << i;
                }
            }
        }

// ------------------------------------------------

        for poly in &polys {
            assert!(poly.len() == x_size);
        }
        let row_pad = vec![F::zero(), F::zero(), F::zero()];
        let col_pad = vec![F::zero(), F::zero(), F::zero()];

        assert!(digits.len() == y_size);
        for row in &digits {
            assert!(row.len() == x_size);
        }
        assert!(1 << x_logsize >= x_size);
        assert!(1 << y_logsize >= y_size);

        let mut counter = vec![vec![0u32; x_size]; y_size];
        let mut buckets = vec![vec![vec![]; polys.len()]; y_size << d_logsize];

        let zero = Ctx::G1::zero();

        let comm_mul = 1 << commitment_log_multiplicity;
        let num_matrix_commitments = y_size.div_ceil(comm_mul);

        let mut d_outer_buckets = vec![vec![zero; 1 << d_logsize]; y_size]; // we will first aggregate along each row, then combine them
        let mut c_outer_buckets = vec![vec![zero; 1 << x_logsize]; y_size];

        let c_upper_bound : Vec<usize> = buckets.par_chunks_mut(1 << d_logsize).into_par_iter().zip(counter.par_iter_mut())
            .zip(
                d_outer_buckets.par_iter_mut().zip(
                    c_outer_buckets.par_iter_mut()
                )
            )
            .enumerate().map(|(y, ((bucket_chunk, counter_row), (d_outer_buckets, c_outer_buckets)))| {
            
            let mut max_c = 0;

            for x in 0..x_size {
                let d = digits[y][x] as usize;
                let c = bucket_chunk[d][0].len();

                max_c = max(c, max_c);

                let point = commitment_key.kzg_basis()[x + x_size * (y % comm_mul)];

                d_outer_buckets[d] += point;
                c_outer_buckets[c] += point;

                counter_row[x] = c as u32;
                for poly_id in 0..polys.len() {
                    bucket_chunk[d][poly_id].push(polys[poly_id][x])
                }
            }

            max_c + 1
        }).collect();

        let c_upper_bound : Vec<usize> = c_upper_bound.chunks(comm_mul).map(|chunk| {chunk.into_iter().fold(0, |a, &b| a.max(b))}).collect();

        let d_outer_buckets = d_outer_buckets.par_chunks(comm_mul).into_par_iter().map(
            |chunk| {
                (0..(1 << d_logsize)).map(|i| {
                    let mut acc = chunk[0][i];
                    for j in 1..chunk.len() {
                        acc += chunk[j][i];
                    }
                    acc
                }).collect::<Vec<Ctx::G1>>()
            }
        ).collect::<Vec<Vec<Ctx::G1>>>();

        let c_outer_buckets = c_outer_buckets.par_chunks(comm_mul).into_par_iter().zip(c_upper_bound).map(
            |(chunk, max_c)| {
                
                (0..max_c).map(|i| {
                    let mut acc = chunk[0][i];
                    for j in 1..chunk.len() {
                        acc += chunk[j][i];
                    }
                    acc
                }).collect::<Vec<Ctx::G1>>()
            }
        ).collect::<Vec<Vec<Ctx::G1>>>();

        let mut buckets_transposed = vec![vec![]; polys.len()];

        for y in 0 .. y_size << d_logsize {
            for poly_id in 0 .. polys.len() {
                buckets_transposed[poly_id].push(std::mem::replace(&mut buckets[y][poly_id], vec![]))
            }
        }

        let image = buckets_transposed
            .into_iter()
            .enumerate()
            .map(|(i, buckets)| VecVecPolynomial::new(
                buckets,
                row_pad[i],
                col_pad[i],
                x_logsize,
                y_logsize + d_logsize)
            )
            .collect_vec();


        let d : Vec<CC::BaseField> =
            digits.par_iter().map(|row| row.par_iter().map(|elt| CC::BaseField::from(*elt as u64))).flatten().collect();

        let c : Vec<CC::BaseField> =
            counter.par_iter().map(|row| row.par_iter().map(|elt| CC::BaseField::from(*elt as u64))).flatten().collect();

        let mut ac_d = vec![0u64; 1 << d_logsize];
        let mut ac_c = vec![0u64; 1 << x_logsize];

        for row in &digits {
            for &elt in row {
                ac_d[elt as usize] += 1
            }
        }
        for row in &counter {
            for &elt in row {
                ac_c[elt as usize] += 1
            }
        }

        let ac_c : Vec<F> = ac_c.par_iter().map(|&x| -CC::BaseField::from(x)).collect();
        let ac_d : Vec<F> = ac_d.par_iter().map(|&x| -CC::BaseField::from(x)).collect();
        
        let [p_0, p_1, _] = polys.try_into().unwrap();

        let d_comm : Vec<Ctx::G1Affine> = d_outer_buckets.par_iter().map(|d_row_chunk_buckets| {
            let mut acc = zero;
            let mut running_sum = zero;
            let len = 1 << d_logsize;
            for i in 0..len-1 {
                running_sum += d_row_chunk_buckets[len - i - 1];
                acc += running_sum;
            }
            acc.into()
        }).collect();

        let c_comm : Vec<Ctx::G1Affine> = c_outer_buckets.par_iter().map(|c_row_chunk_buckets| {
            let mut acc = zero;
            let mut running_sum = zero;
            let len = c_row_chunk_buckets.len();
            for i in 0..len-1 {
                running_sum += c_row_chunk_buckets[len - i - 1];
                acc += running_sum;
            }
            acc.into()
        }).collect();

        // let expected_c_comm : Vec<Ctx::G1Affine> = c.par_chunks(1 << commitment_key.num_vars()).map(|chunk| commitment_key.commit(&chunk)).collect();
        // let expected_d_comm : Vec<Ctx::G1Affine> = d.par_chunks(1 << commitment_key.num_vars()).map(|chunk| commitment_key.commit(&chunk)).collect();
        // assert!(d_comm == expected_d_comm);
        // assert!(c_comm == expected_c_comm);

        let phase_1_comm = PipMSMPhase1Comm::<Ctx> {
            c: c_comm,
            d: d_comm,
            p_0: commitment_key.commit(&p_0),
            p_1: commitment_key.commit(&p_1),
            ac_c: commitment_key.commit(&ac_c),
            ac_d: commitment_key.commit(&ac_d),
        };

// ------------------------------------------------
        let phase_1_data = PipMSMPhase1Data{
            c,
            d,
            p_0,
            p_1,
            ac_c,
            ac_d
        };
        Self {
            phase_1_data,
            phase_2_data: None,
            y_logsize,
            d_logsize,
            x_logsize,
            y_size,
            x_size: points.len(),
            counter,
            digits,
            image: Some(image),

            commitment_key,
            commitment_log_multiplicity,

            phase_1_comm,
            phase_2_comm: None,
            d_outer_buckets,
            c_outer_buckets,

        }
    }

    pub fn second_phase(&mut self, r: &[F]) {
        assert!(self.phase_2_data.is_none());
        let (r_y, rest) = r.split_at(self.y_logsize);
        let r_y = r_y.to_vec();
        let (r_d, rest) = rest.split_at(self.d_logsize);
        let r_d = r_d.to_vec();
        let (r_c, rest) = rest.split_at(self.x_logsize);
        let r_c = r_c.to_vec();
        assert_eq!(rest.len(), 0);

        let eq_c = EqPoly::new(self.x_logsize, &r_c).evals();
        let eq_d = EqPoly::new(self.d_logsize, &r_d).evals();

        let c_pull : Vec<F> = self.counter.par_iter().map(|row| {
            row.par_iter().map(|&elt| {
                eq_c[elt as usize]
            })
        }).flatten().collect();

        let d_pull : Vec<F> = self.digits.par_iter().map(|row| {
            row.par_iter().map(|&elt| {
                eq_d[elt as usize]
            })
        }).flatten().collect();


        let d_pull_comm = self.d_outer_buckets.par_iter().map(|basis| {
            Ctx::G1::msm_nonaff(&basis, &eq_d).unwrap().into()
        }).collect();
        let c_pull_comm = self.c_outer_buckets.par_iter().map(|basis| {
            let eq_c_slice = &eq_c[..basis.len()];
            Ctx::G1::msm_nonaff(&basis, eq_c_slice).unwrap().into()
        }).collect();

        // let expected_c_pull_comm : Vec<Ctx::G1Affine> = c_pull.par_chunks(1 << self.commitment_key.num_vars()).map(|chunk| self.commitment_key.commit(&chunk)).collect();
        // let expected_d_pull_comm : Vec<Ctx::G1Affine> = d_pull.par_chunks(1 << self.commitment_key.num_vars()).map(|chunk| self.commitment_key.commit(&chunk)).collect();
        // assert!(d_pull_comm == expected_d_pull_comm);
        // assert!(c_pull_comm == expected_c_pull_comm);

        self.phase_2_data = Some(
            PipMSMPhase2Data{
                c_pull,
                d_pull
            }
        );

        self.phase_2_comm = Some(PipMSMPhase2Comm{
            c_pull : c_pull_comm,
            d_pull : d_pull_comm,
        })
    }
}

pub struct PushforwardFinalClaims<F: PrimeField> {
    pub gamma: F,
    pub claims_about_matrix: SinglePointClaims<F>,
    pub claims_ac_c: SinglePointClaims<F>,
    pub claims_ac_d: SinglePointClaims<F>,
}

impl<F: PrimeField, PT: TProofTranscript2> Protocol2<PT> for PushforwardProtocol<F> {
    type ProverInput = (PipMSMPhase1Data<F>, PipMSMPhase2Data<F>);

    type ProverOutput = (PipMSMPhase1Data<F>, PipMSMPhase2Data<F>);

    type ClaimsBefore = SinglePointClaims<F>; // Full evaluation claim

    type ClaimsAfter = PushforwardFinalClaims<F>; // Evaluation claims and gamma

    fn prove(&self, transcript: &mut PT, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {

        // Parse the point
        let (r_y, rest) = claims.point.split_at(self.y_logsize);
        let r_y = r_y.to_vec();
        let (r_d, rest) = rest.split_at(self.d_logsize);
        let r_d = r_d.to_vec();
        let (r_c, rest) = rest.split_at(self.x_logsize);
        let r_c = r_c.to_vec();
        assert!(rest.len() == 0);

        let (
            PipMSMPhase1Data { mut c, mut d, p_0, p_1, ac_c, ac_d },
            PipMSMPhase2Data { mut c_pull, mut d_pull }
        ) = advice;

        let d_logsize = self.d_logsize;
        let x_logsize = self.x_logsize;
        let y_logsize = self.y_logsize;
        let x_size = 1 << x_logsize;
        let y_size = self.y_size;

        let matrix_logsize = x_logsize + y_logsize;
        let matrix_size = x_size * y_size; // matrix is laid out row-wise

        let f_addinv = AddInversesFn::new();

        // We currently lay out polynomials without padding, but add it when we do an actual proof. The padding-optimized implementation will be added later.

        assert!(c.len() == matrix_size);
        assert!(d.len() == matrix_size);
        assert!(p_0.len() == x_size);
        assert!(p_1.len() == x_size);
        assert!(ac_c.len() == 1 << x_logsize);
        assert!(ac_d.len() == 1 << d_logsize);
        assert!(c_pull.len() == matrix_size);
        assert!(d_pull.len() == matrix_size);

        let _ac_c = ac_c.clone();
        let _ac_d = ac_d.clone();
        let _c_pull = c_pull.clone();
        let _d_pull = d_pull.clone();

        // get challenges

        let [psi, tau_c, tau_d, tau_suppression_term] = transcript.challenge_vec::<F>(4, 512).try_into().unwrap(); // can be smaller bitsize, but let's make it simple for now.
        let gamma : F = transcript.challenge(128);

        // gamma is a folding challenge, psi is a linear combination challenge, tau_c and tau_d are affine offset challenges
        // i.e. lhs of logup will look like sum 1 / c_adj + 1 / d_adj
        // where c_adj, d_adj are the following linear combination:
        // c_adj = c_pull + psi * c - tau_c * selector  + tau_suppression_term * (1 - selector)

        // suppression term is added to c_adj and d_adj outside of the active matrix. it is another tau, which basically enforces us to lookup (0, 0) outside of the matrix -
        // which forces c_pull and c to be equal to 0 outside.

        let mut c_adj : Vec<F> = c_pull.par_iter().zip(c.par_iter()).map(|(&c_pull, &c)| c_pull + psi * c - tau_c).collect();
        let mut d_adj : Vec<F> = d_pull.par_iter().zip(d.par_iter()).map(|(&d_pull, &d)| d_pull + psi * d - tau_d).collect();
        pad_vector(&mut c_adj, matrix_logsize, tau_suppression_term);
        pad_vector(&mut d_adj, matrix_logsize, tau_suppression_term);

        // c_adj = c_pull + psi * c - tau_c * selector + tau_suppression_term * (1 - selector), and similar for d.

        pad_vector(&mut c, matrix_logsize, F::zero());
        pad_vector(&mut d, matrix_logsize, F::zero());
        pad_vector(&mut c_pull, matrix_logsize, F::zero());
        pad_vector(&mut d_pull, matrix_logsize, F::zero());

        // Current version of sumcheck, with padding terms for y coordinate:
        // s denotes selector, eq_s - product of eq and a selector
        // (c_adj + d_adj + gamma * (c_adj * d_adj))
        // gamma^2 * [eq_s(r_y, y)(p_0(x) + gamma p_1(x) + gamma^2 p_2(x)) c_pull(x,y) d_pull(x,y)]

        // now, we will compute the result of this fractional addition

        let [left, right] = f_addinv.map_split_hi(&[&c_adj, &d_adj]); // eventually need to do low splits to deal with padding, idc now
        let [num_l, den_l] = left.try_into().unwrap();
        let [num_r, den_r] = right.try_into().unwrap();

        // synthesize tables (denominators of ac_c and ac_d)
        // this is relatively cheap, because the tables are small

        let eq_c = EqPoly::new(x_logsize, &r_c).evals();
        let eq_d = EqPoly::new(d_logsize, &r_d).evals();
        let table_c: Vec<F> = (0 .. x_size).into_par_iter().map(|i| eq_c[i] + psi * F::from(i as u64) - tau_c).collect();
        let table_d: Vec<F> = (0 .. 1 << d_logsize).into_par_iter().map(|i| eq_d[i] + psi * F::from(i as u64) - tau_d).collect();

        let suppression_term_total = F::from(2 * ((1 << matrix_logsize) - matrix_size) as u64) * tau_suppression_term.inverse().unwrap();

        let mainphase = LogupMainphaseProtocol::<F>::new(vec![self.x_logsize + self.y_logsize - 1, self.x_logsize + self.y_logsize - 1, self.x_logsize, self.d_logsize]);

        let (mainphase_claims, ()) = mainphase.prove(
            transcript, 
            suppression_term_total,
            vec![[num_l, den_l], [num_r, den_r], [ac_c, table_c], [ac_d, table_d]]
        );

        assert!(mainphase_claims.len() == 3); // sanity.
        let [cd_claims, ac_c_claims, ac_d_claims] = mainphase_claims.try_into().unwrap();

        let split = SplitAt::<F>::new(SplitIdx::HI(0), 2);

        let (cd_claims, ()) = split.prove(transcript, cd_claims, ());

        let gammas = make_gamma_pows(gamma, 5);

        // (P0 + gamma * P1 + gamma^2 * 1) c_pull d_pull
        let p_folded : Vec<F> = p_0.par_iter().zip(p_1.par_iter()).map(|(&p0, &p1)| p0 + gammas[1] * p1 + gammas[2]).collect();
        let eq_sel_y = EqTruncPoly::new(y_logsize, y_size, &r_y).evals();

        let p_selector_prod : Vec<F> = (0 .. 1 << matrix_logsize).into_par_iter().map(|i| {
            let i_y = i >> x_logsize;
            let i_x = (i_y << x_logsize) ^ i;
            eq_sel_y[i_y] * p_folded[i_x]
        }).collect();

        assert!(claims.evs.len() == 3); //sanity
        let ev_folded = claims.evs[0] + gammas[1] * claims.evs[1] + gammas[2] * claims.evs[2];

        let f_prod3 = Prod3Fn::<F>::new();

        let mut prod3_object = Prod3SumcheckObjectSO::new(vec![p_selector_prod, c_pull, d_pull], f_prod3, matrix_logsize, ev_folded);

        // eq(r, x) (c_adj + d_adj + gamma c_adj d_adj)
        let f_inv = AddInversesFn::<F>::new();
        let SinglePointClaims { point: cd_point, evs: cd_evs } = cd_claims;

        // sanity:
        assert!(cd_evs.len() == 2);
        let mut claim = (cd_evs[0] + gammas[1] * cd_evs[1]) + gammas[2] * ev_folded;

        let frac_object = DenseEqSumcheckObject::new(vec![c_adj, d_adj], f_inv, cd_point, cd_evs);
        let mut frac_object = frac_object.rlc(gamma);

        let mut output_point = vec![];

        // using combined responses of two sumchecks. probably need a sumcheck wrapper for this, someday.
        for i in 0 .. x_logsize + y_logsize {
            let prod3_response = prod3_object.unipoly().as_vec();
            let frac_response = frac_object.unipoly().as_vec();
            // Sanity:
            assert!(prod3_response.len() == 4);
            assert!(frac_response.len() == 4);

            let combined_response : Vec<F> = (0..4).map(|i| frac_response[i] + gammas[2] * prod3_response[i]).collect();
            //sanity:
            assert!(combined_response[0].double() + combined_response[1] + combined_response[2] + combined_response[3] == claim, "{}", i);

            let prover_msg = compress_coefficients(&combined_response);

            transcript.write_scalars(&prover_msg);
            let t = transcript.challenge::<F>(128);

            claim = evaluate_univar(&combined_response, t);
            output_point.push(t);
            prod3_object.bind(t);
            frac_object.bind(t);
        }

        output_point.reverse();

        let [p_selector_prod_ev, c_pull_ev, d_pull_ev] = prod3_object.final_evals().try_into().unwrap();
        let [c_adj_ev, d_adj_ev, _] = frac_object.final_evals().try_into().unwrap();

        let p_folded_ev = p_selector_prod_ev * eq_sel_y.evaluate(&output_point[..y_logsize]).inverse().unwrap();
        // SANITY:
        assert!(evaluate_poly(&p_folded, &output_point[y_logsize..]) == p_folded_ev);

        // c_adj_ev = c_pull_ev + psi c_ev - tau_c * sel_ev + tau_suppression_term * (1 - sel_ev)
        // similar for d

        let sel_ev =
            SelectorPoly::new(y_logsize, y_size)
            .evaluate(&output_point[..y_logsize]);

        let tmp = tau_suppression_term * (F::one() - sel_ev);
        let psi_inv = psi.inverse().unwrap();

        let c_ev = psi_inv * (c_adj_ev - c_pull_ev + tau_c * sel_ev - tmp);
        let d_ev = psi_inv * (d_adj_ev - d_pull_ev + tau_d * sel_ev - tmp);

        let output_evs = vec![p_folded_ev, c_pull_ev, d_pull_ev, c_ev, d_ev];

        transcript.write_scalars(&output_evs);

        c.truncate(matrix_size);
        d.truncate(matrix_size);


        let output = (
            PipMSMPhase1Data { c, d, p_0, p_1, ac_c: _ac_c, ac_d: _ac_d },
            PipMSMPhase2Data { c_pull: _c_pull, d_pull: _d_pull }
        );

        (
            PushforwardFinalClaims{ gamma,
                claims_about_matrix: SinglePointClaims{ point: output_point, evs: output_evs },
                claims_ac_c: ac_c_claims,
                claims_ac_d: ac_d_claims 
            },
            output
        )

    }

    fn verify(&self, transcript: &mut PT, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {

        // Parse the point
        let (r_y, rest) = claims.point.split_at(self.y_logsize);
        let r_y = r_y.to_vec();
        let (r_d, rest) = rest.split_at(self.d_logsize);
        let r_d = r_d.to_vec();
        let (r_c, rest) = rest.split_at(self.x_logsize);
        let r_c = r_c.to_vec();
        assert!(rest.len() == 0);

        let d_logsize = self.d_logsize;
        let x_logsize = self.x_logsize;
        let y_logsize = self.y_logsize;
        let x_size = 1 << x_logsize;
        let y_size = self.y_size;

        let matrix_logsize = x_logsize + y_logsize;
        let matrix_size = x_size * y_size; // matrix is laid out row-wise

        // get challenges

        let [psi, tau_c, tau_d, tau_suppression_term] = transcript.challenge_vec::<F>(4, 512).try_into().unwrap(); // can be smaller bitsize, but let's make it simple for now.
        let gamma : F = transcript.challenge(128);

        // gamma is a folding challenge, psi is a linear combination challenge, tau_c and tau_d are affine offset challenges
        // i.e. lhs of logup will look like sum 1 / c_adj + 1 / d_adj
        // where c_adj, d_adj are the following linear combination:
        // c_adj = c_pull + psi * c - tau_c * selector  + tau_suppression_term * (1 - selector)

        // suppression term is added to c_adj and d_adj outside of the active matrix. it is another tau, which basically enforces us to lookup (0, 0) outside of the matrix -
        // which forces c_pull and c to be equal to 0 outside.

        // c_adj = c_pull + psi * c - tau_c * selector + tau_suppression_term * (1 - selector), and similar for d.
        
        // Current version of sumcheck, with padding terms for y coordinate:
        // s denotes selector, eq_s - product of eq and a selector
        // (c_adj + d_adj + gamma * (c_adj * d_adj))
        // gamma^2 * [eq_s(r_y, y)(p_0(x) + gamma p_1(x) + gamma^2 p_2(x)) c_pull(x,y) d_pull(x,y)]

        let suppression_term_total = F::from(2 * ((1 << matrix_logsize) - matrix_size) as u64) * tau_suppression_term.inverse().unwrap();

        let mainphase = LogupMainphaseProtocol::<F>::new(vec![self.x_logsize + self.y_logsize - 1, self.x_logsize + self.y_logsize - 1, self.x_logsize, self.d_logsize]);

        let mainphase_claims = mainphase.verify(
            transcript, 
            suppression_term_total,
        );

        assert!(mainphase_claims.len() == 3); // sanity.
        let [cd_claims, ac_c_claims, ac_d_claims] = mainphase_claims.try_into().unwrap();
        
        let split = SplitAt::<F>::new(SplitIdx::HI(0), 2);

        let cd_claims = split.verify(transcript, cd_claims);

        let gammas = make_gamma_pows(gamma, 5);

        assert!(claims.evs.len() == 3); //sanity
        let ev_folded = claims.evs[0] + gammas[1] * claims.evs[1] + gammas[2] * claims.evs[2];

        let f_prod3 = Prod3Fn::<F>::new();

        // eq(r, x) (c_adj + d_adj + gamma c_adj d_adj)
        let f_inv = AddInversesFn::<F>::new();
        let SinglePointClaims { point: cd_point, evs: cd_evs } = cd_claims;

        // sanity:
        assert!(cd_evs.len() == 2);
        let mut claim = cd_evs[0] + gammas[1] * cd_evs[1] + gammas[2] * ev_folded;

        let mut output_point = vec![];

        for i in 0 .. x_logsize + y_logsize {
            let prover_msg = transcript.read_scalars(3);
            let combined_response = decompress_coefficients(&prover_msg, claim);
            let t = transcript.challenge::<F>(128);

            claim = evaluate_univar(&combined_response, t);
            output_point.push(t);

        }
        output_point.reverse();

        let [p_folded_ev, c_pull_ev, d_pull_ev, c_ev, d_ev] = transcript.read_scalars(5).try_into().unwrap();

        // c_adj_ev = c_pull_ev + psi c_ev - tau_c * sel_ev + tau_suppression_term * (1 - sel_ev)
        // similar for d
        let eq_sel_y = EqTruncPoly::new(y_logsize, y_size, &r_y);

        let p_selector_prod_ev = p_folded_ev * eq_sel_y.evaluate(&output_point[..y_logsize]);


        let sel_ev =
            SelectorPoly::new(y_logsize, y_size)
            .evaluate(&output_point[..y_logsize]);

        let tmp = tau_suppression_term * (F::one() - sel_ev);

        let c_adj_ev = c_pull_ev + psi * c_ev - tau_c * sel_ev + tmp;
        let d_adj_ev = d_pull_ev + psi * d_ev - tau_d * sel_ev + tmp;

        let eq_cd = EqPoly::new(matrix_logsize, &cd_point);

        assert!(
            eq_cd.evaluate(&output_point) * ((c_adj_ev + d_adj_ev) + gammas[1] * c_adj_ev * d_adj_ev)
            + gammas[2] * (c_pull_ev * d_pull_ev * p_selector_prod_ev)

            == claim
        );

        let output_evs = vec![p_folded_ev, c_pull_ev, d_pull_ev, c_ev, d_ev];


        PushforwardFinalClaims{ gamma,
            claims_about_matrix: SinglePointClaims{ point: output_point, evs: output_evs },
            claims_ac_c: ac_c_claims,
            claims_ac_d: ac_d_claims 
        }
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
    use crate::cleanup::polys::common::Densify;
    use crate::cleanup::proof_transcript::ProofTranscript2;

    use super::*;

    type Fr = <Config as CurveConfig>::ScalarField;

    #[test]
    fn pushforward_image_works() {
        let rng = &mut test_rng();

        let mut polys = vec![];
        let x_size = 13783;
        let y_size = 29;

        let c = 8;

        for i in 0..3 {
            polys.push((0..x_size).map(|_| Fr::rand(rng)).collect_vec());
        }

        let mut digits = vec![vec![0u32; x_size]; y_size];

        for x in 0..x_size {
            for y in 0..y_size {
                digits[y][x] = rng.next_u32() % (1 << c);
            }
        }

        let (image, counter)
        = compute_bucketing_image(
            &polys,
            &digits,
            c,
            log2(x_size) as usize,
            log2(y_size) as usize,
            x_size,
            y_size,
            vec![Fr::zero(); 3],
            vec![Fr::zero(); 3]
        );

        let image = image.into_iter().map(|vv|vv.data).collect_vec();

        let mut image = image.into_iter().map(|vv|vv.into_iter().map(|v|v.into_iter().map(|x| Some(x)).collect_vec()).collect_vec()).collect_vec();

        for x in 0..x_size {
            for y in 0..y_size {
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

    #[test]
    fn pushforward_works() {
        let rng = &mut test_rng();

        let mut polys = vec![];
        let x_logsize = 10;
        let x_size = 1 << x_logsize;
        let y_logsize = 3;
        let y_size = 5;

        let d_logsize = 8;

        for i in 0..2 {
            polys.push((0..x_size).map(|_| Fr::rand(rng)).collect_vec());
        }
        polys.push((0..x_size).map(|_| Fr::one()).collect_vec());

        let mut digits = vec![vec![0u32; x_size]; y_size];

        for x in 0..x_size {
            for y in 0..y_size {
                digits[y][x] = rng.next_u32() % (1 << d_logsize);
            }
        }

        let (image, counter)
        = compute_bucketing_image(
            &polys,
            &digits,
            d_logsize,
            log2(x_size) as usize,
            log2(y_size) as usize,
            x_size,
            y_size,
            vec![Fr::zero(); 3],
            vec![Fr::zero(); 3]
        );

        let r : Vec<Fr> = (0 .. x_logsize + y_logsize + d_logsize).map(|_|Fr::rand(rng)).collect();

        let image_evals = image.iter().map(|vv|{
            evaluate_poly(&vv.to_dense(()), &r)
        }).collect::<Vec<Fr>>();

        let mut d : Vec<Fr> =
            digits.iter().map(|row| row.iter().map(|elt| Fr::from(*elt as u64))).flatten().collect();

        let mut c : Vec<Fr> =
            counter.iter().map(|row| row.iter().map(|elt| Fr::from(*elt as u64))).flatten().collect();

        let mut ac_d = vec![0u64; 1 << d_logsize];
        let mut ac_c = vec![0u64; 1 << x_logsize];

        for row in &digits {
            for &elt in row {
                ac_d[elt as usize] += 1
            }
        }
        for row in &counter {
            for &elt in row {
                ac_c[elt as usize] += 1
            }
        }

        let ac_c : Vec<Fr> = ac_c.iter().map(|&x| -Fr::from(x)).collect();
        let ac_d : Vec<Fr> = ac_d.iter().map(|&x| -Fr::from(x)).collect();

        let p1_data = PipMSMPhase1Data{
            c : c.clone(),
            d : d.clone(),
            p_0: polys[0].clone(),
            p_1: polys[1].clone(),
            ac_c,
            ac_d
        };

        let (r_y, rest) = r.split_at(y_logsize);
        let r_y = r_y.to_vec();
        let (r_d, rest) = rest.split_at(d_logsize);
        let r_d = r_d.to_vec();
        let (r_c, rest) = rest.split_at(x_logsize);
        let r_c = r_c.to_vec();
        assert!(rest.len() == 0);

        let eq_c = EqPoly::new(x_logsize, &r_c).evals();
        let eq_d = EqPoly::new(d_logsize, &r_d).evals();

        let mut c_pull : Vec<Fr> = counter.iter().map(|row| {
            row.iter().map(|&elt| {
                eq_c[elt as usize]
            })
        }).flatten().collect();

        let mut d_pull : Vec<Fr> = digits.iter().map(|row| {
            row.iter().map(|&elt| {
                eq_d[elt as usize]
            })
        }).flatten().collect();

        let p2_data = PipMSMPhase2Data{
            c_pull : c_pull.clone(),
            d_pull : d_pull.clone()
        };

        let pushforward = PushforwardProtocol::<Fr>::new(x_logsize, y_logsize, y_size, d_logsize);

        let claim = SinglePointClaims{
            point: r.clone(),
            evs: image_evals.clone(),
        };

        let pparam = b"ez first try";
        let mut transcript = ProofTranscript2::start_prover(pparam);
        let (PushforwardFinalClaims{ gamma, claims_about_matrix: output_claim_p, ..}, _) = pushforward.prove(&mut transcript, claim.clone(), (p1_data, p2_data));
        let proof = transcript.end();

        let mut transcript = ProofTranscript2::start_verifier(pparam, proof);
        let PushforwardFinalClaims{ gamma, claims_about_matrix: output_claim_v, ..} = pushforward.verify(&mut transcript, claim);

        assert!(output_claim_p == output_claim_v);

        let output_point = output_claim_p.point;
        let [p_folded_ev, c_pull_ev, d_pull_ev, c_ev, d_ev] = output_claim_p.evs.try_into().unwrap();

        pad_vector(&mut c_pull, x_logsize + y_logsize, Fr::zero());
        pad_vector(&mut d_pull, x_logsize + y_logsize, Fr::zero());
        pad_vector(&mut c, x_logsize + y_logsize, Fr::zero());
        pad_vector(&mut d, x_logsize + y_logsize, Fr::zero());

        assert!(p_folded_ev == evaluate_poly(&polys[0], &output_point[y_logsize..]) + gamma * evaluate_poly(&polys[1], &output_point[y_logsize..]) + gamma * gamma);
        assert!(c_ev == evaluate_poly(&c, &output_point));
        assert!(d_ev == evaluate_poly(&d, &output_point));
        assert!(c_pull_ev == evaluate_poly(&c_pull, &output_point));
        assert!(d_pull_ev == evaluate_poly(&d_pull, &output_point));


    }
}
