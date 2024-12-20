use std::iter::repeat;
use std::marker::PhantomData;
use std::ops::AddAssign;
use ark_bls12_381::Fr;
use ark_ff::{Field, PrimeField};
use ark_std::iterable::Iterable;
use itertools::{repeat_n, Itertools};
use liblasso::poly::unipoly::UniPoly;
use liblasso::utils::math::Math;
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator};
use crate::copoly::Copolynomial;
use crate::cleanup::polys::vecvec::{EQPolyData, VecVecPolynomial};
use crate::cleanup::polys::common::{Make21, BindVar21};
use crate::protocol::protocol::{Protocol, ProtocolProver, ProtocolVerifier};

#[cfg(feature = "prof")]
use profi::{prof, prof_guard};
use tracing::instrument;
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::gkrs::gkr::GKRLayer;
use crate::cleanup::protocols::sumcheck::{DenseSumcheckObjectSO, EqWrapper, FoldToSumcheckable, GammaWrapper, GenericSumcheckProtocol, SinglePointClaims};
use crate::utils::{eq_eval, eq_poly_sequence_from_multiplier_last, eq_poly_sequence_last, make_gamma_pows, zip_with_gamma};
use crate::cleanup::utils::algfn::{AlgFn, AlgFnSO};


pub struct VecVecDeg2SumcheckObject<F: PrimeField, Fun: AlgFn<F>> {
    polys: Vec<VecVecPolynomial<F>>,
    func: Fun,
    claims: Vec<F>,
    point: Vec<F>,
    num_vertical_vars: usize,
}

impl<F: PrimeField, Fun: AlgFn<F>> VecVecDeg2SumcheckObject<F, Fun> {
    pub fn new(
        polys: Vec<VecVecPolynomial<F>>,
        func: Fun,
        claims: Vec<F>,
        point: Vec<F>,
        num_vertical_vars: usize,
    ) -> Self {
        Self {
            polys,
            func,
            claims,
            point,
            num_vertical_vars,
        }
    }
}

impl<F: PrimeField, Fun: AlgFn<F>> FoldToSumcheckable<F> for VecVecDeg2SumcheckObject<F, Fun> {
    type Target = VecVecDeg2SumcheckObjectSO<F, Fun>;

    fn rlc(self, gamma: F) -> Self::Target {
        let gamma_pows = make_gamma_pows(gamma, self.func.n_outs());
        let mut claim = self.claims[0];
        for i in 1..self.claims.len() {
            claim += gamma_pows[i] * self.claims[i];
        }
        Self::Target::new(
            self.polys,
            self.func,
            gamma_pows,
            claim,
            &self.point,
            self.num_vertical_vars,
        )
    }
}


pub struct VecVecDeg2LoSumcheckObjectSO<F: PrimeField, Fun: AlgFn<F>> {
    polys: Vec<VecVecPolynomial<F>>,
    func: Fun,
    gamma_pows: Vec<F>,
    current_point: Vec<F>,
    eq_poly_data: EQPolyData<F>,
    claim: F,
    cached_unipoly: Option<UniPoly<F>>,
}

pub enum VecVecDeg2SumcheckStage<F: PrimeField, Fun: AlgFn<F>> {
    Sparse(VecVecDeg2LoSumcheckObjectSO<F, Fun>),
    Dense(DenseSumcheckObjectSO<F, EqWrapper<F, GammaWrapper<F, Fun>>>)
}

pub struct VecVecDeg2SumcheckObjectSO<F: PrimeField, Fun: AlgFn<F>> {
    sumcheckable: Option<VecVecDeg2SumcheckStage<F, Fun>>
}


impl<F: PrimeField, Fun: AlgFn<F>> VecVecDeg2SumcheckObjectSO<F, Fun> {
    pub fn new(
        polys: Vec<VecVecPolynomial<F>>,
        func: Fun,
        gamma_pows: Vec<F>,
        claim: F,
        point: &[F],
        col_logsize: usize,
    ) -> Self {
        Self {
            sumcheckable: Some(VecVecDeg2SumcheckStage::Sparse(VecVecDeg2LoSumcheckObjectSO {
                eq_poly_data: EQPolyData::new(
                    point,
                    col_logsize,
                    polys[0].data.iter().map(|r| r.len()).max().unwrap(),
                ),
                polys,
                func,
                claim,
                gamma_pows,
                current_point: vec![],
                cached_unipoly: None,
            })),
        }
    }

    pub fn claim(&self) -> F {
        match &self.sumcheckable {
            None => {unreachable!()}
            Some(sumcheckable) => {
                match sumcheckable {
                    VecVecDeg2SumcheckStage::Sparse(s) => {s.claim}
                    VecVecDeg2SumcheckStage::Dense(d) => {d.claim}
                }
            }
        }
    }
}

impl<F: PrimeField, Fun: AlgFn<F>> VecVecDeg2LoSumcheckObjectSO<F, Fun> {
    pub fn new(
        polys: Vec<VecVecPolynomial<F>>,
        func: Fun,
        gamma_pows: Vec<F>,
        claim: F,
        point: &[F],
        col_logsize: usize,
    ) -> Self {
        Self {
            eq_poly_data: EQPolyData::new(
                point,
                col_logsize,
                polys[0].data.iter().map(|r| r.len()).max().unwrap(),
            ),
            polys,
            func,
            claim,
            gamma_pows,
            current_point: vec![],
            cached_unipoly: None,
        }
    }

    pub fn bind_into_dense(mut self, t: F) -> DenseSumcheckObjectSO<F, EqWrapper<F, GammaWrapper<F, Fun>>> {
        let tm1 = t - F::one();
        let mut polys = self.polys
            .iter()
            .map(|p| p.data
                .iter()
                .map(|r| {
                    match r.len() {
                        0 => {p.row_pad}
                        2 => {r[1] + tm1 * (r[0] - r[1])}
                        _ => {unreachable!()}
                    }
                })
                .chain(repeat(p.col_pad))
                .take(1 << self.eq_poly_data.point_parts.padded_vars_idx)
                .collect_vec()
            )
            .collect_vec();
        
        polys.push(eq_poly_sequence_from_multiplier_last(
            self.eq_poly_data.multiplier * (F::one() - self.eq_poly_data.point[self.eq_poly_data.point_parts.binding_var_idx.unwrap()] - t + (self.eq_poly_data.point[self.eq_poly_data.point_parts.binding_var_idx.unwrap()] * t).double()),
            &self.eq_poly_data.point[self.eq_poly_data.point_parts.vertical_vars_range()]).unwrap(),
        );


        DenseSumcheckObjectSO::new(
            polys,
            EqWrapper::new(
                GammaWrapper::new(self.func, self.gamma_pows[1])
            ),
            self.eq_poly_data.point_parts.padded_vars_idx,
            self.cached_unipoly.take().unwrap().evaluate(&t),
        )
    }
}

pub struct UnivarFormat<F> {
    _pd: PhantomData<F>
}

impl<F: PrimeField> UnivarFormat<F> {
    pub fn from12(p1: F, p2: F, eq1: F, previous_claim: F) -> UniPoly<F> {
        let eq0 = F::one() - eq1;
        let eq2 = eq1.double() - eq0;
        let eq3 = eq2.double() - eq1;

        let prod1 = p1 * eq1;
        let prod0 = previous_claim - prod1;
        let p0 = prod0 * eq0.inverse().unwrap();

        let p3 = p2.double() + p2 - p1.double() - p1 + p0;

        UniPoly::from_evals(&[
            prod0,
            prod1,
            p2 * eq2,
            p3 * eq3,
        ])
    }
}

pub trait Sumcheckable<F: PrimeField> {
    fn bind(&mut self, t: F);
    fn unipoly(&mut self) -> UniPoly<F>;
    fn final_evals(&self) -> Vec<F>;
    fn challenges(&self) -> &[F];

    fn current_round(&self) -> usize {todo!()}
}

impl<F: PrimeField, Fun: AlgFn<F>> Sumcheckable<F> for VecVecDeg2SumcheckObjectSO<F, Fun> {
    fn bind(&mut self, t: F) {
        let mut sumcheckable = self.sumcheckable.take();
        match sumcheckable {
            None => {unreachable!()}
            Some(mut sumcheckable) => {
                match sumcheckable {
                    VecVecDeg2SumcheckStage::Sparse(mut vecvec_so) => {
                        if vecvec_so.eq_poly_data.point_parts.binding_var_idx.unwrap() > vecvec_so.eq_poly_data.point_parts.padded_vars_idx {
                            (&mut vecvec_so).bind(t);
                            self.sumcheckable = Some(VecVecDeg2SumcheckStage::Sparse(vecvec_so));
                        } else {
                            self.sumcheckable = Some(VecVecDeg2SumcheckStage::Dense(vecvec_so.bind_into_dense(t)));
                        }
                    }
                    VecVecDeg2SumcheckStage::Dense(mut dense_so) => {
                        (&mut dense_so).bind(t);
                        self.sumcheckable = Some(VecVecDeg2SumcheckStage::Dense(dense_so));
                    }
                }
            }
        }

    }

    fn unipoly(&mut self) -> UniPoly<F> {
        if let Some(sumcheckable) = &mut self.sumcheckable {
            match sumcheckable {
                VecVecDeg2SumcheckStage::Sparse(vecvec_so) => {
                    vecvec_so.unipoly()
                }
                VecVecDeg2SumcheckStage::Dense(dense_so) => {
                    dense_so.unipoly()
                }
            }
        } else {
            unreachable!()
        }
    }

    fn final_evals(&self) -> Vec<F> {
        if let Some(sumcheckable) = &self.sumcheckable {
            match sumcheckable {
                VecVecDeg2SumcheckStage::Sparse(_) => {
                    unreachable!()
                }
                VecVecDeg2SumcheckStage::Dense(dense_so) => {
                    dense_so.final_evals()
                }
            }
        } else { unreachable!() }
    }

    fn challenges(&self) -> &[F] {
        if let Some(sumcheckable) = &self.sumcheckable {
            match sumcheckable {
                VecVecDeg2SumcheckStage::Sparse(vecvec_so) => {
                    vecvec_so.challenges()
                }
                VecVecDeg2SumcheckStage::Dense(dense_so) => {
                    dense_so.challenges()
                }
            }
        } else { unreachable!() }
    }
}

impl<F: PrimeField, Fun: AlgFn<F>> Sumcheckable<F> for VecVecDeg2LoSumcheckObjectSO<F, Fun> {
    fn bind(&mut self, t: F) {
        self.polys.par_iter_mut().map(|v| v.bind_21(t)).count();
        self.current_point.push(t);
        self.eq_poly_data.bind(t);
        self.claim = self.cached_unipoly.take().unwrap().evaluate(&t);
    }

    fn unipoly(&mut self) -> UniPoly<F> {
        if let Some(_) = self.cached_unipoly {
            panic!()
        };

        self.polys.par_iter_mut().map(|v| v.make_21()).count();

        let mut inputs = self.polys.iter().map(|p| p.row_pad).collect_vec();

        let pad_results = self.func.exec(&inputs).collect_vec();

        inputs = self.polys.iter().map(|p| p.col_pad).collect_vec();

        let mut col_pad_results = self.func.exec(&inputs).collect_vec();

        let mut sum2 = vec![F::zero(); self.func.n_outs()];
        let mut sum1 = vec![F::zero(); self.func.n_outs()];
        let row_count = self.polys[0].data.len();
        for row_idx in 0..row_count {
            let mut sum_local2 = vec![F::zero(); self.func.n_outs()];
            let mut sum_local1 = vec![F::zero(); self.func.n_outs()];
            let segment_len = self.polys[0].data[row_idx].len() / 2;
            let eq = self.eq_poly_data.get_segment_evals(segment_len);

            for idx in 0..segment_len {
                for (poly_idx, poly) in self.polys.iter().enumerate() {
                    inputs[poly_idx] = poly.data[row_idx][2 * idx]
                }
                let addition2 = self.func.exec(&inputs);
                for (add_2, i) in addition2.zip_eq(0..self.func.n_outs()) {
                    sum_local2[i] += add_2 * eq[idx];
                }

                for (poly_idx, poly) in self.polys.iter().enumerate() {
                    inputs[poly_idx] = poly.data[row_idx][2 * idx + 1]
                }
                let addition1 = self.func.exec(&inputs);
                for (add_1, i) in addition1.zip_eq(0..self.func.n_outs()) {
                    sum_local1[i] += add_1 * eq[idx];
                }
            }

            let trailing_sum = self.eq_poly_data.get_trailing_sum(segment_len);

            for i in 0..self.func.n_outs() {
                sum_local2[i] += pad_results[i] * trailing_sum;
                sum_local1[i] += pad_results[i] * trailing_sum;
            }

            let vertical_eq_multiplier = self.eq_poly_data.row_eq_coefs[row_idx];
            for i in 0..self.func.n_outs() {
                sum_local2[i] *= vertical_eq_multiplier;
                sum_local1[i] *= vertical_eq_multiplier;
            }

            for i in 0..self.func.n_outs() {
                sum2[i] += sum_local2[i];
                sum1[i] += sum_local1[i];
            }
        }
        
        if row_count < (1 << self.eq_poly_data.point_parts.vertical_vars_range().len()) {
            for (idx, out) in col_pad_results.iter().enumerate() {
                let res = *out * self.eq_poly_data.row_eq_coefs_tail_sums[row_count];
                sum2[idx] += res;
                sum1[idx] += res;
            }
        }
        

        let mut total2 = sum2[0];
        let mut total1 = sum1[0];

        for i in 1..self.func.n_outs() {
            total2 += sum2[i] * self.gamma_pows[i];
            total1 += sum1[i] * self.gamma_pows[i];
        }

        total2 *= self.eq_poly_data.multiplier;
        total1 *= self.eq_poly_data.multiplier;


        let unipoly = UnivarFormat::from12(total1, total2, self.eq_poly_data.point[self.eq_poly_data.point_parts.binding_var_idx.unwrap()], self.claim);
        self.cached_unipoly = Some(unipoly.clone());

        unipoly
    }

    fn final_evals(&self) -> Vec<F> {
        // self.polys.par_iter().map(|poly| poly[0]).collect()
        unreachable!()
    }

    fn challenges(&self) -> &[F] {
        &self.current_point
    }
}

pub struct VecVecDeg2Sumcheck<F: PrimeField, Fun: AlgFn<F>> {
    pub f: Fun,
    pub num_vars: usize,
    pub num_vertical_vars: usize,
    pub _pd: PhantomData<F>,
}

impl <F: PrimeField, Fun: AlgFn<F>> VecVecDeg2Sumcheck<F, Fun> {
    pub fn new(f: Fun, num_vars: usize, num_vertical_vars: usize) -> Self {
        Self {
            f,
            num_vars,
            num_vertical_vars,
            _pd: Default::default(),
        }
    }
}

impl <Transcript: TProofTranscript2, F: PrimeField, Fun: AlgFn<F>> Protocol2<Transcript> for  VecVecDeg2Sumcheck<F, Fun> {
    type ProverInput = Vec<VecVecPolynomial<F>>;
    type ProverOutput = ();
    type ClaimsBefore = SinglePointClaims<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    #[instrument(name="VecVecDeg2Sumcheck::prove", level="trace", skip_all)]
    fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        assert_eq!(self.f.deg(), 2);

        let gamma = transcript.challenge(128);
        let SinglePointClaims { point, evs } = claims;
        let so = VecVecDeg2SumcheckObject::new(
            advice,
            self.f.clone(),
            evs,
            point,
            self.num_vertical_vars
        );

        let so = so.rlc(gamma);

        let degrees = repeat_n(self.f.deg() + 1, self.num_vars);
        let generic_protocol_config = GenericSumcheckProtocol::new(degrees);

        let ((_, point), mut poly_evs) = generic_protocol_config.prove(transcript, so.claim(), so);

        poly_evs.pop();

        transcript.write_scalars(&poly_evs);

        (SinglePointClaims {point, evs: poly_evs}, ())
    }

    fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let degrees = repeat_n(self.f.deg() + 1, self.num_vars);
        let gamma = transcript.challenge(128);
        let SinglePointClaims { point: input_point, evs } = claims;
        let folded_claim = zip_with_gamma(gamma, &evs);

        let generic_protocol_config = GenericSumcheckProtocol::<F, _, VecVecDeg2SumcheckObjectSO<F, Fun>>::new(degrees);

        let (ev, output_point) = generic_protocol_config.verify(transcript, folded_claim);

        let poly_evs = transcript.read_scalars(self.f.n_ins());

        assert_eq!(zip_with_gamma(gamma, &self.f.exec(&poly_evs).collect_vec()) * eq_eval(&input_point, &output_point), ev, "Final combinator check has failed.");
        SinglePointClaims {point: output_point, evs: poly_evs}
    }
}


impl<Transcript: TProofTranscript2, F: PrimeField, Fun: AlgFn<F>> GKRLayer<Transcript, SinglePointClaims<F>, Vec<VecVecPolynomial<F>>> for VecVecDeg2Sumcheck<F, Fun> {
    fn prove_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>, advice: Vec<VecVecPolynomial<F>>) -> SinglePointClaims<F> {
        Protocol2::prove(self, transcript, claims.into(), advice.into()).0
    }

    fn verify_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>) -> SinglePointClaims<F> {
        Protocol2::verify(self, transcript, claims.into())
    }
}


#[cfg(test)]
mod test {
    use std::ops::Index;
    use rstest::*;
    use ark_bls12_381::Fr;
    use ark_ec::CurveConfig;
    use ark_ec::twisted_edwards::{MontCurveConfig, TECurveConfig};
    use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
    use ark_ff::{Field, PrimeField};
    use ark_std::{test_rng, UniformRand};
    use itertools::Itertools;
    use num_traits::{One, Zero};
    use crate::cleanup::polys::common::{Densify, MapSplit};
    use crate::cleanup::proof_transcript::ProofTranscript2;
    use crate::copoly::Copolynomial;
    use crate::cleanup::utils::twisted_edwards_ops::algfns::twisted_edwards_add_l1;
    use crate::cleanup::polys::vecvec::{VecVecPolynomial};
    use crate::protocol::sumcheck::Sumcheckable as OldSumcheckable;
    use crate::utils::{eq_poly_sequence_last, make_gamma_pows_static};
    use super::{Sumcheckable as NewSumcheckable, VecVecDeg2SumcheckObject};
    use crate::cleanup::protocols::sumcheck::{EqWrapper, ExampleSumcheckObjectSO, FoldToSumcheckable, GammaWrapper};
    use crate::cleanup::utils::arith::evaluate_poly;
    use super::*;

    enum Denseness {
        Full,
        Rows,
        Nothing,
    }

    #[rstest]
    fn check_univars(
        #[values(0, 1, 3)]
        num_vertical_vars: usize,
        #[values(Denseness::Full, Denseness::Rows, Denseness::Nothing)]
        denseness: Denseness
    ) {
        let rng = &mut test_rng();
        type F = <BandersnatchConfig as CurveConfig>::BaseField;

        for i in 0..100 {
            let num_vars = 6;

            let generator = match denseness {
                Denseness::Full => { VecVecPolynomial::rand_points_dense::<BandersnatchConfig, _> }
                Denseness::Rows => { VecVecPolynomial::rand_points_dense_rows::<BandersnatchConfig, _> }
                Denseness::Nothing => { VecVecPolynomial::rand_points::<BandersnatchConfig, _> }
            };

            let mut data_l = generator(
                rng,
                num_vars - num_vertical_vars, num_vertical_vars
            );
            let data_r = data_l.clone();

            let data = data_l.into_iter().chain(data_r.into_iter()).collect_vec();

            let gamma = F::one().double();
            let gamma_pows = make_gamma_pows_static::<_, 4>(gamma);

            let f = EqWrapper::new(GammaWrapper::new(twisted_edwards_add_l1(), gamma));
            let f2 = f.clone();

            let mut dense_data = data.iter().map(|p| p.to_dense(())).collect_vec();

            let mut point = (0..num_vars).map(|_| Fr::rand(rng)).collect_vec();

            let mut dense_eqpoly = eq_poly_sequence_last(&point).unwrap();
            dense_data.push(dense_eqpoly.clone());

            let sum_claim = (0 .. 1 << num_vars).map(|i| f.exec(& [0, 1, 2, 3, 4, 5, 6].map(|j| dense_data[j][i]))).sum::<Fr>();

            let vec_claim: Vec<F> = (0..1 << num_vars).map(|i| {
                twisted_edwards_add_l1().exec(&[0, 1, 2, 3, 4, 5].map(|j| dense_data[j][i])).collect_vec()
            }).enumerate().fold(
                vec![F::zero(); 4],
                |mut acc, (i, n)| {
                    acc.iter_mut().zip_eq(n).map(|(a, n)| {
                        *a += (n * dense_eqpoly[i])
                    }).count();
                    acc
                }
            );

            let max_row_len = data.iter().map(|poly| poly.data.iter().map(|row| row.len())).flatten().max().unwrap();

            let vecvec_sumcheck_builder = VecVecDeg2SumcheckObject::new(
                data.to_vec(),
                twisted_edwards_add_l1(),
                vec_claim.try_into().unwrap(),
                point.clone(),
                num_vertical_vars,
            );

            let mut vecvec_sumcheckable = vecvec_sumcheck_builder.rlc(gamma_pows[1]);

            let mut dense_sumcheckable = ExampleSumcheckObjectSO::new(
                dense_data,
                f,
                num_vars,
            );

            for i in 0..num_vars {
                let vecvec_unipoly = vecvec_sumcheckable.unipoly();
                let dense_unipoly = dense_sumcheckable.unipoly();

                assert_eq!(dense_unipoly.evaluate(&Fr::zero()), vecvec_unipoly.evaluate(&Fr::zero()));
                assert_eq!(dense_unipoly.evaluate(&Fr::one()), vecvec_unipoly.evaluate(&Fr::one()));
                assert_eq!(dense_unipoly.evaluate(&Fr::from(2)), vecvec_unipoly.evaluate(&Fr::from(2)));
                assert_eq!(dense_unipoly.evaluate(&Fr::from(3)), vecvec_unipoly.evaluate(&Fr::from(3)));

                assert_eq!(dense_unipoly.as_vec(), vecvec_unipoly.as_vec());

                let t = F::rand(rng);
                vecvec_sumcheckable.bind(t);
                dense_sumcheckable.bind(t);
            }
            assert_eq!(vecvec_sumcheckable.final_evals(), dense_sumcheckable.final_evals());
        }
    }

    #[rstest]
    fn vecvec_sumcheck_prover_verifier(
        #[values(0, 1, 3)]
        num_vertical_vars: usize,
        #[values(Denseness::Full, Denseness::Rows, Denseness::Nothing)]
        denseness: Denseness
    ) {
        let rng = &mut test_rng();
        type F = <BandersnatchConfig as CurveConfig>::BaseField;

        for i in 0..100 {
            let num_vars = 6;

            let generator = match denseness {
                Denseness::Full => { VecVecPolynomial::rand_points_dense::< BandersnatchConfig, _ > }
                Denseness::Rows => { VecVecPolynomial::rand_points_dense_rows::< BandersnatchConfig, _ > }
                Denseness::Nothing => { VecVecPolynomial::rand_points::< BandersnatchConfig, _ > }
            };

            let mut data_l = generator(
                rng,
                num_vars - num_vertical_vars,
                num_vertical_vars
            );
            let data_r = data_l.clone();

            let polys = data_l.into_iter().chain(data_r.into_iter()).collect_vec();

            let output = VecVecPolynomial::algfn_map(&polys, twisted_edwards_add_l1());
            let dense_output = output.iter().map(|p| p.to_dense(())).collect_vec();
            let point = (0..num_vars).map(|_| Fr::rand(rng)).collect_vec();
            let ev_claims = SinglePointClaims {
                point: point.clone(),
                evs: dense_output.iter().map(|output| evaluate_poly(output, &point)).collect(),
            };

            let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");

            let mut sumcheck = VecVecDeg2Sumcheck::new(
                twisted_edwards_add_l1(),
                num_vars,
                num_vertical_vars,
            );

            let (output_claims, _) = sumcheck.prove(&mut transcript_p, ev_claims.clone(), polys.clone());

            let proof = transcript_p.end();

            let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);

            let expected_output_claims = sumcheck.verify(&mut transcript_v, ev_claims);

            assert_eq!(output_claims, expected_output_claims);

            let SinglePointClaims { point : new_point, evs } = output_claims;
            assert_eq!(polys.iter().map(|poly| evaluate_poly(&poly.to_dense(()), &new_point)).collect_vec(), evs);

        }
    }
}