use rayon::iter::ParallelIterator;
use std::marker::PhantomData;
use ark_ff::PrimeField;
use ark_std::iterable::Iterable;
use itertools::{repeat_n, Itertools};
use liblasso::poly::unipoly::UniPoly;
use rayon::iter::IntoParallelRefMutIterator;
use crate::cleanup::proof_transcript::TProofTranscript2;
use crate::cleanup::protocol2::Protocol2;
use crate::cleanup::protocols::gkrs::gkr::GKRLayer;
use crate::cleanup::protocols::sumcheck::{DenseSumcheckObjectSO, EqWrapper, FoldToSumcheckable, GammaWrapper, GenericSumcheckProtocol, SinglePointClaims};
use crate::cleanup::protocols::sumchecks::vecvec_eq::{Sumcheckable, UnivarFormat};
use crate::polynomial::vecvec::{EQPolyData, VecVecPolynomial};
use crate::utils::{eq_eval, eq_poly_sequence, eq_poly_sequence_from_multiplier_last, eq_poly_sequence_last, make_gamma_pows, zip_with_gamma, BindVar21, Make21};
use crate::cleanup::utils::algfn::{AlgFn, AlgFnSO};



pub struct DenseDeg2SumcheckObject<F: PrimeField, Fun: AlgFn<F>> {
    polys: Vec<Vec<F>>,
    func: Fun,
    claims: Vec<F>,
    point: Vec<F>,
}

impl<F: PrimeField, Fun: AlgFn<F>> DenseDeg2SumcheckObject<F, Fun> {
    pub fn new(
        polys: Vec<Vec<F>>,
        func: Fun,
        claims: Vec<F>,
        point: Vec<F>,
    ) -> Self {
        Self {
            polys,
            func,
            claims,
            point,
        }
    }
}

impl<F: PrimeField, Fun: AlgFn<F>> FoldToSumcheckable<F> for DenseDeg2SumcheckObject<F, Fun> {
    type Target = DenseDeg2SumcheckObjectSO<F, Fun>;

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
            self.point,
        )
    }
}

pub struct DenseDeg2SumcheckObjectSO<F: PrimeField, Fun: AlgFn<F>> {
    polys: Vec<Vec<F>>,
    func: Fun,
    gamma_pows: Vec<F>,
    current_point: Vec<F>,
    eq_poly_data: Vec<Vec<F>>,
    claim: F,
    cached_unipoly: Option<UniPoly<F>>,
    multiplier: F,
    point: Vec<F>,
}


impl<F: PrimeField, Fun: AlgFn<F>> DenseDeg2SumcheckObjectSO<F, Fun> {
    pub fn new(
        polys: Vec<Vec<F>>,
        func: Fun,
        gamma_pows: Vec<F>,
        claim: F,
        point: Vec<F>,
    ) -> Self {
        Self {
            eq_poly_data: eq_poly_sequence(&point[0..(point.len() - 1)]),
            polys,
            func,
            claim,
            gamma_pows,
            current_point: vec![],
            cached_unipoly: None,
            multiplier: F::one(),
            point,
        }
    }
}


impl<F: PrimeField, Fun: AlgFn<F>> Sumcheckable<F> for DenseDeg2SumcheckObjectSO<F, Fun> {
    fn bind(&mut self, t: F) {
        self.multiplier *=  F::one() - self.point.last().unwrap() - t + (*self.point.last().unwrap() * t).double();
        self.polys.par_iter_mut().map(|v| v.bind_21(t)).count();
        self.current_point.push(t);
        self.eq_poly_data.pop();
        self.point.pop();
        self.claim = self.cached_unipoly.take().unwrap().evaluate(&t);
    }

    fn unipoly(&mut self) -> UniPoly<F> {
        if let Some(_) = self.cached_unipoly {
            panic!()
        };
        self.polys.par_iter_mut().map(|v: &mut Vec<F>| v.make_21()).count();
        
        let mut inputs = vec![F::zero(); self.polys.len()];

        let pad_results = self.func.exec(&inputs).collect_vec();

        let mut sum2 = vec![F::zero(); self.func.n_outs()];
        let mut sum1 = vec![F::zero(); self.func.n_outs()];
        let mut eq_sum = F::zero();
        for idx in 0..(self.polys[0].len() / 2) {
            for (poly_idx, poly) in self.polys.iter().enumerate() {
                inputs[poly_idx] = poly[2 * idx]
            }
            let addition2 = self.func.exec(&inputs);
            for (add_2, i) in addition2.zip_eq(0..self.func.n_outs()) {
                sum2[i] += add_2 * self.eq_poly_data.last().unwrap()[idx];
            }

            for (poly_idx, poly) in self.polys.iter().enumerate() {
                inputs[poly_idx] = poly[2 * idx + 1]
            }
            let addition1 = self.func.exec(&inputs);
            for (add_1, i) in addition1.zip_eq(0..self.func.n_outs()) {
                sum1[i] += add_1 * self.eq_poly_data.last().unwrap()[idx];
            }

            eq_sum += self.eq_poly_data.last().unwrap()[idx];
        }

        let trailing_sum = F::one() - eq_sum;

        for i in 0..self.func.n_outs() {
            sum2[i] += pad_results[i] * trailing_sum;
            sum1[i] += pad_results[i] * trailing_sum;
        }

        let mut total2 = sum2[0];
        let mut total1 = sum1[0];

        for i in 1..self.func.n_outs() {
            total2 += sum2[i] * self.gamma_pows[i];
            total1 += sum1[i] * self.gamma_pows[i];
        }

        total2 *= self.multiplier;
        total1 *= self.multiplier;


        let unipoly = UnivarFormat::from12(total1, total2, *self.point.last().unwrap(), self.claim);
        self.cached_unipoly = Some(unipoly.clone());

        unipoly
    }

    fn final_evals(&self) -> Vec<F> {
        self.polys.iter().map(|poly| poly[0]).collect() // O_O
    }

    fn challenges(&self) -> &[F] {
        &self.current_point
    }
}


pub struct DenseDeg2Sumcheck<F: PrimeField, Fun: AlgFn<F>> {
    f: Fun,
    num_vars: usize,
    _pd: PhantomData<F>,
}

impl <Transcript: TProofTranscript2, F: PrimeField, Fun: AlgFn<F>> Protocol2<Transcript> for DenseDeg2Sumcheck<F, Fun> {
    type ProverInput = Vec<Vec<F>>;
    type ProverOutput = ();
    type ClaimsBefore = SinglePointClaims<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    fn prove(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        assert_eq!(self.f.deg(), 2);

        let gamma = transcript.challenge(128);
        let SinglePointClaims { point, evs } = claims;
        let so = DenseDeg2SumcheckObject::new(
            advice,
            self.f.clone(),
            evs,
            point,
        );

        let so = so.rlc(gamma);

        let degrees = repeat_n(self.f.deg() + 1, self.num_vars);
        let generic_protocol_config = GenericSumcheckProtocol::new(degrees);

        let ((_, point), poly_evs) = generic_protocol_config.prove(transcript, so.claim, so);

        transcript.write_scalars(&poly_evs);

        (SinglePointClaims {point, evs: poly_evs}, ())
    }

    fn verify(&self, transcript: &mut Transcript, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let degrees = repeat_n(self.f.deg() + 1, self.num_vars);
        let gamma = transcript.challenge(128);
        let SinglePointClaims { point: input_point, evs } = claims;
        let folded_claim = zip_with_gamma(gamma, &evs);
        let generic_protocol_config = GenericSumcheckProtocol::<F, _, DenseDeg2SumcheckObjectSO<F, Fun>>::new(degrees);

        let (ev, output_point) = generic_protocol_config.verify(transcript, folded_claim);

        let poly_evs = transcript.read_scalars(self.f.n_ins());

        assert_eq!(zip_with_gamma(gamma, &self.f.exec(&poly_evs).collect_vec()) * eq_eval(&input_point, &output_point), ev, "Final combinator check has failed.");
        SinglePointClaims {point: output_point, evs: poly_evs}
    }
}


#[cfg(test)]
mod test {
    use std::ops::Index;
    use rstest::*;
    use std::sync::{Arc, OnceLock};
    use ark_bls12_381::Fr;
    use ark_ec::CurveConfig;
    use ark_ec::twisted_edwards::{MontCurveConfig, TECurveConfig};
    use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
    use ark_ff::{Field, PrimeField};
    use ark_std::{test_rng, UniformRand};
    use itertools::{repeat_n, Itertools};
    use num_traits::{One, Zero};
    use crate::copoly::{Copolynomial, EqPoly};
    use crate::cleanup::utils::twisted_edwards_ops::algfns::twisted_edwards_add_l1;
    use crate::utils::{eq_poly_sequence_last, make_gamma_pows_static, DensePolyRndConfig, RandomlyGeneratedPoly};
    use super::{DenseDeg2SumcheckObject, Sumcheckable as NewSumcheckable};
    use crate::cleanup::protocols::sumcheck::{EqWrapper, ExampleSumcheckObjectSO, FoldToSumcheckable, GammaWrapper, SumClaim};
    use super::*;

    #[test]
    fn check_univars() {
        let rng = &mut test_rng();
        type F = <BandersnatchConfig as CurveConfig>::BaseField;

        for i in 0..100 {
            let num_vars = 6;

            let mut data_l = Vec::rand_points::<BandersnatchConfig, _>(
                rng,
                DensePolyRndConfig {
                    num_vars
                }
            );
            let data_r = data_l.clone();

            let data = data_l.into_iter().chain(data_r.into_iter()).collect_vec();

            let gamma = F::one().double();
            let gamma_pows = make_gamma_pows_static::<_, 4>(gamma);

            let f = EqWrapper::new(GammaWrapper::new(twisted_edwards_add_l1(), gamma));
            let f2 = f.clone();

            let mut dense_data = data.iter().map(|p| {
                let mut ret : Vec<_> = p.clone();
                assert_eq!(p.len() % 2, 0);
                ret.extend(repeat_n(Fr::zero(), (1 << num_vars) - ret.len()));
                ret
            }).collect_vec();

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

            let vecvec_sumcheck_builder = DenseDeg2SumcheckObject::new(
                data.to_vec(),
                twisted_edwards_add_l1(),
                vec_claim.try_into().unwrap(),
                point.clone(),
            );

            let mut opt_sumcheckable = vecvec_sumcheck_builder.rlc(gamma_pows[1]);

            let mut dense_sumcheckable = ExampleSumcheckObjectSO::new(
                dense_data,
                f,
                num_vars,
            );

            assert_eq!(dense_sumcheckable.claim(), sum_claim);
            

            for i in 0..num_vars {
                println!("round {}", i);
                let opt_unipoly = opt_sumcheckable.unipoly();
                let dense_unipoly = dense_sumcheckable.unipoly();

                assert_eq!(dense_unipoly.evaluate(&Fr::zero()), opt_unipoly.evaluate(&Fr::zero()));
                assert_eq!(dense_unipoly.evaluate(&Fr::one()), opt_unipoly.evaluate(&Fr::one()));
                assert_eq!(dense_unipoly.evaluate(&Fr::from(2)), opt_unipoly.evaluate(&Fr::from(2)));
                assert_eq!(dense_unipoly.evaluate(&Fr::from(3)), opt_unipoly.evaluate(&Fr::from(3)));

                assert_eq!(dense_unipoly.as_vec(), opt_unipoly.as_vec());

                let t = F::rand(rng);
                opt_sumcheckable.bind(t);
                dense_sumcheckable.bind(t);
                assert_eq!(dense_sumcheckable.claim(), opt_sumcheckable.claim);
            }
        }
    }
}