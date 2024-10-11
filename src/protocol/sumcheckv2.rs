use std::marker::PhantomData;
use std::ops::AddAssign;
use std::sync::Arc;

use ark_ff::{Field, PrimeField};
use ark_std::iterable::Iterable;
use itertools::Itertools;
use liblasso::poly::unipoly::UniPoly;
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator};
use crate::copoly::{Copolynomial, EqPoly};
use crate::polynomial::vecvec::{EQPolyData, VecVecPolynomial};
use super::protocol::{EvalClaim, MultiEvalClaim, PolynomialMapping, Protocol, ProtocolProver, ProtocolVerifier};

#[cfg(feature = "prof")]
use profi::{prof, prof_guard};

pub struct Lincomb<F: PrimeField, const N_INS: usize, const N_OUT: usize> {
    polys: Vec<VecVecPolynomial<F>>,
    func: Arc<dyn Fn(&[&F; N_INS]) -> [F; N_OUT] + Sync + Send>,
    num_ins: usize,
    num_out: usize,
    degree: usize,
    gamma_pows: Option<[F; N_OUT]>,
    current_point: Vec<F>,
    eq_poly_data: EQPolyData<F>,
    previous_claim: F,
}

impl<F: PrimeField, const N_INS: usize, const N_OUT: usize> Lincomb<F, N_INS, N_OUT> {
    pub fn init_eq(&mut self) {
    }
}

struct UnivarFormat<F> {
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
    fn bind(&mut self, f: &F);
    fn unipoly(&mut self) -> UniPoly<F>;
    fn final_evals(&self) -> Vec<F>;
}

impl<F: PrimeField, const N_INS: usize, const N_OUT: usize> Sumcheckable<F> for Lincomb<F, N_INS, N_OUT> {
    fn bind(&mut self, f: &F) {
        self.polys.par_iter_mut().map(|v| v.bind_21(f)).count();
        self.current_point.push(f.clone());
        self.eq_poly_data.bind(f);
    }

    fn unipoly(&mut self) -> UniPoly<F> {
        self.polys.par_iter_mut().map(|v| v.make_21()).count();

        let mut inputs: [&F; N_INS] = self.polys.iter().map(|p| &p.row_pad).collect_vec().try_into().unwrap();


        // TODO: move to precompute, this is know ant parametrisation phase
        let row_lengths = self.polys[0].data.iter().map(|r| r.len()).collect_vec();

        let pad_results = (self.func)(&inputs);

        let mut sum2 = [F::zero(); N_OUT];
        let mut sum1 = [F::zero(); N_OUT];
        for (row_idx, coef) in self.eq_poly_data.row_eq_coefs.iter().enumerate() {

            let mut sum_local2 = [F::zero(); N_OUT];
            let mut sum_local1 = [F::zero(); N_OUT];
            let eq = self.eq_poly_data.get_segment_evals(row_lengths[row_idx] / 2);
            for idx in (0..row_lengths[row_idx]).step_by(2) {

                for (poly_idx, poly) in self.polys.iter().enumerate() {
                    inputs[poly_idx] = &poly.data[row_idx][idx]
                }
                let addition2 = (self.func)(&inputs);

                for (poly_idx, poly) in self.polys.iter().enumerate() {
                    inputs[poly_idx] = &poly.data[row_idx][idx + 1]
                }
                let addition1 = (self.func)(&inputs);
                for i in 0..N_OUT {
                    sum_local2[i] += addition2[i] * eq[idx];
                    sum_local1[i] += addition1[i] * eq[idx];
                }
            }
            let trailing_sum = F::one() - self.eq_poly_data.get_trailing_sum(row_lengths[row_idx] / 2);
            for i in 0..N_OUT {
                sum2[i] += sum_local2[i];
                sum1[i] += sum_local1[i];
                sum2[i] += pad_results[i] * trailing_sum;
                sum1[i] += pad_results[i] * trailing_sum;
            }

            for i in 0..N_OUT {
                sum2[i] *= coef;
                sum1[i] *= coef;
            }
        }

        let mut total2 = sum2[0];
        let mut total1 = sum1[0];
        for i in 1..N_OUT {
            total2 += sum2[i] * self.gamma_pows.as_ref().unwrap()[i];
            total1 += sum1[i] * self.gamma_pows.as_ref().unwrap()[i];
        }

        UnivarFormat::from12(total1, total2, self.eq_poly_data.point[self.eq_poly_data.point_parts.binding_var_idx], self.previous_claim)
    }

    fn final_evals(&self) -> Vec<F> {
        // self.polys.par_iter().map(|poly| poly[0]).collect()
        vec![]
    }
}



// Polyfill
#[cfg(test)]
mod test {
    use std::sync::{Arc, OnceLock};
    use ark_ec::CurveConfig;
    use ark_ec::twisted_edwards::{MontCurveConfig, TECurveConfig};
    use ark_ed_on_bls12_381_bandersnatch::BandersnatchConfig;
    use ark_ff::Field;
    use ark_std::test_rng;
    use itertools::Itertools;
    use num_traits::{One, Zero};
    use crate::copoly::{Copolynomial, EqPoly};
    use crate::grand_add::twisted_edwards_add_l1;
    use crate::polynomial::fragmented::{Fragment, FragmentContent, FragmentedPoly, Shape};
    use crate::polynomial::vecvec::{EQPolyData, EQPolyPointParts, VecVecPolynomial};
    use crate::protocol::protocol::{MultiEvalClaim, PolynomialMapping};
    use crate::protocol::sumcheck::{make_folded_f, FragmentedLincomb, Sumcheckable as OldSumcheckable};
    use crate::utils::make_gamma_pows_static;
    use super::{Lincomb, Sumcheckable as NewSumcheckable};


    #[test]
    fn check_univars() {
        let rng = &mut test_rng();
        let num_vars = 6;
        let num_vertical_vars = 2;
        type F = <BandersnatchConfig as CurveConfig>::BaseField;

        let data = VecVecPolynomial::rand_points::<BandersnatchConfig, _>(
            rng,
            num_vars - num_vertical_vars, num_vertical_vars
        );

        let point = vec![F::zero(); num_vars];

        let claim = MultiEvalClaim {
            points: vec![vec![]],
            evs: vec![vec![
                (0, F::zero()),
                (0, F::zero()),
                (0, F::zero()),
                (0, F::zero()),
            ]],
        };

        let gamma_pows = make_gamma_pows_static::<_, 4>(F::one().double());
        // // 
        // // let mut new_sumcheckable = Lincomb::<F, 3, 4> {
        // //     polys: data.clone(),
        // //     func: Arc::new(|a| twisted_edwards_add_l1(a).as_slice().try_into().unwrap_or_else(|_| panic!())),
        // //     num_ins: 3,
        // //     num_out: 4,
        // //     degree: 2,
        // //     gamma_pows: Some(gamma_pows.clone()),
        // //     current_point: vec![],
        // //     eq_poly_data: EQPolyData {
        // //         point_parts: EQPolyPointParts {
        // //             padded_vars_idx: 0,
        // //             segment_vars_idx: 0,
        // //             binding_var_idx: 0,
        // //         },
        // //         point: vec![],
        // //         multiplier: F::one(),
        // //         row_eq_coefs: vec![],
        // //         pad_multipliers: vec![],
        // //         row_eq_poly_seq: vec![],
        // //         row_eq_poly_prefix_seq: vec![],
        // //         already_bound_vars: 0,
        // //     },
        // //     previous_claim: F::zero(),
        // // };
        // // 
        // // let folded_f = make_folded_f(
        // //     &claim,
        // //     &gamma_pows,
        // //     &PolynomialMapping {
        // //         exec: Arc::new(twisted_edwards_add_l1),
        // //         degree: 2,
        // //         num_i: 3,
        // //         num_o: 4,
        // //     },
        // // );
        // // 
        // // let shape = Arc::new(OnceLock::from(Shape {
        // //     fragments: vec![
        // //         Fragment {
        // //             mem_idx: 0,
        // //             len: 1 << num_vars,
        // //             content: FragmentContent::Data,
        // //             start: 0,
        // //         }
        // //     ],
        // //     data_len: 1 << num_vars,
        // //     num_consts: 0,
        // //     dedup_consts_len: 0,
        // //     split_perm: Arc::new(Default::default()),
        // //     split: Arc::new(Default::default()),
        // // }));
        // // 
        // // let fragmented_data = data.vec().into_iter().map(|p| {
        // //     FragmentedPoly::new(p, vec![], shape.clone())
        // // }).collect_vec();
        // // 
        // // let mut old_eq = EqPoly::new(point.clone());
        // // old_eq.take_shape(shape.clone());
        // // 
        // // let mut old_sumcheckable = FragmentedLincomb {
        // //     polys: fragmented_data,
        // //     splits: None,
        // //     copolys: vec![Box::new(old_eq)],
        // //     folded_f: Some(folded_f),
        // //     degree: 2,
        // // };
        // 
        // assert_eq!(old_sumcheckable.unipoly().as_vec(), new_sumcheckable.unipoly().as_vec());
    }
}