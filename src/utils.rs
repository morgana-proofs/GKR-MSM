use std::marker::PhantomData;
use std::mem::{transmute, MaybeUninit};
use std::ops::{Add, Index, Mul, Sub};
use std::ptr::read;

use ark_bls12_381::Fr;
use ark_ec::twisted_edwards::{Affine, Projective, TECurveConfig};
use ark_ff::{BigInt, Field, PrimeField};
use ark_std::iterable::Iterable;
use ark_std::rand::Rng;
use ark_std::UniformRand;
use hashcaster::ptr_utils::{AsSharedMUMutPtr, UninitArr, UnsafeIndexRawMut};
use itertools::{repeat_n, Itertools};
use liblasso::poly::dense_mlpoly::DensePolynomial;
#[cfg(feature = "prof")]
use profi::prof;
use rayon::prelude::*;
use crate::cleanup::protocols::splits::SplitIdx;
use crate::cleanup::protocols::sumcheck::{bind_dense_poly, AlgFn};
use crate::protocol::protocol::{MultiEvalClaim, PolynomialMapping};

pub trait TwistedEdwardsConfig {

    const COEFF_D: Self;

    fn mul_by_a(&self) -> Self;

    fn mul_by_d(&self) -> Self;
}


impl TwistedEdwardsConfig for Fr {

    const COEFF_D: Self = Self {
        0: BigInt([12167860994669987632, 4043113551995129031, 6052647550941614584, 3904213385886034240]),
        1: PhantomData
    };

    #[inline(always)]
    fn mul_by_a(&self) -> Self {
        let t = (*self).double().double();
        -(t + *self)
    }

    #[inline(always)]
    fn mul_by_d(&self) -> Self {
        *self * Self::COEFF_D
    }
}


pub fn map_over_poly_legacy<F: PrimeField>(
    ins: &[DensePolynomial<F>],
    f: impl Fn(&[F]) -> Vec<F> + Send + Sync
) -> Vec<DensePolynomial<F>> {
    #[cfg(feature = "prof")]
    prof!("map_over_poly");

    let applications: Vec<Vec<F>> = (0..ins[0].len()).into_par_iter()
        .map(|idx| {
            f(&ins.iter().map(|p| p[idx]).collect_vec())
        }).collect();

    (0..applications.first().unwrap().len()).into_par_iter()
        .map(|idx| {
            DensePolynomial::new(applications.par_iter().map(|v| v[idx]).collect())
        }).collect::<Vec<DensePolynomial::<F>>>().try_into().unwrap()
}

pub fn map_over_poly<F: Field>(
    ins: &[&[F]],
    f: PolynomialMapping<F>,
) -> Vec<Vec<F>> {
    #[cfg(feature = "prof")]
    prof!("map_over_poly");
    let applications: Vec<Vec<F>> = (0..ins[0].len()).into_par_iter()
        .map(|idx| {
            (f.exec)(&ins.iter().map(|p| p[idx]).collect_vec())
        }).collect();

    (0..f.num_o).into_par_iter()
        .map(|idx| {
            applications.iter().map(|v| v[idx]).collect()
        })
        .collect::<Vec<Vec<F>>>()
}


pub fn scale<F: Field + TwistedEdwardsConfig, T: Fn (&[F]) -> Vec<F>>(f: T) -> impl Fn (&[F]) -> Vec<F> {
    move |data: &[F]| -> Vec<F> {
        let (pts, factor) = data.split_at(data.len() - 1);
        f(&pts.to_vec()).par_iter().map(|p| *p * factor[0]).collect()
    }
}

pub fn fold_with_coef<F: Field>(evals: &[F], layer_coef: F) -> Vec<F> {
    assert_eq!(evals.len() % 2, 0);
    let half = evals.len() / 2;
    (0..half)
        .map(|i| evals[i] + layer_coef * (evals[half + i] - evals[i]))
        .collect()
}


pub fn make_gamma_pows_legacy<F: PrimeField>(claims: &MultiEvalClaim<F>, gamma: F) -> Vec<F> {
    let num_claims = claims.evs.iter().fold(0, |acc, upd| acc + upd.len());

    let mut gamma_pows = vec![F::one(), gamma];
    for i in 2..num_claims {
        let tmp = gamma_pows[i-1];
        gamma_pows.push(tmp * gamma);
    }
    gamma_pows
}

pub fn make_gamma_pows_static<F: PrimeField, const N_POWS: usize>(gamma: F) -> [F; N_POWS] {
    let mut gamma_pows = Vec::with_capacity(N_POWS);
    gamma_pows.push(F::one());
    gamma_pows.push(gamma);
    for i in 2..N_POWS {
        let tmp = gamma_pows[i - 1];
        gamma_pows.push(tmp * gamma);
    };
    gamma_pows.try_into().unwrap_or_else(|v: Vec<F>| panic!("Expected a Vec of length {} but it was {}", N_POWS, v.len()))
}

pub fn make_gamma_pows<F: PrimeField>(gamma: F, count: usize) -> Vec<F> {
    let mut gamma_pows = Vec::with_capacity(count);
    gamma_pows.push(F::one());
    gamma_pows.push(gamma);
    for i in 2..count {
        let tmp = gamma_pows[i - 1];
        gamma_pows.push(tmp * gamma);
    };
    gamma_pows
}

pub fn zip_with_gamma<F: PrimeField>(gamma: F, vals: &[F]) -> F {
    let l = vals.len();
    if l == 0 {
        return F::zero();
    }
    let mut ret = vals[l - 1];
    for i in 0 .. (l - 1) {
        ret *= gamma;
        ret += vals[l - i - 2];
    };
    ret
}

pub fn eq_eval<F: PrimeField>(p1: &[F], p2: &[F]) -> F {
    p1.iter().zip_eq(p2.iter()).map(|(x1, x2)| {
        F::one() - x1 - x2 + (*x1 * x2).double()
    }).product()
}

pub fn split_into_chunks_balanced<T>(arr: &[T], num_threads: usize) -> impl Iterator<Item = &[T]> + '_ {
    let l = arr.len();
    let base_size = l / num_threads;
    let num_large_chunks = l - base_size * num_threads;

    let (m_hi, m_lo) = arr.split_at(num_large_chunks * num_threads);
    let chunks_hi = m_hi.chunks(base_size + 1);
    let chunks_lo = m_lo.chunks(base_size);
    chunks_hi.chain(chunks_lo)
}

pub fn fix_var_top<F>(vec: &mut Vec<F>, v: F) {
    vec.push(v);
}

pub fn fix_var_bot<F>(vec: &mut Vec<F>, v: F) {
    vec.insert(0, v);
}

pub fn random_point<F: UniformRand>(gen: &mut impl Rng, num_vars: usize) -> Vec<F> {
    (0..num_vars).map(|_| F::rand(gen)).collect_vec()
}

pub trait EvaluateAtPoint<F: PrimeField> {
    fn evaluate(&self, p: &[F]) -> F;
}
impl<F: PrimeField> EvaluateAtPoint<F> for Vec<F> {
    fn evaluate(&self, p: &[F]) -> F {
        assert_eq!(self.len(), 1 << p.len());
        let mut tmp = Some(self.clone());
        for f in p.iter().rev() {
            tmp = Some(tmp.unwrap().bind(*f));
        }
        tmp.unwrap()[0]
    }
}
pub trait BindVar<F: PrimeField> {
    fn bind(self, t: F) -> Self;
}
impl<F: PrimeField> BindVar<F> for Vec<F> {
    fn bind(mut self, t: F) -> Self {
        bind_dense_poly(&mut self, t);
        self
    }
}
pub trait BindVar21<F: PrimeField> {
    fn bind_21(&mut self, t: F);
}
impl<F: PrimeField> BindVar21<F> for Vec<F> {
    fn bind_21(&mut self, t: F) {
        let tm1 = t - F::one();
        let iter = self.iter();

        for i in 0..(self.len() / 2) {
            self[i] = self[2 * i + 1] + tm1 * (self[2 * i] - self[2 * i + 1]);
        }
        let mut i = self.len() / 2;
        if i % 2 == 1 {
            self[i] = F::zero();
            i += 1;
        }
        self.truncate(i);
    }
}
pub trait Make21<F: PrimeField> {
    fn make_21(&mut self);
}
impl<F: PrimeField> Make21<F> for Vec<F> {
    fn make_21(&mut self) {

        let iter = self.chunks_mut(2);
        // let iter = self.par_chunks_mut(2);

        iter.map(|c| {
            for i in 0..(c.len() / 2) {
                c[2 * i] = c[2 * i + 1].double() - c[2 * i];
            }
        }).count();
    }
}
pub trait MapSplit<F: PrimeField>: Sized {
    fn algfn_map_split<Fnc: AlgFn<F>>(
        polys: &[Self],
        func: Fnc,
        var_idx: SplitIdx,
        bundle_size: usize,
    ) -> Vec<Self>;

    fn algfn_map<Fnc: AlgFn<F>>(
        polys: &[Self],
        func: Fnc
    ) -> Vec<Self>;
}
impl<F: PrimeField> MapSplit<F> for Vec<F> {
    fn algfn_map_split<Fnc: AlgFn<F>>(polys: &[Self], func: Fnc, var_idx: SplitIdx, bundle_size: usize) -> Vec<Self> {
        let mut l_outs = (0..func.n_outs()).map(|_| UninitArr::new(polys[0].len() / 2)).collect_vec();
        let mut r_outs = (0..func.n_outs()).map(|_| UninitArr::new(polys[0].len() / 2)).collect_vec();
        
        let chunk_size = 3;
        
        let mut iter_l_out = l_outs.iter_mut().map(|i| i.chunks_mut(chunk_size)).collect_vec();
        let mut iter_r_out = r_outs.iter_mut().map(|i| i.chunks_mut(chunk_size)).collect_vec();
        let mut iter_ins = polys.iter().map(|i| i.chunks(2 * chunk_size)).collect_vec();

        for _ in 0..iter_ins[0].len() {
            let input_chunks = iter_ins.iter_mut().map(|c| c.next().unwrap()).collect_vec();
            let mut inputs = input_chunks.iter().map(|c| c[0]).collect_vec();
            let mut l_output_chunks = iter_l_out.iter_mut().map(|c| c.next().unwrap()).collect_vec();
            let mut r_output_chunks = iter_r_out.iter_mut().map(|c| c.next().unwrap()).collect_vec();

            for idx in 0..input_chunks[0].len() {
                let out = func.exec(&inputs);
                for (tgt, val) in out.enumerate() {
                    if (idx % 2 == 0) {
                        l_output_chunks[tgt][idx / 2].write(val);
                    } else {
                        r_output_chunks[tgt][idx / 2].write(val);
                    }
                }
                if idx + 1 < input_chunks[0].len() {
                    inputs = input_chunks.iter().map(|c| c[idx + 1]).collect_vec();
                }
            }
        }

        l_outs.into_iter().chunks(bundle_size).into_iter().interleave(r_outs.into_iter().chunks(bundle_size).into_iter()).flatten().map(|data| {
            unsafe { data.assume_init() }    
        }).collect_vec()
    }

    fn algfn_map<Fnc: AlgFn<F>>(polys: &[Self], func: Fnc) -> Vec<Self> {
        let mut outs = (0..func.n_outs()).map(|_| UninitArr::new(polys[0].len())).collect_vec();
        let mut iter_ins = polys.iter().map(|i| i.chunks(1)).collect_vec();
        let mut iter_out = outs.iter_mut().map(|i| i.chunks_mut(1)).collect_vec();

        for _ in 0..iter_ins[0].len() {
            let input_chunks = iter_ins.iter_mut().map(|c| c.next().unwrap()).collect_vec();
            let mut inputs = input_chunks.iter().map(|c| c[0]).collect_vec();
            let mut output_chunks = iter_out.iter_mut().map(|c| c.next().unwrap()).collect_vec();

            for idx in 0..input_chunks[0].len() {
                let out = func.exec(&inputs);
                for (tgt, val) in out.enumerate() {
                    output_chunks[tgt][idx].write(val);
                }
                if idx + 1 < input_chunks[0].len() {
                    inputs = input_chunks.iter().map(|c| c[idx + 1]).collect_vec();
                }
            }
        }
        unsafe { outs.into_iter().map(|o| o.assume_init()).collect_vec() }
    }
}
pub trait RandomlyGeneratedPoly<F: PrimeField>: Sized {
    type Config;
    fn rand_points<
        CC: TECurveConfig<BaseField=F>,
        RNG: Rng,
    >(rng: &mut RNG, cfg: Self::Config) -> [Self; 3];

    fn rand_points_affine<
        CC: TECurveConfig<BaseField=F>,
        RNG: Rng,
    >(rng: &mut RNG, cfg: Self::Config) -> [Self; 2];

}
pub struct DensePolyRndConfig {
    pub num_vars: usize,
}
impl<F: PrimeField> RandomlyGeneratedPoly<F> for Vec<F> {
    type Config = DensePolyRndConfig;

    fn rand_points<CC: TECurveConfig<BaseField=F>, RNG: Rng>(rng: &mut RNG, cfg: Self::Config) -> [Self; 3] {
        let data = (0..(rng.next_u64() as usize % ((1 << (cfg.num_vars - 1)) + 1)) * 2).map(|_| {
            let p = Projective::<CC>::rand(rng);
            (p.x, p.y, p.z)
        }).collect_vec();

        let (x, y, z) = data.into_iter().multiunzip();

        [
            x,
            y,
            z
        ]
    }

    fn rand_points_affine<CC: TECurveConfig<BaseField=F>, RNG: Rng>(rng: &mut RNG, cfg: Self::Config) -> [Self; 2] {
        let data = (0..(rng.next_u64() as usize % (1 << (cfg.num_vars - 1) + 1)) * 2).map(|_| {
            let p = Affine::<CC>::rand(rng);
            (p.x, p.y)
        }).collect_vec();

        let (x, y) = data.into_iter().multiunzip();

        [
            x,
            y,
        ]
    }
}
pub trait Densify<F: Clone> {
    type Hint;
    fn to_dense(&self, hint: Self::Hint) -> Vec<F>;
}
impl<F: PrimeField> Densify<F> for Vec<F> {
    type Hint = usize;

    fn to_dense(&self, hint: Self::Hint) -> Vec<F> {
        let mut out = self.clone();
        out.extend(repeat_n(F::zero(), (1 << hint) - out.len()));
        out
    }
}

#[cfg(feature = "parallel")]
pub trait CfgParallel: Send + Sync {}
#[cfg(not(feature = "parallel"))]
pub trait CfgParallel {}
#[cfg(feature = "parallel")]
impl<F: Send + Sync> CfgParallel for F {}
#[cfg(not(feature = "parallel"))]
impl<F> CfgParallel for F {}


pub fn padded_eq_poly_sequence<F: PrimeField>(padding_size: usize, pt: &[F]) -> Vec<Vec<F>> {
    let l = pt.len();
    let mut ret = Vec::with_capacity(l + 1);
    ret.push(vec![F::one()]);
    for i in 1..=padding_size {
        ret.push(vec![ret[i - 1][0] * (F::one() - pt[i - 1])]);
    }

    for i in (padding_size + 1)..=l {
        let last = &ret[i - 1];
        let multiplier = &pt[i - 1];
        let mut incoming = UninitArr::<F>::new(1 << (i - padding_size));
        unsafe {
            let ptr = incoming.as_shared_mut_ptr();
            #[cfg(not(feature = "parallel"))]
            let iter = (0 .. (1 << (i - 1 - padding_size))).into_iter();

            #[cfg(feature = "parallel")]
            let iter = (0 .. (1 << (i - 1 - padding_size))).into_par_iter();

            iter.map(|j|{
                let w = &last[j];
                let m = *multiplier * w;
                *ptr.get_mut(2 * j) = *w - m;
                *ptr.get_mut(2 * j + 1) = m;
            }).count();
            ret.push(incoming.assume_init());
        }
    }

    ret
}

pub fn eq_poly_sequence_from_multiplier<F: PrimeField>(multiplier: F, pt: &[F]) -> Vec<Vec<F>> {
    let l = pt.len();
    let mut ret = Vec::with_capacity(l + 1);
    ret.push(vec![multiplier]);

    for i in 1..=l {
        let last = &ret[i - 1];
        let multiplier = &pt[i - 1];
        let mut incoming = UninitArr::<F>::new(1 << i);
        unsafe {
            let ptr = incoming.as_shared_mut_ptr();
            #[cfg(not(feature = "parallel"))]
            let iter = (0 .. (1 << (i - 1))).into_iter();

            #[cfg(feature = "parallel")]
            let iter = (0 .. 1 << (i - 1)).into_par_iter();

            iter.map(|j|{
                let w = &last[j];
                let m = *multiplier * w;
                *ptr.get_mut(2 * j) = *w - m;
                *ptr.get_mut(2 * j + 1) = m;
            }).count();
            ret.push(incoming.assume_init());
        }
    }

    ret
}

pub fn eq_poly_sequence<F: PrimeField>(pt: &[F]) -> Vec<Vec<F>> {
    eq_poly_sequence_from_multiplier(F::one(), pt)
}

pub fn eq_poly_sequence_last<F: PrimeField>(pt: &[F]) -> Option<Vec<F>> {
    eq_poly_sequence(pt).pop()
}

pub fn eq_poly_sequence_from_multiplier_last<F: PrimeField>(mul: F, pt: &[F]) -> Option<Vec<F>> {
    eq_poly_sequence_from_multiplier(mul, pt).pop()
}

#[cfg(feature = "memprof")]
pub fn memprof(l: &str) {
    use jemalloc_ctl::{epoch, stats};
    epoch::advance().unwrap();
    let allocated = stats::allocated::read().unwrap();
    let resident = stats::resident::read().unwrap();
    println!("{}: {:.3}Gb ({} bytes) allocated / {:.3}Gb ({} bytes) resident", l, allocated as f64 / 1024f64 / 1024f64 / 1024f64, allocated, resident as f64 / 1024f64 / 1024f64 / 1024f64, resident);
}


#[cfg(test)]
mod test {
    use std::sync::Arc;
    use ark_ec::CurveConfig;
    use ark_ed_on_bls12_381_bandersnatch::{BandersnatchConfig, Fr};
    use ark_std::{test_rng, UniformRand};
    use itertools::Itertools;
    use num_traits::One;
    use crate::cleanup::protocols::splits::SplitIdx;
    use crate::cleanup::utils::algfn::ArcedAlgFn;
    use crate::polynomial::vecvec::{vecvec_map_split, VecVecPolynomial};
    use crate::protocol::protocol::PolynomialMapping;
    use crate::utils::{eq_poly_sequence_from_multiplier, map_over_poly, padded_eq_poly_sequence, DensePolyRndConfig, Densify, MapSplit, RandomlyGeneratedPoly};

    #[test]
    fn eq_poly_seq() {
        let gen = &mut test_rng();
        let num_vars = 8;
        let num_padded = 3;

        let point = (0..num_vars).map(|_| Fr::rand(gen)).collect_vec();

        let mut pad_multipliers = point[0..num_padded].to_vec();
        let total_multiplier = pad_multipliers.iter_mut().fold(Fr::one(), |mut acc, val| {
            acc *= Fr::one() - *val;
            *val = acc;
            acc
        });

        let row_eq_poly_seq = eq_poly_sequence_from_multiplier(total_multiplier, &point[num_padded..num_vars]);

        let padded_eq_poly_seq = padded_eq_poly_sequence(num_padded, &point);
        for i in 0..num_padded {
            assert_eq!(padded_eq_poly_seq[i + 1][0], pad_multipliers[i]);
        }
        for i in (num_padded - 1)..num_vars {
            assert_eq!(padded_eq_poly_seq[i + 1], row_eq_poly_seq[i + 1 - num_padded]);
        }
    }
    type F = <BandersnatchConfig as CurveConfig>::BaseField;

    fn foo(ins: &[&F]) -> Vec<F> {
        vec![
            ins[0] + ins[1],
            ins[1] + ins[2],
        ]
    }
    fn blah(ins: &[F]) -> Vec<F> {
        let tmp = ins.iter().collect_vec();
        let tmp = tmp.as_slice();
        foo(&tmp)
    }
    #[test]
    fn vec_algfn_map() {
        let gen = &mut test_rng();
        let n_args = 3;
        let num_vars = 5;

        let data = Vec::rand_points::<BandersnatchConfig, _>(gen, DensePolyRndConfig {
            num_vars,
        });
        let dense_data = data.iter().map(|p| p.to_dense(num_vars)).collect_vec();

        let out = Vec::algfn_map(data.as_slice().try_into().unwrap(), ArcedAlgFn::new(Arc::new(foo), 3, 2, 1));
        let expected_out = map_over_poly(&dense_data.iter().map(|p| p.as_slice()).collect_vec().as_slice(), PolynomialMapping {
            exec: Arc::new(blah),
            degree: 1,
            num_i: 3,
            num_o: 2,
        });

        let dense_out = out.into_iter().map(|p| p.to_dense(num_vars)).collect_vec();

        assert_eq!(dense_out, expected_out)
    }

    #[test]
    fn map_split() {
        let gen = &mut test_rng();
        let num_vars = 5; 
        for i in 0..100 {
            let n_args = 3;

            let data = Vec::rand_points::<BandersnatchConfig, _>(gen, DensePolyRndConfig {num_vars});
            let dense_data = data.iter().map(|p| p.to_dense(num_vars)).collect_vec();

            let out = Vec::algfn_map_split(data.as_slice().try_into().unwrap(), ArcedAlgFn::new(Arc::new(foo), 3, 2, 1), SplitIdx::LO(0), 1);
            let expected_out = map_over_poly(&dense_data.iter().map(|p| p.as_slice()).collect_vec().as_slice(), PolynomialMapping {
                exec: Arc::new(blah),
                degree: 1,
                num_i: 3,
                num_o: 2,
            });
            let (out0, out1) = out.iter().tee();
            let out0 = out0.step_by(2);
            let out1 = out1.skip(1).step_by(2);

            let dense_out = out0.zip_eq(out1).map(|(l, r)| {
                l.to_dense(num_vars - 1).into_iter().interleave(r.to_dense(num_vars - 1).into_iter()).collect_vec()
            }).collect_vec();

            assert_eq!(dense_out, expected_out);
        }
    }
}