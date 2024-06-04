use std::iter::repeat;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ops::Index;
use std::sync::Arc;
use ark_ff::{Field, PrimeField};
use ark_std::iterable::Iterable;
use ark_std::rand::{Rng, RngCore};
use itertools::{Itertools, repeat_n};
use liblasso::poly::dense_mlpoly::DensePolynomial;
use liblasso::utils::math::Math;
use rayon::prelude::*;

pub trait SplitablePoly<F>: Sized {
    fn split_bot(&self) -> (Self, Self);
}

impl<F: PrimeField> SplitablePoly<F> for DensePolynomial<F> {
    fn split_bot(&self) -> (Self, Self) {
        (
            DensePolynomial::new(self.vec().iter().step_by(2).map(|x| *x).collect_vec()),
            DensePolynomial::new(self.vec().iter().skip(1).step_by(2).map(|x| *x).collect_vec())
        )
    }
}

/// Evaluate a multilinear polynomial in coefficient form in a point.
/// Rewritten to eventually unbind us from liblasso's DensePolynomial dependency. 
/// Will consume the polynomial in process.
/// Method from DensePolynomial requires 1.5n multiplications as far as I understand, so
/// it is possible that cloning is cheaper.
pub fn evaluate_exact<F: Field>(poly: &mut [F], point: &[F]) -> F {
    assert!(poly.len() == 1 << point.len());

    let mut half_size = poly.len() >> 1;
    let mut poly = poly;
    for i in 0..point.len() {
        let p = point[i];
        let (l, r) = poly.split_at_mut(half_size);
        r.par_iter_mut().enumerate().map(|(i, ri)| {*ri -= l[i]; *ri *= p}).count();
        l.par_iter_mut().enumerate().map(|(i, li)| *li += r[i]).count();
        half_size >>= 1;
        poly = l;
    }

    poly[0]
}

/// Similarly, this does actually consume a segment.
pub fn segment_evaluate<F: Field>(segment: &mut [F], continuation: F, point: &[F]) -> F {
    let l = segment.len();
    let nvars = point.len();
    if l == 1 << nvars {
        return evaluate_exact(segment, point)
    }
    assert!(l <= 1 << nvars);
    
    let mut multiplier = F::one();

    segment.par_iter_mut().map(|x| *x -= continuation).count();

    let mut segment = segment;
    let mut chunk;
    let mut acc = F::zero();

    // Note that edge case where l == 1 << nvars is done earlier.
    
    // To understand how this cycle works, let's index each possible chunk by a bit sequence.
    // For example, [0..N/2] is 0, [N/2..N] is 1, et cetera. I.e. it is a sequence of leading
    // bits of indices that are constant in this chunk.
    // When we split our segment into chunks, we need to adjust each evaluation of eq(point[i+1..], _)
    // by a constant factor that eq(point[0..i], _) takes on the whole chunk (if we imagine it embedded
    // in the original polynomial).
    for i in 0 .. nvars {
        if (l >> (nvars - i - 1)) % 2 == 1 {
            (chunk, segment) = segment.split_at_mut(1 << (nvars - i - 1));
            // If we are in this branch, we get a segment which's last bit of indexing bit sequence is 0,
            // so it is multiplied by 1 - point[i]. And all next segments will be to the right of it, so
            // their corresponding multiplier is adjusted by point[i].
            acc += multiplier * (F::one() - point[i]) * evaluate_exact(chunk, &point[i + 1 ..]);
            multiplier *= point[i];
        } else {
            // And if we are in this branch, multiplier is adjusted by 1-point[i], because we are just appending
            // 0-s to the indexing sequence of an upcoming chunk.
            multiplier *= F::one() - point[i];
        }
    }

    acc + continuation
}

#[derive(Eq, PartialEq, Debug, Clone)]
pub enum NestedValues<F: Field> {
    Flat(Vec<F>),
    Nested(Vec<NestedPoly<F>>),
}

#[derive(Eq, PartialEq, Debug, Clone)]
pub struct NestedPoly<F: Field> {
    values: NestedValues<F>,
    continuation: Option<F>,
}

#[derive(Eq, PartialEq, Debug, Clone)]
pub struct NestedPolynomial<F: Field> {
    values: NestedPoly<F>,
    layer_num_vars: Vec<usize>,
}

#[derive(Copy, Clone)]
struct NumVarsWrapper<'a> {
    layer_num_vars: &'a[usize],
    sum_left: usize,
    current_idx: usize,
}

impl<F: Field> NestedValues<F> {
    pub fn len(&self) -> usize {
        match &self {
            NestedValues::Flat(v) => v.len(),
            NestedValues::Nested(v) => v.len(),
        }
    }
}

impl<'a> NumVarsWrapper<'a> {
    fn new(layer_num_vars: &'a[usize]) -> Self {
        Self {
            layer_num_vars,
            sum_left: layer_num_vars.iter().sum(),
            current_idx: 0,
        }
    }

    fn depth(&self) -> usize {
        self.current_idx
    }
    fn height(&self) -> usize {
        self.layer_num_vars.len() - self.current_idx - 1
    }

    fn current(&self) -> usize {
        self.layer_num_vars[self.current_idx]
    }

    fn total(&self) -> usize {
        self.sum_left
    }

    fn total_lower(&self) -> usize {
        self.total() - self.current()
    }

    fn step_down(mut self) -> Self {
        self.sum_left -= self.current();
        self.current_idx += 1;
        self
    }
    fn step_up(mut self) -> Self {
        self.sum_left += self.current();
        self.current_idx -= 1;
        self
    }
}

impl<F: Field> NestedPoly<F> {
    fn split_bot(&self) -> (Self, Self) {
        match &self.values {
            NestedValues::Flat(v) => {
                let (a, b) = v.iter().tee();
                (
                    NestedPoly {
                        values: NestedValues::Flat(a.step_by(2).map(|x| *x).collect()),
                        continuation: self.continuation,
                    },
                    NestedPoly {
                        values: NestedValues::Flat(b.skip(1).step_by(2).map(|x| *x).collect()),
                        continuation: self.continuation,
                    }
                )
            }
            NestedValues::Nested(inner) => {
                let (l, r) = inner.iter().map(|p| p.split_bot()).unzip();
                (
                    NestedPoly {
                        values: NestedValues::Nested(l),
                        continuation: self.continuation,
                    },
                    NestedPoly {
                        values: NestedValues::Nested(r),
                        continuation: self.continuation,
                    }
                )
            }
        }
    }

    fn bound_var_bot(&mut self, r: &F) {
        match &mut self.values {
            NestedValues::Flat(v) => {
                for i in 0..v.len() / 2 {
                    v[i] = v[2 * i] + *r * (v[2 * i + 1] - v[2 * i]);
                }
                let len = v.len();
                if v.len() % 2 == 1 {
                    v[len / 2] = v[len - 1] + *r * (self.continuation.unwrap() - v[len - 1]);
                }
                v.truncate((len + 1) / 2);
            }
            NestedValues::Nested(inner) => {
                inner.par_iter_mut().map(|sub| {
                    sub.bound_var_bot(r);
                }).count();
            }
        }
    }

    pub fn from_values_uncontinued(values: Vec<F>) -> Self {
        Self {values: NestedValues::Flat(values), continuation: None}
    }

    pub fn from_values(values: Vec<F>, continuation: F) -> Self {
        Self {values: NestedValues::Flat(values), continuation: Some(continuation)}
    }

    pub fn from_polys_uncontinued(polys: Vec<NestedPoly<F>>) -> Self {
        if polys.len() > 0 {
            polys
                .iter().count();
        }
        Self {values: NestedValues::Nested(polys), continuation: None}
    }

    pub fn from_polys(polys: Vec<NestedPoly<F>>, continuation: F) -> Self {
        if polys.len() > 0 {
            polys
                .iter().count();
        }
        Self {values: NestedValues::Nested(polys), continuation: Some(continuation)}
    }

    fn evaluate(&self, point: &[F], num_vars: NumVarsWrapper) -> F {
        assert_eq!(point.len(), num_vars.total());
        let (point_ext, point_in) = point.split_at(num_vars.current());
        let mut segment = match &self.values {
            NestedValues::Flat(values) => values.clone(),
            NestedValues::Nested(polys) => polys.into_par_iter().map(|poly| poly.evaluate(point_in, num_vars.step_down())).collect(),
        };
        segment_evaluate(&mut segment, self.continuation.unwrap(), point_ext)
    }

    fn vec(&self, num_vars: NumVarsWrapper) -> Vec<F> {
        match &self.values {
            NestedValues::Flat(v) => {
                v.clone().into_iter().chain(repeat(self.continuation.unwrap())).take(1 << num_vars.current()).collect_vec()
            }
            NestedValues::Nested(v) => {
                let segment_len = num_vars.total();
                let vs = v.iter().map(|p| p.vec(num_vars.step_down())).collect_vec();
                vs.into_iter().flatten().chain(repeat(self.continuation.unwrap())).take(1 << segment_len).collect_vec()
            }
        }
    }

    fn assert_normalized(&self, num_vars: NumVarsWrapper) {
        if !(num_vars.depth() == 0 && num_vars.height() == 0) {
            assert_ne!(num_vars.current(), 0);
        }
        assert!(self.values.len() <= (1 << num_vars.current()));
        if let NestedValues::Nested(inner) = &self.values {
            inner.par_iter().map(|p| p.assert_normalized(num_vars.step_down())).count();
        }
    }

    /// normalize an inner 0-variable node by replacing its parameters with ones from a child node
    fn normalize_from_lower(&mut self) {
        match &mut self.values {
            NestedValues::Flat(_) => unreachable!(),
            NestedValues::Nested(v) => {
               match v.pop() {
                   None => {
                       self.values = NestedValues::Nested(vec![]);
                   }
                   Some(v) => {
                       self.values = v.values;
                       self.continuation = v.continuation;
                   }
               }
            }
        }
    }

    /// normalize bottom-layer nodes by combining them in the previous level
    fn normalize_child(&mut self) {
        match &mut self.values {
            NestedValues::Flat(_) => {},
            NestedValues::Nested(v) => {
                self.values = NestedValues::Flat(v.iter_mut().map(|p| match &mut p.values {
                    NestedValues::Flat(x) => {
                         x.pop().unwrap_or(p.continuation.unwrap())
                    },
                    NestedValues::Nested(_) => unreachable!(),
                }).collect_vec());
            }
        }
    }

    fn normalize_inner(&mut self, num_vars: NumVarsWrapper) {
        let next_num_vars = num_vars.step_down();
        match &mut self.values {
            NestedValues::Flat(_) => {}
            NestedValues::Nested(inner) => {
                inner.par_iter_mut().map(|i| i.normalize_inner(next_num_vars)).count();
            }
        }
        if num_vars.current() == 0 && num_vars.height() != 0 {
                self.normalize_from_lower()
        }
    }

    fn normalize_leafs(&mut self, num_vars: NumVarsWrapper) {
        match &mut self.values {
            NestedValues::Flat(_) => {}
            NestedValues::Nested(inner) => {
                if num_vars.height() != 0 {
                    let next_num_vars = num_vars.step_down();
                    inner.par_iter_mut().map(|i| i.normalize_leafs(next_num_vars)).count();
                }
            }
        }
        if num_vars.height() <= 1 && num_vars.total_lower() == 0 {
            self.normalize_child();
        }
    }

    fn index(&self, idx: usize, num_vars: NumVarsWrapper) -> &F {
        match &self.values {
            NestedValues::Flat(v) => {v.get(idx).unwrap_or(&self.continuation.as_ref().unwrap())}
            NestedValues::Nested(v) => {v.get(idx / (1 << num_vars.total_lower())).map_or(&self.continuation.as_ref().unwrap(), |v| v.index(idx % (1 << num_vars.total_lower()), num_vars.step_down()))}
        }
    }

    pub fn merge_structure(&mut self, other: &Self, num_vars: NumVarsWrapper) {
        match (&other.values, &mut self.values) {
            (NestedValues::Flat(s), NestedValues::Flat(t)) => {
                t.extend(repeat_n(F::zero(), s.len() - t.len()));
            },
            (NestedValues::Nested(s), NestedValues::Nested(t)) => {
                match num_vars.height() {
                    0 => unreachable!(),
                    1 => {
                        t.extend(repeat_n(NestedPoly::from_values_uncontinued(vec![]), s.len() - t.len()))
                    },
                    _ => {
                        t.extend(repeat_n(NestedPoly::from_polys_uncontinued(vec![]), s.len() - t.len()))
                    },
                }
            },
            _ => unreachable!(),
        }
    }
}

impl<F: Field> NestedPolynomial<F> {
    pub fn new(values: NestedPoly<F>, layer_num_vars: Vec<usize>) -> Self {
        values.assert_normalized(NumVarsWrapper::new(&layer_num_vars));
        Self {
            values,
            layer_num_vars,
        }
    }

    pub fn from_values(values: Vec<F>, num_vars: usize, continuation: F) -> Self {
        assert!(values.len() <= (1 << num_vars));
        Self {
            values: NestedPoly::from_values(values, continuation),
            layer_num_vars: vec![num_vars],
        }
    }

    pub fn empty_from_structure(layer_num_vars: &[usize]) -> Self {
        if layer_num_vars.len() > 1 {
            Self {
                values: NestedPoly::from_polys_uncontinued(
                    vec![],
                ),
                layer_num_vars: layer_num_vars.to_vec(),
            }
        } else {
            Self {
                values: NestedPoly::from_values_uncontinued(
                    vec![],
                ),
                layer_num_vars: layer_num_vars.to_vec(),
            }
        }
    }
    pub fn merge_structure(&mut self, other: &Self) {
        assert_eq!(self.layer_num_vars, other.layer_num_vars);
        self.values.merge_structure(&other.values, NumVarsWrapper::new(&other.layer_num_vars))
    }

    pub fn num_vars(&self) -> usize {
        self.layer_num_vars.iter().sum()
    }

    pub fn vec(&self) -> Vec<F> {
        self.values.vec(NumVarsWrapper::new(&self.layer_num_vars))
    }

    pub fn len(&self) -> usize {
        1 << self.layer_num_vars.iter().sum::<usize>()
    }

    pub fn evaluate(&self, point: &[F]) -> F {
        self.values.evaluate(point, NumVarsWrapper::new(&self.layer_num_vars))
    }

    pub fn bound_var_bot(&mut self, r: &F) {
        self.values.bound_var_bot(r);
        self.drop_variable_bot();
    }

    pub fn split_bot(&self) -> (Self, Self) {
        let (l, r) = self.values.split_bot();
        let (mut l, mut r) = (
            Self {
                values: l,
                layer_num_vars: self.layer_num_vars.clone(),
            },
            Self {
                values: r,
                layer_num_vars: self.layer_num_vars.clone(),
            }
        );
        l.drop_variable_bot();
        r.drop_variable_bot();
        (l, r)
    }

    pub fn map_over_poly(
        ins: &[NestedPolynomial<F>],
        f: impl Fn(&[F]) -> Vec<F> + Send + Sync
    ) -> Vec<NestedPolynomial<F>> {
        assert!(ins.len() > 0);
        let layer_num_vars = &ins.first().unwrap().layer_num_vars;
        let mut out = NestedPolynomial::empty_from_structure(&layer_num_vars);
        for p in ins {
            out.merge_structure(p);
        }
        todo!();
    }

    fn drop_variable_bot(&mut self) {
        *self.layer_num_vars.last_mut().unwrap() -= 1;
        if self.layer_num_vars.last().unwrap() == &0 {
            self.normalize_leafs();
        }
    }
    fn normalize_leafs(&mut self) {
        if self.layer_num_vars.len() > 1 {
            self.layer_num_vars = self.layer_num_vars.iter().filter(|&&s| s != 0).map(|&s| s).collect_vec();
        }
        self.values.normalize_leafs(NumVarsWrapper::new(&self.layer_num_vars));
    }

    fn normalize(&mut self) {
        self.values.normalize_inner(NumVarsWrapper::new(&self.layer_num_vars));
        self.normalize_leafs();
    }

    fn index(&self, idx: usize) -> &F {
        self.values.index(idx, NumVarsWrapper::new(&self.layer_num_vars))
    }

    fn assert_normalized(&self) {
        if self.layer_num_vars.len() == 0 && self.layer_num_vars[0] == 0 {
            let NestedValues::Flat(v) = &self.values.values else { panic!() };
            assert!(v.len() < 2);
            return;
        }
        self.values.assert_normalized(NumVarsWrapper::new(&self.layer_num_vars))
    }
}

impl<F: Field> Index<usize> for NestedPolynomial<F> {
    type Output = F;

    fn index(&self, index: usize) -> &Self::Output {
        self.index(index)
    }
}

impl<F: PrimeField> From<&DensePolynomial<F>> for NestedPolynomial<F> {
    fn from(value: &DensePolynomial<F>) -> Self {
        NestedPolynomial::new(
            NestedPoly::from_values(value.vec().iter().take(1 << value.num_vars).map(|f| *f).collect_vec(), F::from(0u64)),
            vec![value.num_vars],
        )
    }
}

impl<F: PrimeField> From<DensePolynomial<F>> for NestedPolynomial<F> {
    fn from(value: DensePolynomial<F>) -> Self {
        NestedPolynomial::new(
            NestedPoly::from_values(value.vec().iter().take(value.num_vars).map(|f| *f).collect_vec(), F::from(0u64)),
            vec![value.num_vars],
        )
    }
}

impl<F: PrimeField> Into<DensePolynomial<F>> for &NestedPolynomial<F> {
    fn into(self) -> DensePolynomial<F> {
        DensePolynomial::new(self.vec())
    }
}

impl<F: PrimeField> Into<DensePolynomial<F>> for NestedPolynomial<F> {
    fn into(self) -> DensePolynomial<F> {
        DensePolynomial::new(self.vec())
    }
}

/// randoms
struct RandParams<RNG: Rng> {
    gen_fill: Arc<dyn Fn(&mut RNG, usize, usize) -> usize>,
    gen_structure: Arc<dyn Fn(&mut RNG, usize) -> Vec<usize>>,
    phantom_data: PhantomData<Box<RNG>>
}

impl<RNG: Rng> Default for RandParams<RNG> {
    fn default() -> Self {
        Self {
            gen_fill: Arc::new(|rng, layer_size, layer_idx| {
                rng.next_u64() as usize % (layer_size + 1)
            }),
            gen_structure: Arc::new(|rng, num_vars| {
                let mut layer_num_vars = vec![];
                let mut sum = 0;
                while sum < num_vars {
                    layer_num_vars.push(1 + (rng.next_u64() as usize) % (num_vars - sum));
                    sum += layer_num_vars.last().unwrap();
                }
                layer_num_vars = layer_num_vars.iter().filter(|&&s| s != 0).map(|&s| s).collect_vec();
                layer_num_vars
            }),
            phantom_data: PhantomData,
        }
    }
}

impl<RNG: Rng> Clone for RandParams<RNG> {
    fn clone(&self) -> Self {
        let Self { gen_fill, gen_structure, .. } = self;
        Self {
            gen_fill: gen_fill.clone(),
            gen_structure: gen_structure.clone(),
            phantom_data: PhantomData,
        }
    }
}

impl<RNG: Rng> RandParams<RNG> {
    fn replace_gen_fill(mut self, f: Arc<dyn Fn(&mut RNG, usize, usize) -> usize>) -> Self {
        self.gen_fill = f;
        self
    }

    fn replace_gen_structure(mut self, f: Arc<dyn Fn(&mut RNG, usize) -> Vec<usize>>) -> Self {
        self.gen_structure = f;
        self
    }
}

impl<F: Field> NestedPolynomial<F> {
    pub fn rand<RNG: Rng>(rng: &mut RNG, max_vars: usize) -> Self {
        Self::rand_conf(rng, max_vars, RandParams::default())
    }
    pub fn rand_conf<RNG: Rng>(rng: &mut RNG, max_vars: usize, cfg: RandParams<RNG>) -> Self {
        Self::rand_annotated_conf(rng, max_vars, cfg).0
    }

    pub fn rand_annotated<RNG: Rng>(rng: &mut RNG, max_vars: usize) -> (Self, Vec<F>) {
        Self::rand_annotated_conf(rng, max_vars, RandParams::default())
    }
    pub fn rand_annotated_conf<RNG: Rng>(rng: &mut RNG, max_vars: usize, cfg: RandParams<RNG>) -> (Self, Vec<F>) {
        let layer_num_vars = (cfg.gen_structure)(rng, max_vars);
        Self::rand_fixed_structure_conf(rng, &layer_num_vars, cfg)
    }

    pub fn rand_fixed_structure<RNG: Rng>(rng: &mut RNG, layer_num_var: &[usize]) -> (Self, Vec<F>) {
        Self::rand_fixed_structure_conf(rng, layer_num_var, RandParams::default())
    }
    pub fn rand_fixed_structure_conf<RNG: Rng>(rng: &mut RNG, layer_num_var: &[usize], cfg: RandParams<RNG>) -> (Self, Vec<F>) {
        let cont = F::from(rng.next_u64());
        let layer_size = 1 << layer_num_var[0];
        let filled = (cfg.gen_fill)(rng, layer_size, 0);
        if layer_num_var.len() == 1 {
            let segment = (0..filled).map(|_| F::from(rng.next_u64())).collect_vec();
            let full = segment.clone().into_iter().chain(repeat(cont)).take(layer_size as usize).collect_vec();
            return (
                NestedPolynomial::new(
                    NestedPoly::from_values(
                        segment,
                        cont,
                    ),
                    layer_num_var.to_vec(),
                ),
                full,
            )
        }

        let (segments, fulls): (Vec<NestedPoly<F>>, Vec<Vec<F>>) = (0..filled).map(|_| {
            let (seg, f) = Self::rand_fixed_structure_conf(rng, &layer_num_var[1..], cfg.clone());
            (seg.values, f)
        }).unzip();
        let sub_segment_len = 1 << layer_num_var[1..].iter().sum::<usize>();
        let full = fulls.into_iter().flatten().chain(repeat(cont)).take(layer_size as usize * sub_segment_len).collect_vec();

        return (
            NestedPolynomial::new(
                NestedPoly::from_polys(
                    segments,
                    cont,
                ),
                layer_num_var.to_vec(),
            ),
            full,
        )
    }
}

#[cfg(test)]
mod tests {
    use std::iter::{once, repeat_with};
    use std::marker::PhantomData;
    use std::sync::Arc;

    use ark_bls12_381::Fr;
    use ark_std::{rand::RngCore, test_rng, UniformRand};
    use itertools::Itertools;
    use liblasso::poly::dense_mlpoly::DensePolynomial;
    use crate::poly::{segment_evaluate, SplitablePoly, NestedPolynomial, RandParams};

    use super::{evaluate_exact, NestedPoly};

    fn assert_poly_eq(old: &DensePolynomial<Fr>, new: &NestedPolynomial<Fr>) {
        assert_eq!(old.num_vars, new.num_vars());
        let old_vec = old.vec();
        let new_vec = new.vec();
        for idx in 1..1 << old.num_vars {
            assert_eq!(old_vec[idx], new_vec[idx]);
            assert_eq!(old[idx], new[idx]);
        }
    }

    #[test]
    fn ev_exact_parity() {
        let rng = &mut test_rng();
        let nvars = 5;
        let point : Vec<_> = repeat_with(|| Fr::rand(rng)).take(nvars).collect(); 
        let poly : Vec<_> = repeat_with(|| Fr::rand(rng)).take(1 << nvars).collect();
        let lhs = evaluate_exact(&mut poly.clone(), &point);
        let rhs = DensePolynomial::new(poly).evaluate(&point);
        assert_eq!(lhs, rhs);
    }

    #[test]

    fn ev_segment() {
        let rng = &mut test_rng();
        let nvars = 10;
        let segsize = 327;
        let continuation = Fr::rand(rng);
        let point : Vec<_> = repeat_with(|| Fr::rand(rng)).take(nvars).collect(); 
        let mut poly : Vec<_> = repeat_with(|| Fr::rand(rng)).take(segsize).collect();
        let mut naive_poly = poly.clone();
        naive_poly.extend(repeat_with(|| continuation).take((1 << nvars) - segsize));
        let lhs = segment_evaluate(&mut poly, continuation, &point);
        let rhs = DensePolynomial::new(naive_poly).evaluate(&point);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn nested_eval() {
        let mut rng = &mut test_rng();
        let max_vars = 8;

        for _ in 0..10 {
            let (nested, flat) = NestedPolynomial::rand_annotated_conf(
                &mut rng,
                max_vars,
                RandParams::default()
                    .replace_gen_fill(Arc::new(|rng, layer_size, _| {
                        if rng.next_u64() % 2 == 0 {
                            return 0;
                        }
                        return 1 + (rng.next_u64() as usize % layer_size)
                    }))
            );
            let dense = DensePolynomial::new(flat.clone());
            for _ in 0..10 {
                let point: Vec<_> = repeat_with(|| Fr::rand(rng)).take(max_vars).collect();

                let straight_eval = evaluate_exact(&mut flat.clone(), &point);
                let nested_eval = nested.evaluate(&point);
                let dense_eval = dense.evaluate(&point);
                assert_eq!(straight_eval, nested_eval);
                assert_eq!(straight_eval, dense_eval);
            }
        }
    }

    #[test]
    fn nested_normalization() {
        let mut poly_a = NestedPolynomial {
            values: NestedPoly::from_polys(
                vec![
                    NestedPoly::from_polys(
                        vec![
                            NestedPoly::from_polys(
                                vec![
                                    NestedPoly::from_polys(
                                        vec![
                                            NestedPoly::from_polys(
                                                vec![
                                                    NestedPoly::from_values(
                                                        vec![
                                                            Fr::from(1)
                                                        ],
                                                        Fr::from(3),
                                                    ),
                                                    NestedPoly::from_values(
                                                        vec![
                                                            Fr::from(2)
                                                        ],
                                                        Fr::from(3),
                                                    ),
                                                    NestedPoly::from_values(
                                                        vec![],
                                                        Fr::from(3),
                                                    ),
                                                ],
                                                Fr::from(4),
                                            ),
                                        ],
                                        Fr::from(5),
                                    ),
                                ],
                                Fr::from(6),
                            ),
                            NestedPoly::from_polys(
                                vec![
                                    NestedPoly::from_polys(
                                        vec![],
                                        Fr::from(5),
                                    ),
                                ],
                                Fr::from(6),
                            ),
                            NestedPoly::from_polys(
                                vec![],
                                Fr::from(6),
                            ),
                        ],
                        Fr::from(7),
                    )
                ],
                Fr::from(8),
            ),
            layer_num_vars: vec![0, 2, 0, 0, 2, 0]
        };

        let poly_b = NestedPolynomial::new(
            NestedPoly::from_polys(
                vec![
                    NestedPoly::from_values(
                        vec![
                            Fr::from(1),
                            Fr::from(2),
                            Fr::from(3),
                        ],
                        Fr::from(4),
                    ),
                    NestedPoly::from_values(
                        vec![],
                        Fr::from(5),
                    ),
                    NestedPoly::from_values(
                        vec![],
                        Fr::from(6),
                    ),
                ],
                Fr::from(7),
            ),
            vec![2, 2],
        );

        assert_eq!(poly_a.vec(), poly_b.vec());
        poly_a.normalize();
        assert_eq!(poly_a, poly_b);
    }

    #[test]
    fn nested_vec() {
        let mut rng = test_rng();
        let (nested, vec) = NestedPolynomial::rand_annotated(&mut rng, 8);
        assert_eq!(nested.len(), vec.len());
        assert_eq!(nested.vec(), vec);
        assert_poly_eq(&DensePolynomial::new(vec), &nested);
    }


    fn assert_split(nested: &NestedPolynomial<Fr>, dense: &DensePolynomial<Fr>) -> impl Iterator<Item=(NestedPolynomial<Fr>, DensePolynomial<Fr>)> {
        let (dense_l, dense_r) = dense.split_bot();
        let (nested_l, nested_r) = nested.split_bot();

        assert_poly_eq(&dense_l, &nested_l);
        assert_poly_eq(&dense_r, &nested_r);

        nested_l.assert_normalized();
        nested_r.assert_normalized();

        once((nested_l, dense_l)).chain(once((nested_r, dense_r)))
    }

    #[test]
    fn nested_split() {
        let mut rng = test_rng();
        let num_vars = 10;
        let (nested, vec) = NestedPolynomial::rand_annotated(&mut rng, num_vars);
        let dense = DensePolynomial::new(vec);

        let mut it = once((nested, dense)).collect_vec();
        for i in 0..num_vars {
            it = it.iter().map(|(n, d)| assert_split(&n, &d)).flatten().collect_vec();
        }
    }

    #[test]
    fn nested_bound() {
        let mut rng = test_rng();
        let num_vars = 10;
        let (mut nested, vec) = NestedPolynomial::rand_annotated(&mut rng, num_vars);
        let mut dense = DensePolynomial::new(vec);

        assert_poly_eq(&dense, &nested);
        for i in 0..num_vars {
            let r = Fr::from(rng.next_u64());
            nested.bound_var_bot(&r);
            dense.bound_poly_var_bot(&r);
            assert_poly_eq(&dense, &nested);
            nested.assert_normalized();
        }
    }

    #[test]
    fn nested_to_dense_convert() {
        let mut rng = test_rng();
        let num_vars = 10;
        let (nested, vec) = NestedPolynomial::<Fr>::rand_annotated(&mut rng, num_vars);
        let dense: DensePolynomial<Fr> = (&nested).into();
        let expected_dense = DensePolynomial::new(vec);
        assert_eq!(dense.vec(), expected_dense.vec());
        assert_eq!(nested.vec(), NestedPolynomial::from(&dense).vec())
    }
}