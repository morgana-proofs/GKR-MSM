// This module describes "copolynomials" - these are globally defined entities which admit
// sums over admissible subset, and evaluation over admissible subset. Example is eq(r, x).
// Every sumcheck will have degree 1 in copolynomials.

use std::{cmp::min, collections::VecDeque};

use ark_ff::{Field, PrimeField};
use rayon::prelude::*;

use crate::poly::Fragment;

#[derive(Clone, Copy)]
/// A segment starting at start and ending at start + 2^loglength, such that 2^loglength | start.
pub struct StandardSubset {
    start: usize,
    loglength: u8,
}

impl StandardSubset {
    pub fn new(start: usize, loglength: u8) -> Self {
        assert!((start >> loglength) << loglength == start, "Start must be divisible by length.");
        Self{ start, loglength }
    }

    pub fn start(&self) -> usize {
        self.start
    }

    pub fn end(&self) -> usize {
        self.start + (1 << self.loglength)
    }

    pub fn loglength(&self) -> u8 {
        self.loglength
    }
}

pub fn count_trailing_zeros(mut x: usize) -> u8 {
    if x == 0 {return 64};
    let mut ret = 0;
    let mut x_shift = x >> 1;
    while x_shift << 1 == x {
        ret += 1;
        x = x_shift;
        x_shift = x >> 1;
    }
    ret
}

pub fn log_floor(mut x: usize) -> u8 {
    let mut ret = 0;
    while x > 1 {
        x >>= 1;
        ret += 1;
    }
    ret
}

pub struct FragmentQuery {
    fragments: Vec<Fragment>,
}


pub struct StSubIter {
    start: usize,
    end: usize,
}

impl StSubIter {
    pub fn new(start: usize, end: usize) -> Self {
        assert!(start <= end);
        StSubIter { start, end }
    }
}

impl Iterator for StSubIter {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        if self.end == self.start {return None}
        let loglength = min(count_trailing_zeros(self.start), log_floor(self.end - self.start));
        self.start += 1 << loglength;
        Some(loglength)
    }
}

/// Divides a contigious segment into the standard subsets.
pub fn compute_segment_split(mut start: usize, end: usize) -> Vec<StandardSubset> {
    let mut ret = vec![];
    while start < end {
        let loglength = min(count_trailing_zeros(start), log_floor(end - start));
        ret.push(StandardSubset::new(start, loglength));
        start += 1 << loglength;
    }
    ret
}

/// Bintree node. Internal node describes positions of of left and right children,
/// leaf describes the address of the leaf content.
#[derive(Clone, Copy, Debug)]
pub enum BinTreeNode {
    Internal(usize, usize),
    Leaf(usize),
}

#[derive(Clone, Debug)]
pub struct BinTree {
    nodes: Vec<BinTreeNode>,
}


/// Assumes that logsizes satisfy our standard subset condition, i.e. size[i] | sum.
pub fn standard_subsets_bintree(logsizes: impl Iterator<Item = u8>) -> BinTree {
    let mut nodes = vec![]; // Keeps the increasing sequence of nodes.
    let mut node_logsizes : Vec<u8> = vec![];
    let mut front : Vec<usize> = vec![];

    let mut to_append;
    for (i, logsize) in logsizes.enumerate() {
        nodes.push(BinTreeNode::Leaf(i));
        node_logsizes.push(logsize);
        to_append = nodes.len() - 1;
        loop {
            if let Some(&last_node_idx) = front.last() {
                let a = node_logsizes[last_node_idx]; 
                let b = node_logsizes[to_append];
                if a > b {
                    front.push(to_append);
                    break;
                } else if a == b {
                    front.pop();
                    nodes.push(BinTreeNode::Internal(last_node_idx, to_append));
                    node_logsizes.push(a + 1);
                    to_append = nodes.len() - 1;
                } else {
                    panic!("Ill-formed sequence of logsizes.");
                }
            } else {
                front.push(to_append);
                break;
            }
        }
    }
    BinTree { nodes }
}

pub struct PrefixFoldIter<T: Iterator, Acc : Clone, F: Fn(&Acc, &T::Item) -> Acc> {
    acc: Acc,
    iter: T,
    f: F,
}

impl<T: Iterator, Acc : Clone, F: Fn(&Acc, &T::Item) -> Acc> Iterator for PrefixFoldIter<T, Acc, F> {
    type Item = (T::Item, Acc);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next_item) = self.iter.next() {
            self.acc = (self.f)(&self.acc, &next_item);
            Some((next_item, self.acc.clone()))
        } else {
            None
        }
    }
}

pub trait PrefixFold : Iterator {
    fn prefix_fold<
        Acc: Clone,
        F: Fn(&Acc, &Self::Item) -> Acc
    >(self, init: Acc, f: F) -> PrefixFoldIter<Self, Acc, F> where Self : Sized {
        PrefixFoldIter { acc: init, iter: self, f }
    }
}

impl<T: Iterator> PrefixFold for T {}


pub fn compute_subsegments(sizes: impl Iterator<Item = usize>) -> impl Iterator<Item = u8> {
    sizes.prefix_fold(0, |a, b| *a + b).map(|(size, sum)| StSubIter::new(sum - size, sum)).flatten()
}


pub trait Copolynomial<F: Field> {
    fn num_vars(&self) -> usize;
    
    /// Computes the sums over even and odd parts of the standard subset.
    fn half_sums_standard_subset(&self, standard_subset: StandardSubset) -> (F, F);

    /// Computes the inner product with the vector of values on a standard subset.
    fn ip_standard_subset(&self, standard_subset: StandardSubset, values: &[F]) -> F;
    
    /// Computes the values on a standard subset.
    fn materialize_standard_subset(&self, standard_subset: StandardSubset, target: &mut[F]);

    /// Evaluates a copolynomial in a point.
    fn ev(&self, pt: &[F]) -> F;

    /// Binds the first variable to a value.
    /// Importantly, this is the reverse order to the poly_var_bound from liblasso.
    fn bound(&mut self, value: F);

    /// Computes half sums over the segment.
    /// Half sums are determined in terms of external indexation, i.e. even and odd parts are determined
    /// as value with even and odd global indices, respectively.
    fn half_sums_segment(&self, start: usize, end: usize) -> (F, F) {
        let stsubs = compute_segment_split(start, end);
        stsubs.into_iter().map(|stsub| self.half_sums_standard_subset(stsub))
            .fold((F::zero(), F::zero()), |(x0, x1), (y0, y1)| (x0 + y0, x1 + y1))
    }

    fn ip_segment(&self, start: usize, end: usize, values: &[F]) -> F {
        let mut target = vec![F::zero(); values.len()];
        self.materialize_segment(start, end, &mut target);
        target.par_iter().zip(values.par_iter()).map(|(a, b)| *a * b).sum()
    }

    fn materialize_segment(&self, start: usize, end: usize, target: &mut[F]) {
        assert!(target.len() == end - start);
        let mut target = target;
        let mut chunk;
        let stsubs = compute_segment_split(start, end);
        for stsub in stsubs {
            (chunk, target) = target.split_at_mut(1 << stsub.loglength());
            self.materialize_standard_subset(stsub, chunk);
        }
    }

}

#[derive(Clone)]
pub struct EqPoly<F: Field> {
    multiplier: F,
    point: Vec<F>, // Keeps coordinates in reverse order, so we can pop them normally.
}

impl<F: Field> EqPoly<F> {
    pub fn new(point: Vec<F>) -> Self {
        EqPoly { multiplier: F::one(), point }
    }
}

impl<F: Field> Copolynomial<F> for EqPoly<F> {
    fn num_vars(&self) -> usize {
        self.point.len()
    }

    fn half_sums_standard_subset(&self, standard_subset: StandardSubset) -> (F, F) {
        let loglength = standard_subset.loglength() as usize;
        let mut prefix = standard_subset.start >> loglength;
        let mut sum = self.multiplier;
        let n = self.num_vars();
        
        assert!(standard_subset.end() <= 1 << n);
        
        for i in (0 .. n - loglength).rev() {
            let prefix_bit = prefix % 2;
            sum *= if prefix_bit == 1 {self.point[i]} else {F::one() - self.point[i]};
            prefix >>= 1;
        }

        if loglength == 0 {
            return if standard_subset.start % 2 == 0 {(sum, F::zero())} else {(F::zero(), sum)}
        }

        let dif = sum * self.point[n-1];
        (sum - dif, dif)
    }

    // Non data destroying version.
    fn ip_standard_subset(&self, standard_subset: StandardSubset, values: &[F]) -> F {
        let target = &mut vec![F::zero(); values.len()];
        self.materialize_standard_subset(standard_subset, target);
        target.par_iter().zip(values.par_iter()).map(|(x, y)| *x * y).sum()
    }

    fn materialize_standard_subset(&self, standard_subset: StandardSubset, target: &mut[F]) {
        let loglength = standard_subset.loglength() as usize;
        let point = &self.point;

        assert!(target.len() == 1 << loglength);
        let mut prefix = standard_subset.start >> loglength;
        let n = self.num_vars();
        assert!(standard_subset.end() <= 1 << n);

        let mut multiplier = self.multiplier;

        for i in (0 .. n - loglength).rev() {
            let prefix_bit = prefix % 2;
            multiplier *= if prefix_bit == 1 {point[i]} else {F::one() - point[i]};
            prefix >>= 1;
        }

        target[0] = multiplier;
        let point = &point[n - loglength ..];
        let mut curr_size = 1;

        for i in (0..loglength).rev() {
            let (left, right) = target[0 .. 2 * curr_size].split_at_mut(curr_size);
            left.par_iter_mut().zip(right.par_iter_mut())
                .map(|(a, b)| { *b = point[i] * *a; *a *= (F::one() - point[i]) })
                .count();
            curr_size <<= 1;
        }
    
    }

    fn ev(&self, pt: &[F]) -> F {
        let r = &self.point;
        assert!(r.len() == pt.len());
        self.multiplier * r.iter().zip(pt.iter()).fold(F::zero(), |acc, (x, y)| acc * (*x * y + (F::one() - x)*(F::one() - y)))
    }
    
    fn bound(&mut self, value: F) {
        let p0 = self.point.pop().unwrap();
        self.multiplier *= p0 * value + (F::one() - p0) * (F::one() - value);
    }
}


// ----------------------------------------------------------------------------------------------------------
// In most cases, using Eq will suffice. However, there are other copolynomials that are sometimes useful
//
// Next, we implement Rot(x, y), which rotates the indices by 1 in cyclical order. This is useful for copy
// constraint argument - and any permutation arguments that do not want to involve GKR tree, for example,
// out of verifier size concerns. Notably, this is different from Hyperplonk permutation argument, which is
// inconvenient for us, as it skips the point with index 0, and all our other protocols work in terms of
// hypercubes, and different from Hyperplonk rotation argument (which also skips 0 and additionally has
// a somewhat weird indexing).
//
// We will also implement polynomials that allow us to move some standard subset into other standard subset, 
// and their sums. This is useful for the cases where we need to move some data to other computation.
//
// In theory this could be combined with even arbitrary rotations, but this quickly becomes messy, so
// we won't do it for now.
//
// ----------------------------------------------------------------------------------------------------------

/// This struct desribes rotation polynomial Rot(x, y), with y substituted to be a point r.
/// Rot(x, y) = (1-x0)y0 * Eq(x[1..], y[1..]) + x0(1-y0) Rot(x[1..], y[1..]).
/// As our structure needs to support variable binding, we actually keep two multipliers - one for Rot and
/// another one for Eq (initialized to 0 on entry).
#[derive(Clone)]
pub struct RotPoly<F: Field> {
    rot_multiplier: F,
    eq_multiplier: F,
    point: Vec<F>,
}

impl<F: Field> RotPoly<F> {
    pub fn new(point: Vec<F>) -> Self {
        RotPoly { rot_multiplier : F::one(), eq_multiplier: F::zero(), point }
    }
}

impl<F: Field> Copolynomial<F> for RotPoly<F> {
    fn num_vars(&self) -> usize {
        self.point.len()
    }

    fn half_sums_standard_subset(&self, standard_subset: StandardSubset) -> (F, F) {
        self.half_sums_segment(standard_subset.start(), standard_subset.end())
    }

    fn ip_standard_subset(&self, standard_subset: StandardSubset, values: &[F]) -> F {
        self.ip_segment(standard_subset.start(), standard_subset.end(), values)
    }

    fn materialize_standard_subset(&self, standard_subset: StandardSubset, target: &mut[F]) {
        self.materialize_segment(standard_subset.start(), standard_subset.end(), target)
    }

    fn half_sums_segment(&self, start: usize, end: usize) -> (F, F) {
        // Edge case: if start = end, always return 0.
        if start == end {
            return (F::zero(), F::zero())
        };

        let l = 1 << self.num_vars();
        let point = &self.point;
        let target_start = start + 1;
        let target_end = min(end + 1, l);
        let poly = EqPoly::new(point.clone());
        let (mut b, mut a) = poly.half_sums_segment(target_start, target_end);
        if end == l {
            b += point.iter().map(|x| F::one() - x).product::<F>();
        }

        a *= self.rot_multiplier;
        b *= self.rot_multiplier;

        if self.eq_multiplier != F::zero() {
            let (a_eq, b_eq) = poly.half_sums_segment(start, end);
            a += a_eq * self.eq_multiplier;
            b += b_eq * self.eq_multiplier; 
        }

        (a, b)
    }

    fn materialize_segment(&self, start: usize, end: usize, target: &mut[F]) {
        let l = target.len();
        assert!(l == end - start);

        let mut eq = EqPoly::new(self.point.clone());
        let mut offset = 0;

        if end == 1 << self.num_vars() {
            target[l-1] = self.rot_multiplier * self.point.iter().map(|x| F::one() - x).product::<F>();
            offset = 1;
        }

        eq.multiplier = self.rot_multiplier;
        eq.materialize_segment(start + 1, end - offset + 1, &mut target[.. l-offset]);
        if self.eq_multiplier != F::zero() {
            let mut eq_target = vec![F::zero(); end - start];
            eq.multiplier = self.eq_multiplier;
            eq.materialize_segment(start, end, &mut eq_target);
            target.par_iter_mut().zip(eq_target.par_iter()).map(|(x, y)| *x += y).count();
        }
        
    }

    fn ev(&self, pt: &[F]) -> F {
        assert!(pt.len() == self.num_vars());
        let mut poly = self.clone();
        for &x in pt.iter().rev() {
            poly.bound(x);
        }
        poly.eq_multiplier + poly.rot_multiplier
    }

    fn bound(&mut self, x0: F) {
        let y0 = self.point.pop().unwrap();
        let y0x0 = y0 * x0;
        self.eq_multiplier *= F::one() - y0 - x0 + y0x0.double(); // Multiply by eq(x0, y0)
        self.eq_multiplier += (y0 - y0x0) * self.rot_multiplier; // Add the component from Rot.
        self.rot_multiplier *= x0 - y0x0;
    }
}


#[cfg(test)]

mod tests {
    use std::iter::repeat_with;
    use std::mem::MaybeUninit;

    use ark_bls12_381::Fr;
    use ark_std::test_rng;
    use ark_std::UniformRand;
    use liblasso::poly::dense_mlpoly::DensePolynomial;
    use liblasso::poly::eq_poly;

    use super::*;

    #[test]
    fn test_segment_split() {
        for start in 0..128 {
            for end in start..129 {
                let standard_subsets = compute_segment_split(start, end);
                let l = standard_subsets.len();
                if l == 0 {
                    assert!(end == start);
                } else {
                    assert!(standard_subsets[0].start() == start);
                    assert!(standard_subsets[l-1].end() == end);
                    for i in 0..(l-1) {
                        assert!(standard_subsets[i].end() == standard_subsets[i+1].start()); 
                    }
                }
            }
        }
    }

    #[test]
    fn test_eq_sum() {
        let rng = &mut test_rng();
        let point : Vec<Fr> = repeat_with(|| Fr::rand(rng)).take(6).collect();
        let multiplier = Fr::rand(rng);
        let eqvals_naive = eq_poly::EqPolynomial::new(point.clone()).evals();
        let mut eqpoly = EqPoly::new(point.clone());
        eqpoly.multiplier = multiplier;
        for start in 0..64 {
            for end in start..65 {
                let lhs = eqpoly.half_sums_segment(start, end);
                let mut rhs = (0..64)
                        .fold(
                            (Fr::ZERO, Fr::ZERO),
                            |acc, i| {
                                if i < start || i >= end {
                                    acc
                                } else if i % 2 == 0 {
                                    (acc.0 + eqvals_naive[i], acc.1)
                                } else {
                                    (acc.0, acc.1 + eqvals_naive[i])
                                }
                            }
                        );
                rhs.0 *= multiplier;
                rhs.1 *= multiplier;
                assert_eq!(lhs, rhs);
            }
        }
    }

    #[test]
    fn test_eq_materialize() {
        let rng = &mut test_rng();
        let point : Vec<Fr> = repeat_with(|| Fr::rand(rng)).take(6).collect();
        let mut eqpoly = EqPoly::new(point.clone());
        let multiplier = Fr::rand(rng);
        eqpoly.multiplier = multiplier;

        let eqvals_naive = eq_poly::EqPolynomial::new(point.clone()).evals();
        for start in 0 .. 64 {
            for end in start .. 65 {
                let mut target = vec![Fr::ZERO; end - start];
                eqpoly.materialize_segment(start, end, &mut target);
                target.iter_mut().zip(eqvals_naive[start .. end].iter()).map(|(t, x)| *t -= *x * multiplier).count();
                for t in target {
                    assert!(t == Fr::ZERO);
                }
            }
        }
    }

    #[test]
    fn test_eq_ip() {
        let rng = &mut test_rng();
        let point : Vec<Fr> = repeat_with(|| Fr::rand(rng)).take(6).collect();
        let eqpoly = EqPoly::new(point.clone());
        let eqvals_naive = eq_poly::EqPolynomial::new(point.clone()).evals();
        let values : Vec<Fr> = repeat_with(|| Fr::rand(rng)).take(64).collect();

        for start in 0 .. 64 {
            for end in start .. 65 {
                let lhs = eqpoly.ip_segment(start, end, &values[start .. end]);
                let rhs = values[start .. end].iter()
                    .zip(eqvals_naive[start .. end].iter()
                ).fold(Fr::ZERO, |acc, (x, y)| acc + *x * y);
                assert_eq!(lhs, rhs);
            }
        }
    }

    #[test]
    fn test_eq_bound() {
        let rng = &mut test_rng();
        let point : Vec<Fr> = repeat_with(|| Fr::rand(rng)).take(6).collect();
        let mut eqpoly = EqPoly::new(point.clone());

        let evaluation_point : Vec<Fr> = repeat_with(|| Fr::rand(rng)).take(6).collect();

        let lhs = eqpoly.ev(&evaluation_point);

        let e0 = evaluation_point[0];
        eqpoly.bound(e0);

        let rhs = eqpoly.ev(&evaluation_point[1 ..]);

        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_rot_ev() {
        let rng = &mut test_rng();
        let x : Vec<Fr> = repeat_with(|| Fr::rand(rng)).take(6).collect();
        let y : Vec<Fr> = repeat_with(|| Fr::rand(rng)).take(6).collect();

        let x_evs = eq_poly::EqPolynomial::new(x.clone()).evals();
        let mut y_evs = eq_poly::EqPolynomial::new(y.clone()).evals();

        let y_ev_0 = y_evs[0];
        let l1 = y_evs.len() - 1;
        for i in 0..l1 {
            y_evs[i] = y_evs[i+1];
        }
        
        y_evs[l1] = y_ev_0; // Rotate evaluations of y left.
        
        let rot = RotPoly::new(y.clone());

        let lhs = rot.ev(&x);
        let rhs = x_evs.iter().zip(y_evs.iter()).fold(Fr::ZERO, |acc, (x, y)| acc + *x * y);

        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_rot_sum() {
        let rng = &mut test_rng();
        let mut y : Vec<Fr> = repeat_with(|| Fr::rand(rng)).take(6).collect();

        let r0  = Fr::rand(rng);
        let r1 = Fr::rand(rng);

        let mut rot = RotPoly::new(y.clone());
        rot.bound(r0);
        rot.bound(r1);

        let mut y_evs = eq_poly::EqPolynomial::new(y.clone()).evals();

        let y_ev_0 = y_evs[0];
        let l1 = y_evs.len() - 1;
        for i in 0..l1 {
            y_evs[i] = y_evs[i+1];
        }
        
        y_evs[l1] = y_ev_0; // Rotate evaluations of y left.
        
        let mut y_evs = DensePolynomial::new(y_evs);
        y_evs.bound_poly_var_bot(&r0);
        y_evs.Z.truncate(32);
        y_evs.bound_poly_var_bot(&r1);
        y_evs.Z.truncate(16);


        for start in 0..16 {
            for end in start..17 {
                let (al, bl) = rot.half_sums_segment(start, end);
                let (mut ar, mut br) = (Fr::ZERO, Fr::ZERO);

                for i in 0..16 {
                    if i >= start && i < end {
                        if i%2 == 0 {
                            ar += y_evs.Z[i];
                        } else {
                            br += y_evs.Z[i];
                        }
                    }
                }

                assert_eq!((al, bl), (ar, br))

            }
        }
    }

    #[test]
    fn test_rot_materialize() {
        let rng = &mut test_rng();
        let y : Vec<Fr> = repeat_with(|| Fr::rand(rng)).take(6).collect();

        let mut x : Vec<Fr> = repeat_with( || Fr::rand(rng)).take(6).collect();

        let mut rot = RotPoly::new(y.clone());
        let mut y_evs = eq_poly::EqPolynomial::new(y.clone()).evals();

        let y_ev_0 = y_evs[0];
        let l1 = y_evs.len() - 1;
        for i in 0..l1 {
            y_evs[i] = y_evs[i+1];
        }
        
        y_evs[l1] = y_ev_0; // Rotate evaluations of y left.

        let mut y_evs = DensePolynomial::new(y_evs);
        
        let r = x.pop().unwrap();
        y_evs.bound_poly_var_bot(&r);
        y_evs.Z.truncate(32);
        rot.bound(r);
        let r = x.pop().unwrap();
        y_evs.bound_poly_var_bot(&r);
        y_evs.Z.truncate(16);
        rot.bound(r);

        for start in 0..16 {
            for end in start..17 {
                let mut target = vec![Fr::ZERO; end - start];
                rot.materialize_segment(start, end, &mut target);
                assert_eq!(target, y_evs.Z[start..end])
            }
        }
    }


    #[test]

    fn test_bintree() {
        let sizes = vec![13, 8, 7, 4];
        let bintree = standard_subsets_bintree(compute_subsegments(sizes.into_iter()));
        println!("{:?}", bintree);
    }

}