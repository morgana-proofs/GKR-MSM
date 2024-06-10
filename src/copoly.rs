// This module describes "copolynomials" - these are globally defined entities which admit
// sums over admissible subset, and evaluation over admissible subset. Example is eq(r, x).
// Every sumcheck will have degree 1 in copolynomials.

use std::{cmp::min};

use ark_ff::{Field, PrimeField};
use rayon::prelude::*;

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


pub trait Copolynomial<F: Field> {
    fn num_vars(&self) -> usize;
    
    /// Computes the sum over a standard subset.
    fn sum_standard_subset(&self, standard_subset: StandardSubset) -> F;
    
    /// Computes the inner product with the vector of values on a standard subset.
    fn ip_standard_subset(&self, standard_subset: StandardSubset, values: &[F]) -> F;
    
    /// Computes the values on a standard subset.
    fn materialize_standard_subset(&self, standard_subset: StandardSubset, target: &mut[F]);

    /// Evaluates a copolynomial in a point.
    fn ev(&self, pt: &[F]) -> F;

    fn sum_segment(&self, start: usize, end: usize) -> F {
        let stsubs = compute_segment_split(start, end);
        stsubs.into_iter().map(|stsub| self.sum_standard_subset(stsub)).fold(F::zero(), |x, y| x + y)
    }

    fn ip_segment(&self, start: usize, end: usize, mut values: &[F]) -> F {
        assert!(values.len() == end - start);
        let mut chunk;
        let stsubs = compute_segment_split(start, end);
        let mut ret = F::zero();
        for stsub in stsubs {
            (chunk, values) = values.split_at(1 << stsub.loglength());
            ret += self.ip_standard_subset(stsub, chunk);
        };
        ret
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

pub struct EqPoly<F: Field> {
    point: Vec<F>,
}

impl<F: Field> EqPoly<F> {
    pub fn new(point: Vec<F>) -> Self {
        EqPoly { point }
    }
}

impl<F: Field> Copolynomial<F> for EqPoly<F> {
    fn num_vars(&self) -> usize {
        self.point.len()
    }

    fn sum_standard_subset(&self, standard_subset: StandardSubset) -> F {
        let loglength = standard_subset.loglength() as usize;
        let mut prefix = standard_subset.start >> loglength;
        let mut ret = F::one();
        let n = self.num_vars();
        for i in loglength .. n {
            let prefix_bit = prefix % 2;
            ret *= if prefix_bit == 1 {self.point[n - i - 1]} else {F::one() - self.point[n - i - 1]};
            prefix >>= 1;
        }
        ret
    }

    // Non-destroying version.
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
        let mut multiplier = F::one();
        for i in loglength .. n {
            let prefix_bit = prefix % 2;
            multiplier *= if prefix_bit == 1 {point[n - i - 1]} else {F::one() - point[n - i - 1]};
            prefix >>= 1;
        }
        target[0] = multiplier;
        
        let point = &point[n - loglength ..];
        let mut curr_size = 1;

        for i in 0 .. loglength {
            let (left, right) = target[0 .. 2 * curr_size].split_at_mut(curr_size);
            left.par_iter_mut().zip(right.par_iter_mut())
                .map(|(a, b)| { *b = point[loglength - i - 1] * *a; *a *= (F::one() - point[loglength - i - 1]) })
                .count();
            curr_size <<= 1;
        }
    
    }

    fn ev(&self, pt: &[F]) -> F {
        let r = &self.point;
        assert!(r.len() == pt.len());
        r.iter().zip(pt.iter()).fold(F::zero(), |acc, (x, y)| acc + *x * y + (F::one() - x)*(F::one() - y))
    }
}



#[cfg(test)]

mod tests {
    use std::iter::repeat_with;

    use ark_bls12_381::Fr;
    use ark_std::test_rng;
    use ark_std::UniformRand;
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
    fn test_eqpoly_sum() {
        let rng = &mut test_rng();
        let point : Vec<Fr> = repeat_with(|| Fr::rand(rng)).take(6).collect();
        let eqvals_naive = eq_poly::EqPolynomial::new(point.clone()).evals();
        for start in 0..64 {
            for end in start..65 {
                let eqpoly = EqPoly::new(point.clone());
                let lhs = eqpoly.sum_segment(start, end);
                let rhs = eqvals_naive[start..end].iter().fold(Fr::ZERO, |x, y| x + y);
                assert!(lhs == rhs);
            }
        }
    }

    #[test]
    fn test_materialize() {
        let rng = &mut test_rng();
        let point : Vec<Fr> = repeat_with(|| Fr::rand(rng)).take(6).collect();
        let eqpoly = EqPoly::new(point.clone());
        let eqvals_naive = eq_poly::EqPolynomial::new(point.clone()).evals();
        for start in 0 .. 64 {
            for end in start .. 65 {
                let mut target = vec![Fr::ZERO; end - start];
                eqpoly.materialize_segment(start, end, &mut target);
                target.iter_mut().zip(eqvals_naive[start .. end].iter()).map(|(t, x)| *t -= x).count();
                for t in target {
                    assert!(t == Fr::ZERO);
                }
            }
        }
    }

    #[test]
    fn test_ip() {
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
}