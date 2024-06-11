// This module describes "copolynomials" - these are globally defined entities which admit
// sums over admissible subset, and evaluation over admissible subset. Example is eq(r, x).
// Every sumcheck will have degree 1 in copolynomials.

use std::{cmp::min, collections::VecDeque};

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
    
    /// Computes the sums over even and odd parts of the standard subset.
    /// Assumes that the standard subset has even length (i.e. loglength > 0).
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

    /// Computes half sums over the segment. Assumes that the start and end of the segment are even.
    fn half_sums_segment(&self, start: usize, end: usize) -> (F, F) {
        assert!(start % 2 == 0);
        assert!(end % 2 == 0);
        let stsubs = compute_segment_split(start, end);
        stsubs.into_iter().map(|stsub| self.half_sums_standard_subset(stsub))
            .fold((F::zero(), F::zero()), |(x0, x1), (y0, y1)| (x0 + y0, x1 + y1))
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
    multiplier: F,
    point: Vec<F>, // Keeps coordinates in reverse order, so we can pop them normally.
}

impl<F: Field> EqPoly<F> {
    pub fn new(mut point: Vec<F>) -> Self {
        point.reverse();
        EqPoly { multiplier: F::one(), point }
    }
}

impl<F: Field> Copolynomial<F> for EqPoly<F> {
    fn num_vars(&self) -> usize {
        self.point.len()
    }

    fn half_sums_standard_subset(&self, standard_subset: StandardSubset) -> (F, F) {
        let loglength = standard_subset.loglength() as usize;
        assert!(loglength > 0);
        let mut prefix = standard_subset.start >> loglength;
        let mut sum = self.multiplier;
        let n = self.num_vars();
        for i in loglength .. n {
            let prefix_bit = prefix % 2;
            sum *= if prefix_bit == 1 {self.point[i]} else {F::one() - self.point[i]};
            prefix >>= 1;
        }
        let dif = sum * self.point[0];
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
        let mut multiplier = self.multiplier;

        for i in loglength .. n {
            let prefix_bit = prefix % 2;
            multiplier *= if prefix_bit == 1 {point[i]} else {F::one() - point[i]};
            prefix >>= 1;
        }

        target[0] = multiplier;
        let point = &point[.. loglength];
        let mut curr_size = 1;

        for i in 0 .. loglength {
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
        let multiplier = Fr::rand(rng);
        let eqvals_naive = eq_poly::EqPolynomial::new(point.clone()).evals();
        let mut eqpoly = EqPoly::new(point.clone());
        eqpoly.multiplier = multiplier;
        for start in (0..64).step_by(2) {
            for end in (start..65).step_by(2) {
                let lhs = eqpoly.half_sums_segment(start, end);
                let mut rhs = (start..end).step_by(2)
                        .fold(
                            (Fr::ZERO, Fr::ZERO),
                            |acc, i| (acc.0 + eqvals_naive[i], acc.1 + eqvals_naive[i+1])
                        );
                rhs.0 *= multiplier;
                rhs.1 *= multiplier;
                assert_eq!(lhs, rhs);
            }
        }
    }

    #[test]
    fn test_materialize() {
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

    #[test]
    fn test_bound() {
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
}