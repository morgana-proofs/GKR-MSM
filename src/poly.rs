use std::cmp::max;
use std::collections::VecDeque;
use std::iter::repeat;
use std::ops::Index;
use ark_ff::{Field, PrimeField};
use ark_std::iterable::Iterable;
use itertools::Itertools;
use liblasso::poly::dense_mlpoly::DensePolynomial;
use liblasso::utils::math::Math;
use rayon::prelude::*;

pub trait GKRablePoly<F>: SplitablePoly<F> + SumcheckablePoly<F> {}

pub trait SplitablePoly<F>: Sized + Poly<F> {
    fn split(&self) -> (Self, Self) {
        #[cfg(feature = "split_bot_to_top")]
            let o = self.split_top();
        #[cfg(not(feature = "split_bot_to_top"))]
            let o= self.split_bot();
        o
    }
    fn split_bot(&self) -> (Self, Self);
    fn split_top(&self) -> (Self, Self);
}

pub trait SumcheckablePoly<F>: Index<usize> + Sized + Poly<F> {
    fn bound_poly_var(&mut self, r: &F) {
        #[cfg(feature = "sumcheck_bot_to_top")]
        self.bound_poly_var_bot(r);
        #[cfg(not(feature = "sumcheck_bot_to_top"))]
        self.bound_poly_var_top(r);
    }

    fn bound_poly_var_top(&mut self, r: &F);
    fn bound_poly_var_bot(&mut self, r: &F);
}

pub trait Poly<F> {
    fn num_vars(&self) -> usize;
}

impl<F: PrimeField> SumcheckablePoly<F> for DensePolynomial<F> {
    fn bound_poly_var_top(&mut self, r: &F) {
        self.bound_poly_var_top(r)
    }

    fn bound_poly_var_bot(&mut self, r: &F) {
        self.bound_poly_var_bot(r)
    }}

impl<F: PrimeField> SplitablePoly<F> for DensePolynomial<F> {
    fn split_bot(&self) -> (Self, Self) {
        (
            DensePolynomial::new(self.vec().iter().step_by(2).map(|x| *x).collect_vec()),
            DensePolynomial::new(self.vec().iter().skip(1).step_by(2).map(|x| *x).collect_vec())
        )
    }
    fn split_top(&self) -> (Self, Self) {
        self.split(self.len() / 2)
    }
}

impl<F: PrimeField> Poly<F> for DensePolynomial<F> {
    fn num_vars(&self) -> usize {
        self.num_vars
    }
}

impl<F: PrimeField> GKRablePoly<F> for DensePolynomial<F> {}


#[derive(Clone)]
pub struct FixedOffsetSegment<F: PrimeField> {
    start_idx: usize,
    evs: Vec<F>,
}

impl<F: PrimeField> FixedOffsetSegment<F> {
    pub fn new(start_idx: usize, evs: Vec<F>) -> Self {
        Self {
            start_idx,
            evs,
        }
    }
}

pub struct FOSegmentedPolynomial<F: PrimeField> {
    num_bucket_coords: usize,
    num_outer_coords: usize,
    segments: Vec<FixedOffsetSegment<F>>,
    constant: F,
}

impl<F: PrimeField> FOSegmentedPolynomial<F> {
    pub fn new(
        num_bucket_coords: usize,
        num_outer_coords: usize,
        segments: Vec<FixedOffsetSegment<F>>,
        constant: F,
    ) -> Self {
        let mut last_idx = 0;
        for (cur_idx, segment) in segments.iter().enumerate() {
            assert!(
                (last_idx == 0 && segment.start_idx == 0) || segment.start_idx > last_idx,
                "SegmentedPoly construction error: segment on index {} has starting pos less or equal to previous: {} <= {}",
                cur_idx, segment.start_idx, last_idx,
            );
            assert!(segment.evs.len() < (1 << num_bucket_coords))
        }

        assert!(last_idx < (1 << num_outer_coords), "SegmentedPoly construction error: provided num_outer_coords is too small");

        Self {
            num_bucket_coords,
            num_outer_coords,
            segments,
            constant,
        }
    }

    pub fn num_vars(&self) -> usize {
        self.num_bucket_coords + self.num_outer_coords
    }

    pub fn vec(&self) -> Vec<F> {
        let mut ret = Vec::with_capacity(1 << self.num_vars());
        let mut current_idx = 0;
        for segment in self.segments.iter() {
            ret.extend(repeat(self.constant).take((1 << self.num_bucket_coords) * segment.start_idx - ret.len()));
            for val in segment.evs.iter() {
                ret.push(val.clone());
            }
            current_idx = segment.start_idx + 1;
        }
        ret.extend(repeat(self.constant).take((1 << self.num_vars()) - ret.len()));
        ret
    }
}

impl<F: PrimeField> Into<DensePolynomial<F>> for FOSegmentedPolynomial<F> {
    fn into(self) -> DensePolynomial<F> {
        DensePolynomial::new(self.vec())
    }
}

impl<F: PrimeField> Index<usize> for FOSegmentedPolynomial<F> {
    type Output = F;

    fn index(&self, index: usize) -> &Self::Output {
        let real = index % (1 << self.num_bucket_coords);
        let fake = index / (1 << self.num_bucket_coords);
        match self.segments.binary_search_by_key(&fake, |s| s.start_idx) {
            Ok(idx) => &self.segments[idx].evs.get(real).unwrap_or(&self.constant),
            Err(_) => &self.constant,
        }
    }
}

impl<F: PrimeField> SplitablePoly<F> for FOSegmentedPolynomial<F> {
    fn split_bot(&self) -> (Self, Self) {
        let mut segments_l = Vec::with_capacity(self.segments.len());
        let mut segments_r = Vec::with_capacity(self.segments.len());
        for segment in self.segments.iter() {
            segments_l.push(FixedOffsetSegment {
                start_idx: segment.start_idx,
                evs: segment.evs.iter().step_by(2).map(|x| *x).collect_vec(),
            });
            segments_r.push(FixedOffsetSegment {
                start_idx: segment.start_idx,
                evs: segment.evs.iter().skip(1).step_by(2).map(|x| *x).collect_vec(),
            });
        }

        (
            Self {
                num_bucket_coords: self.num_bucket_coords - 1,
                num_outer_coords: self.num_outer_coords,
                segments: segments_l,
                constant: self.constant,
            },
            Self {
                num_bucket_coords: self.num_bucket_coords - 1,
                num_outer_coords: self.num_outer_coords,
                segments: segments_r,
                constant: self.constant,
            }
        )
    }
    fn split_top(&self) -> (Self, Self) {
        let split_size = 1 << (self.num_outer_coords - 1);
        let split_idx = self.segments.binary_search_by_key(&(split_size), |s| s.start_idx).map_or_else(|idx| idx, |idx| idx);
        let mut segments_l = self.segments.clone();
        let mut segments_r = segments_l.split_off(split_idx);
        for s in segments_r.iter_mut() {
            s.start_idx -= split_size;
        }

        (
            Self {
                num_bucket_coords: self.num_bucket_coords,
                num_outer_coords: self.num_outer_coords - 1,
                segments: segments_l,
                constant: self.constant,
            },
            Self {
                num_bucket_coords: self.num_bucket_coords,
                num_outer_coords: self.num_outer_coords - 1,
                segments: segments_r,
                constant: self.constant,
            }
        )
    }
}

impl<F: PrimeField> Poly<F> for FOSegmentedPolynomial<F> {
    fn num_vars(&self) -> usize {
        self.num_vars()
    }
}

impl<F: PrimeField> SumcheckablePoly<F> for FOSegmentedPolynomial<F> {
    fn bound_poly_var_top(&mut self, r: &F) {
        unreachable!()
    }

    fn bound_poly_var_bot(&mut self, r: &F) {
        for segment in self.segments.iter_mut() {
            for i in 0..segment.evs.len() / 2 {
                segment.evs[i] = segment.evs[2 * i] + *r * (segment.evs[2 * i + 1] - segment.evs[2 * i]);
            }
            let len = segment.evs.len();
            if segment.evs.len() % 2 == 1 {
                segment.evs[len / 2] = segment.evs[len - 1] + *r * (self.constant - segment.evs[len - 1]);
            }
            segment.evs.truncate((len + 1) / 2);
        }
        self.constant = self.constant + *r * self.constant;
        self.num_bucket_coords -= 1;
    }
}


// --- evaluation impl, to eventually integrate into this ^
// this API is not safe, as it changes polynomial to something different.
// I am not sure how to achieve this effect with safe API, probably boxed slices or smth?

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

pub enum NestedValues<F: Field> {
    Flat(Vec<F>),
    Nested(Vec<NestedPoly<F>>),
}

pub struct NestedPoly<F: Field> {
    values: NestedValues<F>,
    num_ext_vars: usize,
    continuation: F,
}

impl<F: Field> NestedPoly<F> {
    pub fn from_values(values: Vec<F>, num_ext_vars: usize, continuation: F) -> Self {
        assert!(values.len() <= 1 << num_ext_vars);
        Self {values: NestedValues::Flat(values), num_ext_vars, continuation}
    }

    pub fn from_polys(polys: Vec<NestedPoly<F>>, num_ext_vars: usize, continuation: F) -> Self {
        assert!(polys.len() <= 1 << num_ext_vars);
        
        if polys.len() > 0 {
            let num_int_vars = polys[0].num_ext_vars;
            polys
                .iter()
                .map(|p|{assert!(p.num_ext_vars == num_int_vars)}).count();
        }
        Self {values: NestedValues::Nested(polys), num_ext_vars, continuation}
    }

    pub fn evaluate(self, point : &[F]) -> F {
        assert!(point.len() >= self.num_ext_vars);
        let (point_ext, point_in) = point.split_at(self.num_ext_vars);
        let mut segment = match self.values {
            NestedValues::Flat(values) => values,
            NestedValues::Nested(polys) => polys.into_par_iter().map(|poly|poly.evaluate(point_in)).collect(), 
        };
        segment_evaluate(&mut segment, self.continuation, point_ext)
    }
}







#[cfg(test)]
mod tests {
    use std::iter::repeat_with;

    use ark_bls12_381::Fr;
    use ark_ff::Zero;
    use ark_std::{log2, rand::RngCore, test_rng, UniformRand};
    use liblasso::poly::dense_mlpoly::DensePolynomial;
    use crate::poly::{segment_evaluate, FOSegmentedPolynomial, FixedOffsetSegment, SplitablePoly, SumcheckablePoly};

    use super::{evaluate_exact, NestedPoly};

    fn assert_poly_eq(old: &DensePolynomial<Fr>, new: &FOSegmentedPolynomial<Fr>) {
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
        assert!(lhs == rhs);
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
        assert!(lhs == rhs);        
    }


    #[test]
    fn ev_nested() {
        let rng = &mut test_rng();
        
        let mut v1 = vec![];
        let mut poly1_naive = vec![];
        let continuation1 = Fr::rand(rng);

        for i in 0..16 {
            let j_size = if i == 13 {0} else {(rng.next_u64() % 16) as usize};

            let mut v2 = vec![];
            let mut poly2_naive = vec![];
            let continuation2 = Fr::rand(rng);
            for j in 0..j_size {
                let k_size = if j == 13 {0} else {(rng.next_u64() % 16) as usize};
                
                let mut v3 = vec![];
                for _k in 0..k_size {
                    v3.push(Fr::rand(rng));
                }
                let continuation3 = Fr::rand(rng);
                let mut poly3_naive = v3.clone();
                poly3_naive.extend(repeat_with(|| continuation3).take(16 - k_size));
                let poly3 = NestedPoly::from_values(v3, 4, continuation3);

                v2.push(poly3);
                poly2_naive.push(poly3_naive);
            }

            let cont2_vec = vec![continuation2; 16];
            poly2_naive.extend(repeat_with(||{cont2_vec.clone()}).take(16 - j_size));
            let poly2 = NestedPoly::from_polys(v2, 4, continuation2);

            v1.push(poly2);
            poly1_naive.push(poly2_naive);
        }

        let poly1 = NestedPoly::from_polys(v1, 4, continuation1);

        let point : Vec<_> = repeat_with(|| Fr::rand(rng)).take(4 * 3).collect();

        let lhs = poly1.evaluate(&point);

        let poly1_naive : Vec<_> = poly1_naive.into_iter().flatten().collect();
        let mut poly1_naive : Vec<Fr> = poly1_naive.into_iter().flatten().collect();

        let rhs = evaluate_exact(&mut poly1_naive, &point);

        assert!(lhs == rhs);

    }

    #[test]
    fn fixed_offset_segmented() {
        let mut rng = test_rng();
        let expected_vec = vec![
            Fr::from(rng.next_u64()),
            Fr::from(rng.next_u64()),
            Fr::from(rng.next_u64()),
            Fr::from(rng.next_u64()),
            Fr::from(rng.next_u64()),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::from(rng.next_u64()),
            Fr::from(rng.next_u64()),
            Fr::from(rng.next_u64()),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::from(rng.next_u64()),
            Fr::from(rng.next_u64()),
            Fr::from(rng.next_u64()),
            Fr::from(rng.next_u64()),
            Fr::from(rng.next_u64()),
            Fr::from(rng.next_u64()),
            Fr::from(rng.next_u64()),
            Fr::zero(),
        ];
        let mut expected_poly = DensePolynomial::new(expected_vec.clone());
        let segments = vec![
            FixedOffsetSegment {
                start_idx: 0,
                evs: vec![
                    expected_vec[0],
                    expected_vec[1],
                    expected_vec[2],
                    expected_vec[3],
                    expected_vec[4],
                ],
            },
            FixedOffsetSegment {
                start_idx: 2,
                evs: vec![
                    expected_vec[16],
                    expected_vec[17],
                    expected_vec[18],
                ],
            },
            FixedOffsetSegment {
                start_idx: 3,
                evs: vec![
                    expected_vec[24],
                    expected_vec[25],
                    expected_vec[26],
                    expected_vec[27],
                    expected_vec[28],
                    expected_vec[29],
                    expected_vec[30],
                ],
            },
        ];
        let mut poly = FOSegmentedPolynomial {
            num_bucket_coords: 3,
            num_outer_coords: 2,
            segments: segments.clone(),
            constant: Fr::zero(),
        };
        assert_eq!(expected_vec, poly.vec());

        assert_poly_eq(&expected_poly, &poly);

        let r = Fr::from(rng.next_u64());
        poly.bound_poly_var_bot(&r);
        expected_poly.bound_poly_var_bot(&r);

        assert_poly_eq(&expected_poly, &poly);

        let r = Fr::from(rng.next_u64());
        poly.bound_poly_var_bot(&r);
        expected_poly.bound_poly_var_bot(&r);

        assert_poly_eq(&expected_poly, &poly);

        poly = FOSegmentedPolynomial::new(
            3,
            2,
            segments.clone(),
            Fr::zero(),
        );
        expected_poly = DensePolynomial::new(expected_vec.clone());

        let (l, r) = poly.split_top();
        let (expected_l, expected_r) = expected_poly.split_top();

        assert_poly_eq(&expected_l, &l);
        assert_poly_eq(&expected_r, &r);

        let (l, r) = poly.split_bot();
        let (expected_l, expected_r) = expected_poly.split_bot();

        assert_poly_eq(&expected_l, &l);
        assert_poly_eq(&expected_r, &r);
    }
}