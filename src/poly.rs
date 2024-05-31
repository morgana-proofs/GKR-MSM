use std::cmp::max;
use std::iter::repeat;
use std::ops::Index;
use ark_ff::PrimeField;
use ark_std::iterable::Iterable;
use itertools::Itertools;
use liblasso::poly::dense_mlpoly::DensePolynomial;
use liblasso::utils::math::Math;

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

pub struct FixedOffsetSegmentedPolynomial<F: PrimeField> {
    num_real_vars: usize,
    num_fake_vars: usize,
    segments: Vec<FixedOffsetSegment<F>>,
    constant: F,
}

impl<F: PrimeField> FixedOffsetSegmentedPolynomial<F> {
    pub fn new(num_vars: usize, segments: Vec<FixedOffsetSegment<F>>, constant: F) -> Self {
        let mut max_vars = 0;
        let mut last_idx = 0;
        for (cur_idx, segment) in segments.iter().enumerate() {
            assert!(
                (last_idx == 0 && segment.start_idx == 0) || segment.start_idx > last_idx,
                "SegmentedPoly construction error: segment on index {} has starting pos less or equal to previous: {} <= {}",
                cur_idx, segment.start_idx, last_idx,
            );
            max_vars = max(max_vars, segment.evs.len().log_2());
        }

        assert!(last_idx < (1 << (num_vars - max_vars)), "SegmentedPoly construction error: provided num_vars is too small");

        Self {
            num_real_vars: max_vars,
            num_fake_vars: num_vars - max_vars,
            segments,
            constant,
        }
    }

    pub fn num_vars(&self) -> usize {
        self.num_real_vars + self.num_fake_vars
    }

    pub fn vec(&self) -> Vec<F> {
        let mut ret = Vec::with_capacity(1 << self.num_vars());
        let mut current_idx = 0;
        for segment in self.segments.iter() {
            ret.extend(repeat(self.constant).take((1 << self.num_real_vars) * segment.start_idx - ret.len()));
            for val in segment.evs.iter() {
                ret.push(val.clone());
            }
            current_idx = segment.start_idx + 1;
        }
        ret.extend(repeat(self.constant).take((1 << self.num_vars()) - ret.len()));
        ret
    }
}

impl<F: PrimeField> Into<DensePolynomial<F>> for FixedOffsetSegmentedPolynomial<F> {
    fn into(self) -> DensePolynomial<F> {
        DensePolynomial::new(self.vec())
    }
}

impl<F: PrimeField> Index<usize> for FixedOffsetSegmentedPolynomial<F> {
    type Output = F;

    fn index(&self, index: usize) -> &Self::Output {
        let real = index % (1 << self.num_real_vars);
        let fake = index / (1 << self.num_real_vars);
        match self.segments.binary_search_by_key(&fake, |s| s.start_idx) {
            Ok(idx) => &self.segments[idx].evs.get(real).unwrap_or(&self.constant),
            Err(_) => &self.constant,
        }
    }
}

impl<F: PrimeField> SplitablePoly<F> for FixedOffsetSegmentedPolynomial<F> {
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
                num_real_vars: self.num_real_vars - 1,
                num_fake_vars: self.num_fake_vars,
                segments: segments_l,
                constant: self.constant,
            },
            Self {
                num_real_vars: self.num_real_vars - 1,
                num_fake_vars: self.num_fake_vars,
                segments: segments_r,
                constant: self.constant,
            }
        )
    }
    fn split_top(&self) -> (Self, Self) {
        let split_size = 1 << (self.num_fake_vars - 1);
        let split_idx = self.segments.binary_search_by_key(&(split_size), |s| s.start_idx).map_or_else(|idx| idx, |idx| idx);
        let mut segments_l = self.segments.clone();
        let mut segments_r = segments_l.split_off(split_idx);
        for s in segments_r.iter_mut() {
            s.start_idx -= split_size;
        }

        (
            Self {
                num_real_vars: self.num_real_vars,
                num_fake_vars: self.num_fake_vars - 1,
                segments: segments_l,
                constant: self.constant,
            },
            Self {
                num_real_vars: self.num_real_vars,
                num_fake_vars: self.num_fake_vars - 1,
                segments: segments_r,
                constant: self.constant,
            }
        )
    }
}

impl<F: PrimeField> Poly<F> for FixedOffsetSegmentedPolynomial<F> {
    fn num_vars(&self) -> usize {
        self.num_vars()
    }
}

impl<F: PrimeField> SumcheckablePoly<F> for FixedOffsetSegmentedPolynomial<F> {
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
        self.num_real_vars -= 1;
    }
}


#[cfg(test)]
mod tests {
    use ark_bls12_381::Fr;
    use ark_ff::Zero;
    use ark_std::{test_rng, UniformRand, rand::RngCore};
    use liblasso::poly::dense_mlpoly::DensePolynomial;
    use crate::poly::{FixedOffsetSegment, FixedOffsetSegmentedPolynomial, SplitablePoly, SumcheckablePoly};

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
        let mut poly = FixedOffsetSegmentedPolynomial {
            num_real_vars: 3,
            num_fake_vars: 2,
            segments: segments.clone(),
            constant: Fr::zero(),
        };
        assert_eq!(expected_vec, poly.vec());

        for (idx, val) in expected_vec.iter().enumerate() {
            assert_eq!(&poly[idx], val);
            assert_eq!(&expected_poly[idx], val);
        }

        let r = Fr::from(rng.next_u64());
        poly.bound_poly_var_bot(&r);
        expected_poly.bound_poly_var_bot(&r);

        assert_eq!(poly.num_vars(), expected_poly.num_vars);
        for (idx, val) in expected_poly.vec().iter().take(1 << expected_poly.num_vars).enumerate() {
            let x = poly[idx];
            assert_eq!(x, *val);
        }

        let r = Fr::from(rng.next_u64());
        poly.bound_poly_var_bot(&r);
        expected_poly.bound_poly_var_bot(&r);

        assert_eq!(poly.num_vars(), expected_poly.num_vars);
        for (idx, val) in expected_poly.vec().iter().take(1 << expected_poly.num_vars).enumerate() {
            let x = poly[idx];
            assert_eq!(x, *val);
        }

        poly = FixedOffsetSegmentedPolynomial {
            num_real_vars: 3,
            num_fake_vars: 2,
            segments: segments.clone(),
            constant: Fr::zero(),
        };
        expected_poly = DensePolynomial::new(expected_vec.clone());

        let (l, r) = poly.split_top();
        let (expected_l, expected_r) = expected_poly.split_top();
        assert_eq!(l.num_vars(), expected_l.num_vars);
        for (idx, val) in expected_l.vec().iter().take(1 << expected_l.num_vars).enumerate() {
            let x = l[idx];
            assert_eq!(x, *val);
        }
        assert_eq!(r.num_vars(), expected_r.num_vars);
        for (idx, val) in expected_r.vec().iter().take(1 << expected_r.num_vars).enumerate() {
            let x = r[idx];
            assert_eq!(x, *val);
        }

        let (l, r) = poly.split_bot();
        let (expected_l, expected_r) = expected_poly.split_bot();
        assert_eq!(l.num_vars(), expected_l.num_vars);
        for (idx, val) in expected_l.vec().iter().take(1 << expected_l.num_vars).enumerate() {
            let x = l[idx];
            assert_eq!(x, *val);
        }
        assert_eq!(r.num_vars(), expected_r.num_vars);
        for (idx, val) in expected_r.vec().iter().take(1 << expected_r.num_vars).enumerate() {
            let x = r[idx];
            assert_eq!(x, *val);
        }
    }
}