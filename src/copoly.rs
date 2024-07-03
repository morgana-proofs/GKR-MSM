// This module describes "copolynomials" - these are globally defined entities which admit
// sums over admissible subset, and evaluation over admissible subset. Example is eq(r, x).
// Every sumcheck will have degree 1 in copolynomials.

use std::{cmp::min, collections::VecDeque, mem::{transmute, MaybeUninit}, sync::{Arc, OnceLock}};
use std::ops::{AddAssign, Index, SubAssign};

use ark_ff::{Field, PrimeField, Zero};
use itertools::Itertools;
use rayon::prelude::*;

use crate::polynomial::fragmented::{Fragment, FragmentContent, FragmentedPoly, Shape};
use crate::polynomial::fragmented::FragmentContent::{Consts, Data};

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

// This is dual to fragments from poly.rs. Probably we should refactor this at some point.

#[derive(Clone, Copy, Debug)]
pub enum QueryContent {
    Data,
    Sum,
}

#[derive(Clone, Copy)]
pub struct SegmentQuery {
    mem_idx: usize,
    start: usize,
    end: usize,
    content: QueryContent,
}

impl SegmentQuery {
    pub fn new(start: usize, end: usize, mem_idx: usize, content: QueryContent) -> Self {
        assert!(start <= end);
        Self {start, end, content, mem_idx}
    }
}

#[derive(Clone, Copy, Debug)]

pub struct StSubQuery {
    mem_idx: usize,
    start: usize,
    logsize: u8,
    content: QueryContent,
}

impl StSubQuery {
    pub fn new_unchecked(start: usize, logsize: u8, mem_idx: usize, content: QueryContent) -> Self {
        Self {start, logsize, content, mem_idx}        
    }

    pub fn new(start: usize, logsize: u8, mem_idx: usize, content: QueryContent) -> Self {
        assert!((start >> logsize) << logsize == start);
        Self::new_unchecked(start, logsize, mem_idx, content)
    }
}

pub struct StSubIter {
    start: usize,
    end: usize,
    mem_idx: usize,
    content: QueryContent
}

impl StSubIter {
    pub fn new(query: SegmentQuery) -> Self {
        StSubIter { start: query.start, end: query.end, mem_idx: query.mem_idx, content: query.content }
    }
}

impl Iterator for StSubIter {
    type Item = StSubQuery;

    fn next(&mut self) -> Option<Self::Item> {
        if self.end == self.start {return None}
        let logsize = min(count_trailing_zeros(self.start), log_floor(self.end - self.start));
        self.start += 1 << logsize;
        let prev_mem_idx = self.mem_idx;
        if let QueryContent::Data = self.content {
            self.mem_idx += 1 << logsize;
        } else {}
        Some(Self::Item::new_unchecked(self.start - (1 << logsize), logsize, prev_mem_idx, self.content))
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

#[derive(Clone, Copy, Debug)]
pub struct BinTreeNode {
    parent: usize,
    is_r_child: bool,
    is_leaf: bool,
}

impl BinTreeNode {
    pub fn new(parent: usize, is_r_child: bool, is_leaf: bool) -> Self {
        Self { parent, is_r_child, is_leaf }
    }
}


#[derive(Clone, Debug)]
pub struct BinTree {
    total_logsize: usize, 
    nodes: Vec<Vec<BinTreeNode>>, // Points to parent + L/R identifier, ordered from the root.
    sum_leaves: Vec<(usize, usize, usize)>, // Points to (depth, i, mem_idx)
    data_leaves: Vec<(usize, usize, usize)>,
}

impl BinTree {

    pub fn from_segments(total_logsize: usize, seg_queries: impl Iterator<Item = SegmentQuery>) -> Self {
        Self::from_stsubs(total_logsize, seg_queries.map(|seg| StSubIter::new(seg)).flatten())
    }

/// Assumes that queries are non-intersecting and ordered from left to right.
    pub fn from_stsubs(total_logsize: usize, stsub_queries: impl Iterator<Item = StSubQuery>) -> Self {

        let mut ret = BinTree {
            total_logsize,
            nodes: vec![vec![]; total_logsize + 1],
            data_leaves: vec![],
            sum_leaves: vec![]
        };

        let nodes = &mut ret.nodes;

        let mut nodes_metadata = vec![vec![]; total_logsize + 1];

        let mut prev_right_end = 0;

        for (i, query) in stsub_queries.enumerate() {
            assert!(query.start >= prev_right_end, "query sequence is not properly ordered");
            prev_right_end = query.start + (1 << query.logsize);

            let mut path = query.start >> query.logsize;
            let mut depth = total_logsize - (query.logsize as usize);

            match query.content {
                QueryContent::Data => {ret.data_leaves.push((depth, nodes[depth].len(), query.mem_idx))},
                QueryContent::Sum => {ret.sum_leaves.push((depth, nodes[depth].len(), query.mem_idx))},
            }

            let mut bit;

            while depth > 0 {
                let is_leaf = (depth == total_logsize - (query.logsize as usize));
                bit = (path % 2) == 1;

                match nodes_metadata[depth - 1].last() {
                    None => {
                        nodes[depth].push(BinTreeNode::new(0, bit, is_leaf));
                        nodes_metadata[depth].push(path);
                    },
                    Some(parent_path) => {
                        if path >> 1 == *parent_path {
                            assert!(bit, "should always happen");
                            nodes[depth].push(
                                BinTreeNode::new(
                                    nodes_metadata[depth - 1].len() - 1,
                                    bit,
                                    is_leaf
                                )
                            );
                            nodes_metadata[depth].push(path);
                            break;
                        } else {
                            nodes[depth].push(
                                BinTreeNode::new(
                                    nodes_metadata[depth - 1].len(), 
                                    bit,
                                    is_leaf
                                )
                            );
                            nodes_metadata[depth].push(path);
                        }
                    },
                }

                path >>= 1;
                depth -= 1;
            }
            // Process initial case - add root.
            if i == 0 {
                nodes[0].push(BinTreeNode::new(0, false, false)); // root
                nodes_metadata[0].push(0); // root's path is trivial            
                if query.logsize as usize == total_logsize {
                    nodes[0][0].is_leaf = true; // make the root leaf.
                    return ret;
                }
            }
        }
        ret
    }
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


pub fn compute_subsegments(segments: impl Iterator<Item = SegmentQuery>) -> impl Iterator<Item = StSubQuery> {
    segments.map(|x| StSubIter::new(x)).flatten()
}

/// Slices the data array. 
pub fn slice_data<'a, T>(segments: impl Iterator<Item = SegmentQuery>, mut data: &'a mut [T]) -> Vec<&'a mut [T]> {
    let mut ret = vec![];
    let mut chunk;
    for segment in compute_subsegments(segments) {
        match segment.content {
            QueryContent::Data => {
                (chunk, data) = data.split_at_mut(1 << segment.logsize);
                ret.push(chunk);
            },
            QueryContent::Sum => (),
        }
    };
    ret
}

/// Dual to the data of a polynomial.
#[derive(Clone, Debug)]
pub struct CopolyData<T> {
    pub values: Vec<T>,
    pub sums: Vec<T>,
}

impl<T> CopolyData<T> {
   pub fn iter(&self) -> impl Iterator<Item=&T> {
        self.values.iter().chain(self.sums.iter())
    }
}

impl<T: Send + Sync> CopolyData<T> {
    pub fn par_iter(&self) -> impl ParallelIterator<Item=&T> {
        self.values.par_iter().chain(self.sums.par_iter())
    }
}

impl<T> Index<usize> for CopolyData<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.values.get(index).unwrap_or_else(|| &self.sums[index - self.values.len()])
    }
}

impl<T: AddAssign + Send + Sync + Copy> AddAssign<&Self> for CopolyData<T> {
    fn add_assign(&mut self, rhs: &Self) {
        self.values.par_iter_mut().zip(rhs.values.par_iter()).map(|(l, r)| *l += *r).count();
        self.sums.par_iter_mut().zip(rhs.sums.par_iter()).map(|(l, r)| *l += *r).count();
    }
}

impl<T: SubAssign + Send + Sync + Copy> SubAssign<&Self> for CopolyData<T> {
    fn sub_assign(&mut self, rhs: &Self) {
        self.values.par_iter_mut().zip(rhs.values.par_iter()).map(|(l, r)| *l -= *r).count();
        self.sums.par_iter_mut().zip(rhs.sums.par_iter()).map(|(l, r)| *l -= *r).count();
    }
}


pub trait Copolynomial<F: Field> {
    fn num_vars(&self) -> usize;

    /// Evaluates a copolynomial in a point.
    fn ev(&self, pt: &[F]) -> F;

    /// Binds the first variable to a value.
    /// Importantly, this is the reverse order to the poly_var_bound from liblasso.
    fn bind(&mut self, value: &F);

    // ----- New multi-query API -----

    /// Prepare to answer queries from the shape (and its splits).
    /// Binds together with the shape.
    fn take_shape(&mut self, shape: Arc<OnceLock<Shape>>);

    /// Creates data which adheres to the current shape.
    /// The "constant" values are interpreted as sums over the corresponding segments.
    fn materialize(&mut self) -> CopolyData<F>;

    /// Computes the split of this data.
    fn materialize_split(&mut self) -> (CopolyData<F>, CopolyData<F>);

    // ----- Legacy content - kept for now for testing. -----

    /// Computes the sums over even and odd parts of the standard subset.
    fn half_sums_standard_subset(&self, standard_subset: StandardSubset) -> (F, F);

    /// Computes the inner product with the vector of values on a standard subset.
    fn ip_standard_subset(&self, standard_subset: StandardSubset, values: &[F]) -> F;
    
    /// Computes the values on a standard subset.
    fn materialize_standard_subset(&self, standard_subset: StandardSubset, target: &mut[F]);

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
    shape: Option<Arc<OnceLock<Shape>>>,
}

impl<F: Field> EqPoly<F> {
    pub fn new(point: Vec<F>) -> Self {
        EqPoly { multiplier: F::one(), point, shape: None }
    }
}

pub fn materialize_eq_slice<F: Field>(multiplier: F, point: &[F], slice: &mut [MaybeUninit<F>]) {
    let n = point.len();
    assert!(1 << n == slice.len());
    slice[0] = MaybeUninit::new(multiplier);
    for i in 0..n {
        let half = 1 << i;
        let pt_idx = n - i - 1;
        let (a, b) = slice[0..2*half].split_at_mut(half);

        b
            .par_iter_mut()
            .enumerate()
            .map(|(j, x)| *x = MaybeUninit::new(unsafe{a[j].assume_init()} * point[pt_idx])).count();
        a
            .par_iter_mut()
            .enumerate()
            .map(|(j, x)| *x = MaybeUninit::new(unsafe{x.assume_init() - b[j].assume_init()})).count();
    }
}

impl<F: Field> EqPoly<F> {
    pub fn materialize_eq_with_shape(&self, shape: &Shape) -> CopolyData<F> {
        let Shape{
            fragments,
            data_len,
            num_consts,
            split: _ ,
            dedup_consts_len,
        } = shape;

        let mut data = vec![MaybeUninit::<F>::uninit(); *data_len];
        let mut sums = vec![F::zero(); *num_consts];
        let mut sum_initialized = vec![false; *num_consts];

        let bintree = BinTree::from_segments(
            self.num_vars(),
            fragments.iter().map(|Fragment{mem_idx, len, content, start}| {
                SegmentQuery {
                    mem_idx: *mem_idx,
                    start: *start,
                    end: start + len,
                    content : match content {
                        FragmentContent::Data => QueryContent::Data,
                        FragmentContent::Consts => QueryContent::Sum
                    }
                }
            }));

        let multipliers : &mut Vec<Vec<(F, Option<F>)>> = &mut vec![vec![(self.multiplier, None)]];

        if !bintree.nodes[0][0].is_leaf {
            multipliers[0][0].1 = Some(multipliers[0][0].0 * self.point[0])
        }

        for i in 1 .. self.num_vars() + 1 {
            let j = bintree.nodes[i].len();
            multipliers.push((0..j).into_par_iter().map(|idx| {
                let BinTreeNode { parent, is_r_child, is_leaf } = bintree.nodes[i][idx];
                let m = if is_r_child {
                    multipliers[i-1][parent].1.unwrap()
                } else {
                    multipliers[i-1][parent].0 - multipliers[i-1][parent].1.unwrap()
                };
                match is_leaf {
                    false => (m, Some(self.point[i] * m)),
                    true => (m, None),
                }
            }).collect());
        }

        bintree.sum_leaves.iter().map(|&(depth, idx, mem_idx)| {
            sums[mem_idx] = if sum_initialized[mem_idx] {
                sums[mem_idx] + multipliers[depth][idx].0
            } else {
                multipliers[depth][idx].0
            };
            sum_initialized[mem_idx] = true;
        }).count();

        slice_data(shape.fragments.iter().map(|&Fragment { mem_idx, len, content, start }|{
            let content = match content {
                FragmentContent::Data => QueryContent::Data,
                FragmentContent::Consts => QueryContent::Sum,
            };
            SegmentQuery{ mem_idx, start, end: (start+len), content }
        }), &mut data)
            .into_par_iter()
            .zip_eq(
                bintree.data_leaves.par_iter()
            ).map(|(slice, (depth, idx, _))|{
            materialize_eq_slice(multipliers[*depth][*idx].0, &self.point[*depth ..], slice)
        }).count();

        CopolyData{values: unsafe{ transmute::<Vec<MaybeUninit<F>>, Vec<F>>(data) }, sums}

    }
}

impl<F: Field> Copolynomial<F> for EqPoly<F> {
    fn num_vars(&self) -> usize {
        self.point.len()
    }

    fn ev(&self, pt: &[F]) -> F {
        let r = &self.point;
        assert!(r.len() == pt.len());
        self.multiplier * r.iter().zip(pt.iter()).fold(F::zero(), |acc, (x, y)| acc * (*x * y + (F::one() - x)*(F::one() - y)))
    }
    
    fn bind(&mut self, value: &F) {
        let p0 = self.point.pop().unwrap();
        self.multiplier *= p0 * value + (F::one() - p0) * (F::one() - value);
        if self.shape.is_some() {
            let _ = self.shape.as_ref().unwrap().clone().get().unwrap().split();
            self.shape = Some(self.shape.as_ref().unwrap().clone().get().unwrap().split.clone());
        };
    }
    
    fn take_shape(&mut self, shape: Arc<OnceLock<Shape>>) {
        assert!(self.shape.is_none());
        self.shape = Some(shape);
    }
    
    fn materialize(&mut self) -> CopolyData<F> {
        let shape = self.shape.as_ref().unwrap().get().unwrap();
        self.materialize_eq_with_shape(shape)
    }
    
    fn materialize_split(&mut self) -> (CopolyData<F>, CopolyData<F>) {
        let mut point = self.point.clone();
        let m1 = point.pop().unwrap();
        let m0 = F::one() - m1;
        let a;
        let b;
        if m0.is_zero() {
            let mut eq1 = Self::new(point);
            eq1.multiplier = m1;
            b = eq1.materialize_eq_with_shape(self.shape.as_ref().unwrap().get().unwrap().split());
            a = CopolyData { values: vec![F::zero(); b.values.len()], sums: vec![F::zero(); b.sums.len()]}

        } else {
            let m = m1 * m0.inverse().unwrap();
            let mut eq0 = Self::new(point);
            eq0.multiplier = m0;
            a = eq0.materialize_eq_with_shape(self.shape.as_ref().unwrap().get().unwrap().split());
            b = CopolyData {
                        values: a.values.iter().map(|x| *x * m).collect(),
                        sums: a.sums.iter().map(|x| *x * m).collect()
                    };
        }
        (a, b)
    }        

    // -------- snip ----------

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

    fn ev(&self, pt: &[F]) -> F {
        assert!(pt.len() == self.num_vars());
        let mut poly = self.clone();
        for x in pt.iter().rev() {
            poly.bind(x);
        }
        poly.eq_multiplier + poly.rot_multiplier
    }

    fn bind(&mut self, x0: &F) {
        let y0 = self.point.pop().unwrap();
        let y0x0 = y0 * x0;
        self.eq_multiplier *= F::one() - y0 - x0 + y0x0.double(); // Multiply by eq(x0, y0)
        self.eq_multiplier += (y0 - y0x0) * self.rot_multiplier; // Add the component from Rot.
        self.rot_multiplier *= *x0 - y0x0;
    }
    
    fn take_shape(&mut self, shape: Arc<OnceLock<Shape>>) {
        todo!()
    }
    
    fn materialize(&mut self) -> CopolyData<F> {
        todo!()
    }
    
    fn materialize_split(&mut self) -> (CopolyData<F>, CopolyData<F>) {
        todo!()
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
    use liblasso::poly::eq_poly::EqPolynomial;
    use liblasso::utils::math::Math;
    use ark_ff::Field;

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
        eqpoly.bind(&e0);

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
        rot.bind(&r0);
        rot.bind(&r1);

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
        rot.bind(&r);
        let r = x.pop().unwrap();
        y_evs.bound_poly_var_bot(&r);
        y_evs.Z.truncate(16);
        rot.bind(&r);

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
        let mut acc = 0;
        let queries = sizes.into_iter().map(|size| {acc += size; SegmentQuery::new(acc - size, acc, acc - size, QueryContent::Data)});
        let bintree = BinTree::from_stsubs(5, compute_subsegments(queries));

        println!("{:?}", bintree);
    }

    #[test]
    fn test_eq_new_materialize() {
        let rng = &mut test_rng();

        let num_consts = 3;
        let _shape = Shape::rand_by_frag_spec(rng, 10, 10, num_consts);

        let lf = _shape.fragments.last().unwrap();
        let num_vars = (lf.start + lf.len).log_2();
        let point : Vec<Fr> = repeat_with(|| Fr::rand(rng)).take(num_vars).collect();
        let lhs = EqPolynomial::new(point.clone()).evals();

        let mut eq = EqPoly::new(point);
        let mut shape = Arc::new(OnceLock::new());
        shape.get_or_init(||{_shape});
        eq.take_shape(shape);

        let mut lhs_sums = vec![Fr::ZERO; num_consts];

        let materialized : CopolyData<Fr> = eq.materialize();

        for fragment in eq.shape.unwrap().get().unwrap().fragments.iter() {
            match fragment.content {
                FragmentContent::Data => {
                    assert_eq!(
                        lhs[fragment.start .. fragment.start + fragment.len],
                        materialized.values[fragment.mem_idx .. fragment.mem_idx + fragment.len]
                    )
                },
                FragmentContent::Consts => {
                    lhs_sums[fragment.mem_idx] += lhs[fragment.start .. fragment.start + fragment.len].iter().sum::<Fr>();
                },
            }
        }

        assert_eq!(lhs_sums, materialized.sums);

    }

}