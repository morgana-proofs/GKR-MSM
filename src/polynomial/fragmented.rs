use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::mem::MaybeUninit;
use std::ops::{Add, AddAssign, Mul, Sub};
use std::sync::{Arc, OnceLock};
use ark_ff::Field;
use ark_std::iterable::Iterable;
use ark_std::rand::{Rng, RngCore};
use itertools::Itertools;
use liblasso::utils::math::Math;
use rayon::prelude::*;
use crate::polynomial::fragmented::FragmentContent::{Consts, Data};

pub trait Split: Sized {
    fn split(&self) -> (Self, Self);
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum FragmentContent {
    Data,
    Consts,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Fragment {
    pub mem_idx: usize,
    pub len: usize,
    pub content: FragmentContent,
    pub start: usize,
}

impl Fragment {
    pub fn new_of(content: FragmentContent) -> Self {
        Self {
            mem_idx: 0,
            len: 0,
            content,
            start: 0,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Shape {
    pub fragments: Vec<Fragment>,
    pub data_len: usize,
    pub num_consts: usize,
    pub dedup_consts_len: usize,
    pub split: Arc<OnceLock<Shape>>,
}


const MERGE_THRESH: usize = 2;

fn should_merge(f1: &Fragment, f2: &Fragment) -> bool {
    match (&f1.content, &f2.content) {
        (Data, Data) => true,
        (Data, Consts) => {
            f2.len < MERGE_THRESH
        },
        (Consts, Data) => false,
        (Consts, Consts) => {
            f1.mem_idx == f2.mem_idx
        },
    }
}

impl Shape {
    pub fn empty(num_consts: usize) -> Self {
        Self { fragments: vec![], data_len: 0, num_consts, dedup_consts_len: 0, split: <_>::default() }
    }
    
    /// Derives num_consts automatically.
    pub fn new(shape: Vec<Fragment>, num_consts: usize) -> Self {
        let mut new = Self::empty(num_consts);
        new.fragments = shape;
        new.finalize();
        new
    }

    /// Merges last and one before last fragments of given poly
    /// Assumes that they can be merged and are correct
    fn merge_in(&mut self, last: Fragment) {
        let prev = self.fragments.last_mut().unwrap();
        match (&prev.content, last.content) {
            (Data, Data) => {
                prev.len += last.len;
                self.data_len += last.len;
            }
            (Data, Consts) => {
                prev.len += last.len;
                self.data_len += last.len;
            }
            (Consts, Data) => {
                unreachable!()
            }
            (Consts, Consts) => {
                prev.len += last.len;
            }
        }
    }

    pub fn add(&mut self, fragment: Fragment) {

        println!("State: {:?}", self);
        println!("Adding fragment {:?}", fragment);
        let merge;

        match self.fragments.last() {
            None => {
                merge = false;
            }
            Some(prev) => {
                if should_merge(&prev, &fragment) {
                    merge = true;
                } else {
                    merge = false;
                }
            }
        }

        if merge {
            self.merge_in(fragment)
        } else {
            match &fragment.content {
                Data => {
                    assert!(fragment.mem_idx == self.data_len);
                    self.data_len += fragment.len;
                },
                Consts => {
                    assert!(fragment.mem_idx < self.num_consts);
                    self.dedup_consts_len += 1;
                },
            }
            self.fragments.push(fragment);
        }
    }

    /// This is only used in new() construction. Adds must preserve all invariants.
    fn finalize(&mut self) {
        self.data_len = 0;
        self.dedup_consts_len = 0;

        for frag in self.fragments.iter() {
            match frag.content {
                Data => {
                    assert_eq!(frag.mem_idx, self.data_len, "Shape data incorrect at frag.mem_idx = {:?}, self.data_len = {:?}, \nFull shape{:?}", frag.mem_idx, self.data_len, self);
                    self.data_len += frag.len;
                }
                Consts => {
                    self.dedup_consts_len += 1;
                    assert!(frag.mem_idx < self.num_consts);
                }
            }
        }
    }

    /// Does not actually need mutable receiver.
    pub fn assert_correct(&mut self) {
        let data_len = self.data_len;
        let dedup_consts_len = self.dedup_consts_len;

        self.finalize();

        assert_eq!(data_len, self.data_len);
        assert_eq!(dedup_consts_len, self.dedup_consts_len);
    }

    /// Slices the data array. Also makes the integrity checks (should eventually be
    /// moved to shape construction) - namely, it does check that data layout
    /// used by the shape is contigious. 
    pub fn slice_data<'a, T>(&self, mut data: &'a mut [T]) -> Vec<&'a mut [T]> {
        assert_eq!(data.len(), self.data_len);
        let mut ret = Vec::with_capacity(self.fragments.len());
        let mut chunk;
        for fragment in &self.fragments {
            match fragment.content {
                Data => {
                    (chunk, data) = data.split_at_mut(fragment.len);
                    ret.push(chunk);
                },
                Consts => (),
            }
        };
        ret
    }

    pub fn rand<RNG: Rng>(rng: &mut RNG, frag_size: usize, frags: usize) -> Self {
        println!("rand entry");
        
        let mut rand = Self::empty(1);
        let mut const_size = 0;
        let mut start = 0;
        for _ in 0..frags {
            let len = rng.next_u64() as usize % frag_size + 1;
            let content = if rng.next_u32() % 2 == 0 { Data } else { Consts };
            let mem_idx = match content {
                Data => rand.data_len,
                Consts => {rng.next_u64() as usize % (const_size + 1)}
            };
            println!("Logging fragment addition: mem_idx {:?}, len {:?}, content {:?}, start {:?}", mem_idx, len, content, start);
            rand.add(Fragment {
                mem_idx,
                len,
                content,
                start,
            });
            start += len;
        }
        let len = (1 << start.log_2()) - start;
        rand.add(Fragment {
            mem_idx: rng.next_u64() as usize % (const_size + 1),
            len,
            content: Consts,
            start,
        });

        rand.assert_correct();

        rand
    }
}

impl Shape {
    pub fn split(&self) -> &Self {
        self.split.get_or_init(|| {
            let mut l = Self::empty(self.num_consts);
            for frag in self.fragments.iter() {
                let Fragment { mut len, content, mut start, mem_idx} = frag;
                if start % 2 == 1 {
                    // move first element to the previous frag, push previous frag
                    match content {
                        Data => {
                            len += 1;
                            start -= 1;
                        }
                        Consts => {
                            len -= 1;
                            start += 1;
                            l.add(Fragment {
                                mem_idx: l.data_len,
                                len: 1,
                                content: Data,
                                start: (start - 2) / 2,
                            });
                        }
                    }
                }
                if len % 2 == 1 {
                    len -= 1;
                }
                if len > 0 {
                    match content {
                        Data => {
                            l.add(Fragment {
                                mem_idx: l.data_len,
                                len: len / 2,
                                content: Data,
                                start: start / 2,
                            });
                        }
                        Consts => {
                            if len / 2 < MERGE_THRESH {
                                l.add(Fragment {
                                    mem_idx: l.data_len,
                                    len: len / 2,
                                    content: Data,
                                    start: start / 2,
                                });
                            } else {
                                l.add(Fragment {
                                    mem_idx: *mem_idx,
                                    len: len / 2,
                                    content: Consts,
                                    start: start / 2,
                                });
                            }
                        }
                    };
                }
            }
            l.assert_correct();
            l  
        })
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FragmentedPoly<F> {
    pub data: Vec<F>,
    pub consts: Vec<F>,
    pub shape: Arc<OnceLock<Shape>>,
}

impl<F> FragmentedPoly<F> {
    pub fn new(data: Vec<F>, consts: Vec<F>, shape: Arc<OnceLock<Shape>>) -> Self {
        Self {
            data,
            consts,
            shape,
        }
    }

    pub fn num_vars(&self) -> usize {
        match self.shape.get().unwrap().fragments.last() {
            None => 0,
            Some(Fragment{ len, start, .. }) => (start + len).log_2(),
        }
    }

    fn get_by_fragment(&self, frag: &Fragment, idx: usize) -> &F {
        match frag.content {
            Data => &self.data[frag.mem_idx + idx],
            Consts => &self.consts[frag.mem_idx],
        }
    }
}

impl<F: From<u64>> FragmentedPoly<F> {
    pub fn rand<RNG: Rng>(rng: &mut RNG, frag_size: usize, frags: usize) -> Self {
        let shape = Arc::new(OnceLock::new());
        let s = shape.get_or_init(|| Shape::rand(rng, frag_size, frags));
        Self {
            data: (0..s.data_len).map(|_| F::from(rng.next_u64())).collect_vec(),
            consts: (0..s.num_consts).map(|_| F::from(rng.next_u64())).collect_vec(),
            shape,
        }
    }
}

impl<F: Clone> FragmentedPoly<F> {
    // pub fn morph_into_shape(&self, source: &Shape, target: &Shape) -> Self {
    //     let mut new = Self::new(Vec::with_capacity(target.data_len), Vec::with_capacity(target.consts_len));
    //     let mut source_iter = source.shape.iter();
    //     let mut target_iter = target.shape.iter();
    //
    //     let mut source_frag = source_iter.next();
    //     let mut source_frag_counter = 0;
    //     for target_frag in target_iter {
    //         match &target_frag.content {
    //             Data => {
    //                 for _ in 0..target_frag.len {
    //                     new.data.push(self.get_by_fragment(source_frag.unwrap(), source_frag_counter).clone());
    //                     source_frag_counter += 1;
    //
    //                     if source_frag_counter >= source_frag.unwrap().len {
    //                         source_frag = source_iter.next();
    //                         source_frag_counter = 0;
    //                     }
    //                 }
    //             }
    //             Consts => {
    //                 new.consts.push(self.get_by_fragment(source_frag.unwrap(), source_frag_counter).clone());
    //                 source_frag_counter += target_frag.len;
    //
    //                 if source_frag_counter >= source_frag.unwrap().len {
    //                     source_frag = source_iter.next();
    //                     source_frag_counter = 0;
    //                 }
    //             }
    //         }
    //     }
    //     new
    // }

    pub fn split(&self) -> (Self, Self) {
        let source = self.shape.get().unwrap();
        let target = self.shape.get().unwrap().split();
        let split_shape = self.shape.get().unwrap().split.clone();
        let last_target = target.fragments.last().unwrap();
        let data_size = last_target.mem_idx + match last_target.content {
            Data => last_target.len,
            Consts => 1,
        };
        let (mut l, mut r) = (Self::new(Vec::with_capacity(data_size), self.consts.clone(), split_shape.clone()), Self::new(Vec::with_capacity(data_size), self.consts.clone(), split_shape));

        let mut source_iter = source.fragments.iter();
        let mut target_iter = target.fragments.iter();

        let mut source_frag = source_iter.next();
        let mut source_frag_counter = 0;
        for target_frag in target_iter {
            match &target_frag.content {
                Data => {
                    for _ in 0..target_frag.len {
                        l.data.push(self.get_by_fragment(source_frag.unwrap(), source_frag_counter).clone());
                        source_frag_counter += 1;
                        if source_frag_counter >= source_frag.unwrap().len {
                            source_frag = source_iter.next();
                            source_frag_counter = 0;
                        }
                        r.data.push(self.get_by_fragment(source_frag.unwrap(), source_frag_counter).clone());
                        source_frag_counter += 1;

                        if source_frag_counter >= source_frag.unwrap().len {
                            source_frag = source_iter.next();
                            source_frag_counter = 0;
                        }
                    }
                }
                Consts => {
                    source_frag_counter += target_frag.len * 2;

                    if source_frag_counter >= source_frag.unwrap().len {
                        source_frag = source_iter.next();
                        source_frag_counter = 0;
                    }
                }
            }
        }

        (l, r)
    }
}

impl<F: AddAssign + Mul<Output=F> + Sub<Output=F> + Send + Sync + Sized + Copy> FragmentedPoly<F> {
    pub fn bind(&self, f: &F) -> Self {
        let (mut l, r) = self.split();
        l.data.par_iter_mut()
            .chain(l.consts.par_iter_mut())
            .zip(r.data.par_iter().chain(r.consts.par_iter()))
            .map(|(l, r)| { *l += *f * (*r - *l) }).count();
        l
    }

    pub fn evaluate(&self, r: &[F]) -> F {
        let mut tmp = None;
        for f in r.iter().rev() {
            tmp = Some(
                tmp
                    .as_ref()
                    .unwrap_or(self)
                    .bind(f)
            );
        }
        let cur = tmp.as_ref().unwrap_or(self);
        cur.get_by_fragment(cur.shape.get().unwrap().fragments.first().unwrap(), 0).clone()
    }
}

impl <F: Clone> FragmentedPoly<F> {
    fn into_vec(self) -> Vec<F> {
        let mut out = vec![];
        for fragment in &self.shape.get().unwrap().fragments {
            for idx in 0..fragment.len {
                out.push(self.get_by_fragment(fragment, idx).clone());
            }
        }
        out
    }
}


#[cfg(test)]
mod tests {
    use std::cell::OnceCell;
    use std::iter::repeat_with;
    use std::sync::{Arc, OnceLock, RwLock, RwLockWriteGuard, TryLockError, TryLockResult};
    use ark_ed_on_bls12_381_bandersnatch::Fr;
    use ark_std::rand::RngCore;
    use ark_std::{test_rng, UniformRand};
    use itertools::Itertools;
    use liblasso::poly::dense_mlpoly::DensePolynomial;
    use crate::polynomial::nested_poly::{evaluate_exact, NestedPolynomial, RandParams};
    use super::*;


    #[test]
    fn bind_rand_poly() {
        let rng = &mut test_rng();
        for _ in 0..100 {
            let shape_cell = Arc::new(OnceLock::new());
            let shape = Shape::rand(rng, 10, 10);
            shape_cell.set(shape.clone()).unwrap();
            let split = shape.split();
            let p = FragmentedPoly::new(
                (0..shape.data_len).map(|_| Fr::from(rng.next_u64())).collect_vec(),
                (0..shape.num_consts).map(|_| Fr::from(rng.next_u64())).collect_vec(),
                shape_cell,
            );
            let v = p.clone().into_vec();
            let mut ev = DensePolynomial::new(v.clone());
            let f = Fr::from(rng.next_u64());
            ev.bound_poly_var_bot(&f);
            let el = v.iter().cloned().step_by(2).collect_vec();
            let er = v.iter().cloned().skip(1).step_by(2).collect_vec();

            let l = p.bind(&f);

            assert_eq!(ev.vec().iter().take(1 << ev.num_vars).cloned().collect_vec(), l.into_vec());
        }
    }

    #[test]
    fn split_rand_poly() {
        let rng = &mut test_rng();
        for _ in 0..100 {
            let shape_cell = Arc::new(OnceLock::new());
            let shape = Shape::rand(rng, 10, 10);
            shape_cell.set(shape.clone()).unwrap();
            let split = shape.split();
            let p = FragmentedPoly::new(
                (0..shape.data_len).map(|_| rng.next_u64() % 10).collect_vec(),
                (0..shape.num_consts).map(|_| rng.next_u64() % 10).collect_vec(),
                shape_cell,
            );
            let v = p.clone().into_vec();
            let el = v.iter().cloned().step_by(2).collect_vec();
            let er = v.iter().cloned().skip(1).step_by(2).collect_vec();
            let (l, r) = p.split();
            assert_eq!(el, l.into_vec());
            assert_eq!(er, r.into_vec());
        }
    }

    #[test]
    fn split_poly() {
        let v = vec![
            4, 4, 4, 4, 4, 4, 4, 4, 4,
            4, 4,
            0,
            4,
            4, 4, 4, 4, 4, 4, 4,
            4, 3, 7,
            4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
            2, 4, 4, 1, 2, 2, 7, 8,
            4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
        ];
        let d = vec![
            4, 3, 7, 2, 4, 4, 1, 2, 2, 7, 8,
        ];
        let c = vec![
            4, 0
        ];
        let s = vec![
            Fragment {
                mem_idx: 0,
                len: 9,
                content: Consts,
                start: 0,
            },
            Fragment {
                mem_idx: 0,
                len: 2,
                content: Consts,
                start: 9,
            },
            Fragment {
                mem_idx: 1,
                len: 1,
                content: Consts,
                start: 11,
            },
            Fragment {
                mem_idx: 0,
                len: 1,
                content: Consts,
                start: 12,
            },
            Fragment {
                mem_idx: 0,
                len: 7,
                content: Consts,
                start: 13,
            },
            Fragment {
                mem_idx: 0,
                len: 3,
                content: Data,
                start: 20,
            },
            Fragment {
                mem_idx: 0,
                len: 10,
                content: Consts,
                start: 23,
            },
            Fragment {
                mem_idx: 3,
                len: 8,
                content: Data,
                start: 33,
            },
            Fragment {
                mem_idx: 0,
                len: 23,
                content: Consts,
                start: 41,
            },
        ];

        let shape = Shape::new(s, 2);
        let shape_cell = Arc::new(OnceLock::new());
        shape_cell.set(shape.clone()).unwrap();
        let split = shape.split();
        let p = FragmentedPoly::new(d, c, shape_cell);
        assert_eq!(v, p.clone().into_vec());
        let el = v.iter().cloned().step_by(2).collect_vec();
        let er = v.iter().cloned().skip(1).step_by(2).collect_vec();
        let (l, r) = p.split();
        assert_eq!(el, l.into_vec());
        assert_eq!(er, r.into_vec());
    }

    #[test]
    fn split_shape() {
        let s = Shape::new(vec![
            Fragment {
                mem_idx: 0,
                len: 4,
                content: Data,
                start: 0,
            },
            Fragment {
                mem_idx: 0,
                len: 4,
                content: Consts,
                start: 4,
            },
            Fragment {
                mem_idx: 4,
                len: 6,
                content: Data,
                start: 8,
            },
            Fragment {
                mem_idx: 1,
                len: 2,
                content: Consts,
                start: 14,
            },
            Fragment {
                mem_idx: 2,
                len: 4,
                content: Consts,
                start: 16,
            },
            Fragment {
                mem_idx: 10,
                len: 8,
                content: Data,
                start: 20,
            },
            Fragment {
                mem_idx: 3,
                len: 4,
                content: Consts,
                start: 28,
            },
        ],
        4
        );
        let l = s.split();
        let el =  Shape::new(vec![
            Fragment {
                mem_idx: 0,
                len: 2,
                content: Data,
                start: 0,
            },
            Fragment {
                mem_idx: 0,
                len: 2,
                content: Consts,
                start: 2,
            },
            Fragment {
                mem_idx: 2,
                len: 4,
                content: Data,
                start: 4,
            },
            Fragment {
                mem_idx: 2,
                len: 2,
                content: Consts,
                start: 8,
            },
            Fragment {
                mem_idx: 6,
                len: 4,
                content: Data,
                start: 10,
            },
            Fragment {
                mem_idx: 3,
                len: 2,
                content: Consts,
                start: 14,
            },
        ],
        4);
        assert_eq!(l, &el);
        let ll = l.split();
        let ell =  Shape::new(vec![
            Fragment {
                mem_idx: 0,
                len: 8,
                content: Data,
                start: 0,
            },
        ], 4);
        assert_eq!(ll, &ell);
    }

    #[test]
    fn evaluate() {
        let mut rng = &mut test_rng();

        for _ in 0..10 {
            let poly = FragmentedPoly::rand(rng, 10, 10);
            let flat = poly.clone().into_vec();
            let dense = DensePolynomial::new(flat.clone());
            for _ in 0..10 {
                let point: Vec<_> = repeat_with(|| ark_bls12_381::Fr::rand(rng)).take(poly.num_vars()).collect();

                let straight_eval = evaluate_exact(&mut flat.clone(), &point);
                let nested_eval = poly.evaluate(&point);
                let dense_eval = dense.evaluate(&point);
                assert_eq!(straight_eval, nested_eval);
                assert_eq!(straight_eval, dense_eval);
            }
        }
    }
}