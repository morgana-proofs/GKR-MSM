use std::cmp::{max, min};
use std::fmt::Debug;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::io::repeat;
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Mul, Sub};
use std::sync::Arc;
use ark_ff::Field;
use ark_std::iterable::Iterable;
use ark_std::rand;
use ark_std::rand::{Rng, RngCore};
use itertools::{Either, Itertools, repeat_n};
use liblasso::utils::math::Math;
use rayon::prelude::*;
use crate::poly::FragmentContent::{Consts, Data};

pub trait Split: Sized {
    fn split(&self) -> (Self, Self);
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
enum FragmentContent {
    Data,
    Consts,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct Fragment {
    idx: usize,
    len: usize,
    content: FragmentContent,
    start: usize,
}

impl Fragment {
    pub fn new_of(content: FragmentContent) -> Self {
        Self {
            idx: 0,
            len: 0,
            content,
            start: 0,
        }
    }
}

#[derive(Default, Debug, Clone, Eq, PartialEq)]
struct Shape {
    shape: Vec<Fragment>,
    data_len: usize,
    consts_len: usize,
}

/// Merges last and one before last fragments of given poly
/// Assumes that they can be merged and are correct
fn merge_last_fragments(shape: &mut Vec<Fragment>, last: Fragment) {
    let prev = shape.last_mut().unwrap();
    match (&prev.content, last.content) {
        (FragmentContent::Data, FragmentContent::Data) => {
            prev.len += last.len;
        }
        (FragmentContent::Data, FragmentContent::Consts) => {
            prev.len += last.len;
        }
        (FragmentContent::Consts, FragmentContent::Data) => {
            unreachable!()
        }
        (FragmentContent::Consts, FragmentContent::Consts) => {
            prev.len += last.len;
        }
    }
}

const const_merge_thresh: usize = 2;

fn should_merge(poly: &Vec<Fragment>, f1: &Fragment, f2: &Fragment) -> bool {
    match (&f1.content, &f2.content) {
        (FragmentContent::Data, FragmentContent::Data) => true,
        (FragmentContent::Data, FragmentContent::Consts) => {
            f2.len < const_merge_thresh
        },
        (FragmentContent::Consts, FragmentContent::Data) => false,
        (FragmentContent::Consts, FragmentContent::Consts) => {
            f1.idx == f2.idx
        },
    }
}

impl Shape {
    pub fn new(shape: Vec<Fragment>) -> Self {
        let mut new = Self::default();
        new.shape = shape;
        new.finish();
        new
    }
    fn add(&mut self, fragment: Fragment) {
        match self.shape.last() {
            None => {
                self.shape.push(fragment);
            }
            Some(prev) => {
                if should_merge(&self.shape, &prev, &fragment) {
                    merge_last_fragments(&mut self.shape, fragment)
                } else {
                    self.shape.push(fragment);
                }
            }
        }

    }

    fn finish(&mut self) {
        self.data_len = 0;
        self.consts_len = 0;
        for frag in self.shape.iter() {
            match frag.content {
                Data => {self.data_len += frag.len}
                Consts => {self.consts_len = max(self.consts_len, frag.idx + 1)}
            }
        }
    }

    pub fn rand<RNG: Rng>(rng: &mut RNG, frag_size: usize, frags: usize) -> Self {
        let mut rand = Self::new(vec![]);
        let mut data_idx = 0;
        let mut const_size = 0;
        let mut start = 0;
        for _ in 0..frags {
            let len = rng.next_u64() as usize % frag_size + 1;
            let content = if rng.next_u32() % 2 == 0 { Data } else { Consts };
            let idx = match content {
                Data => data_idx,
                Consts => {rng.next_u64() as usize % (const_size + 1)}
            };
            rand.add(Fragment {
                idx,
                len,
                content,
                start,
            });
            start += len;
            match content {
                Data => {data_idx += len}
                Consts => {}
            }
        }
        let len = (1 << start.log_2()) - start;
        rand.add(Fragment {
            idx: rng.next_u64() as usize % (const_size + 1),
            len,
            content: Consts,
            start,
        });
        rand.finish();
        rand
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct Poly<F> {
    data: Vec<F>,
    consts: Vec<F>,
}

impl<F> Poly<F> {
    pub fn new(data: Vec<F>, consts: Vec<F>) -> Self {
        Self {
            data,
            consts,
        }
    }

    fn get_by_fragment(&self, frag: &Fragment, idx: usize) -> &F {
        match frag.content {
            Data => &self.data[frag.idx + idx],
            Consts => &self.consts[frag.idx],
        }
    }
}

impl<F: Clone> Poly<F> {
    pub fn morph_into_shape(&self, source: &Shape, target: &Shape) -> Self {
        let mut new = Self::new(Vec::with_capacity(target.data_len), Vec::with_capacity(target.consts_len));
        let mut source_iter = source.shape.iter();
        let mut target_iter = target.shape.iter();

        let mut source_frag = source_iter.next();
        let mut source_frag_counter = 0;
        for target_frag in target_iter {
            match &target_frag.content {
                Data => {
                    for _ in 0..target_frag.len {
                        new.data.push(self.get_by_fragment(source_frag.unwrap(), source_frag_counter).clone());
                        source_frag_counter += 1;

                        if source_frag_counter >= source_frag.unwrap().len {
                            source_frag = source_iter.next();
                            source_frag_counter = 0;
                        }
                    }
                }
                Consts => {
                    new.consts.push(self.get_by_fragment(source_frag.unwrap(), source_frag_counter).clone());
                    source_frag_counter += target_frag.len;

                    if source_frag_counter >= source_frag.unwrap().len {
                        source_frag = source_iter.next();
                        source_frag_counter = 0;
                    }
                }
            }
        }
        new
    }

    pub fn split_into_shape(&self, source: &Shape, target: &Shape) -> (Self, Self) {
        let last_target = target.shape.last().unwrap();
        let data_size = last_target.idx + match last_target.content {
            Data => last_target.len,
            Consts => 1,
        };
        let (mut l, mut r) = (Self::new(Vec::with_capacity(data_size), self.consts.clone()), Self::new(Vec::with_capacity(data_size), self.consts.clone()));

        let mut source_iter = source.shape.iter();
        let mut target_iter = target.shape.iter();

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

impl<F: AddAssign + Mul<Output=F> + Sub<Output=F> + Send + Sync + Sized + Copy> Poly<F> {
    pub fn bind(a: &mut Self, b: &Self, f: &F) {
        a.data.par_iter_mut()
            .chain(a.consts.par_iter_mut())
            .zip(b.data.par_iter().chain(b.consts.par_iter()))
            .map(|(l, r)| { *l += *f * (*r - *l) }).count();
    }
}

impl <F: Clone> Poly<F> {
    fn into_vec(self, shape: &Shape) -> Vec<F> {
        let mut out = vec![];
        for fragment in &shape.shape {
            for idx in 0..fragment.len {
                out.push(self.get_by_fragment(fragment, idx).clone());
            }
        }
        out
    }
}

impl Shape {
    fn split(&self) -> Self {
        let mut l = Self::default();
        let mut data_idx = 0;
        for frag in self.shape.iter() {
            let Fragment { mut len, content, mut start , idx} = frag;
            if start % 2 == 1 {
                // steal first element into previous frag, push previous frag
                match content {
                    Data => {
                        len += 1;
                        start -= 1;
                    }
                    Consts => {
                        len -= 1;
                        start += 1;
                        l.add(Fragment {
                            idx: data_idx,
                            len: 1,
                            content: FragmentContent::Data,
                            start: (start - 2) / 2,
                        });
                        data_idx += 1;
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
                            idx: data_idx,
                            len: len / 2,
                            content: Data,
                            start: start / 2,
                        });
                        data_idx += len / 2;
                    }
                    Consts => { 
                        if len / 2 < const_merge_thresh {
                            l.add(Fragment {
                                idx: data_idx,
                                len: len / 2,
                                content: Data,
                                start: start / 2,
                            });
                            data_idx += len / 2;
                        } else {
                            l.add(Fragment {
                                idx: *idx,
                                len: len / 2,
                                content: Consts,
                                start: start / 2,
                            });
                        }
                    }
                };
            }
        }
        l.finish();
        l
    }
}




#[cfg(test)]
mod tests {
    use ark_ed_on_bls12_381_bandersnatch::Fr;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;
    use itertools::Itertools;
    use liblasso::poly::dense_mlpoly::DensePolynomial;
    use crate::poly::{Fragment, Poly, Shape, Split};
    use crate::poly::FragmentContent::{Consts, Data};


    #[test]
    fn bind_rand_poly() {
        let rng = &mut test_rng();
        for _ in 0..100 {
            let shape = Shape::rand(rng, 10, 10);
            let split = shape.split();
            let p = Poly::new(
                (0..shape.data_len).map(|_| Fr::from(rng.next_u64())).collect_vec(),
                (0..shape.consts_len).map(|_| Fr::from(rng.next_u64())).collect_vec(),
            );
            let v = p.clone().into_vec(&shape);
            let mut ev = DensePolynomial::new(v.clone());
            let f = Fr::from(rng.next_u64());
            ev.bound_poly_var_bot(&f);
            let el = v.iter().cloned().step_by(2).collect_vec();
            let er = v.iter().cloned().skip(1).step_by(2).collect_vec();

            let (mut l, r) = p.split_into_shape(&shape, &split);
            Poly::bind(&mut l, &r, &f);
            drop(r);

            assert_eq!(ev.vec().iter().take(1 << ev.num_vars).cloned().collect_vec(), l.into_vec(&split));
        }
    }

    #[test]
    fn split_rand_poly() {
        let rng = &mut test_rng();
        for _ in 0..100 {
            let shape = Shape::rand(rng, 10, 10);
            let split = shape.split();
            let p = Poly::new(
                (0..shape.data_len).map(|_| rng.next_u64() % 10).collect_vec(),
                (0..shape.consts_len).map(|_| rng.next_u64() % 10).collect_vec(),
            );
            let v = p.clone().into_vec(&shape);
            let el = v.iter().cloned().step_by(2).collect_vec();
            let er = v.iter().cloned().skip(1).step_by(2).collect_vec();
            let (l, r) = p.split_into_shape(&shape, &split);
            assert_eq!(el, l.into_vec(&split));
            assert_eq!(er, r.into_vec(&split));
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
                idx: 0,
                len: 9,
                content: Consts,
                start: 0,
            },
            Fragment {
                idx: 0,
                len: 2,
                content: Consts,
                start: 9,
            },
            Fragment {
                idx: 1,
                len: 1,
                content: Consts,
                start: 11,
            },
            Fragment {
                idx: 0,
                len: 1,
                content: Consts,
                start: 12,
            },
            Fragment {
                idx: 0,
                len: 7,
                content: Consts,
                start: 13,
            },
            Fragment {
                idx: 0,
                len: 3,
                content: Data,
                start: 20,
            },
            Fragment {
                idx: 0,
                len: 10,
                content: Consts,
                start: 23,
            },
            Fragment {
                idx: 3,
                len: 8,
                content: Data,
                start: 33,
            },
            Fragment {
                idx: 0,
                len: 23,
                content: Consts,
                start: 41,
            },
        ];

        let shape = Shape::new(s);
        let split = shape.split();
        let p = Poly::new(d, c);
        assert_eq!(v, p.clone().into_vec(&shape));
        let el = v.iter().cloned().step_by(2).collect_vec();
        let er = v.iter().cloned().skip(1).step_by(2).collect_vec();
        let (l, r) = p.split_into_shape(&shape, &split);
        assert_eq!(el, l.into_vec(&split));
        assert_eq!(er, r.into_vec(&split));
    }

    #[test]
    fn split_shape() {
        let s = Shape::new(vec![
            Fragment {
                idx: 0,
                len: 4,
                content: Data,
                start: 0,
            },
            Fragment {
                idx: 0,
                len: 4,
                content: Consts,
                start: 4,
            },
            Fragment {
                idx: 4,
                len: 6,
                content: Data,
                start: 8,
            },
            Fragment {
                idx: 1,
                len: 2,
                content: Consts,
                start: 14,
            },
            Fragment {
                idx: 2,
                len: 4,
                content: Consts,
                start: 16,
            },
            Fragment {
                idx: 10,
                len: 8,
                content: Data,
                start: 20,
            },
            Fragment {
                idx: 3,
                len: 4,
                content: Consts,
                start: 28,
            },
        ]);
        let l = s.split();
        let el =  Shape::new(vec![
            Fragment {
                idx: 0,
                len: 2,
                content: Data,
                start: 0,
            },
            Fragment {
                idx: 0,
                len: 2,
                content: Consts,
                start: 2,
            },
            Fragment {
                idx: 2,
                len: 4,
                content: Data,
                start: 4,
            },
            Fragment {
                idx: 2,
                len: 2,
                content: Consts,
                start: 8,
            },
            Fragment {
                idx: 6,
                len: 4,
                content: Data,
                start: 10,
            },
            Fragment {
                idx: 3,
                len: 2,
                content: Consts,
                start: 14,
            },
        ]);
        assert_eq!(l, el);
        let ll = l.split();
        let ell =  Shape::new(vec![
            Fragment {
                idx: 0,
                len: 8,
                content: Data,
                start: 0,
            },
        ]);
        assert_eq!(ll, ell);
    }
}