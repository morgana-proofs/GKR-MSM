use std::cmp::max;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
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
pub struct Shape {
    pub shape: Vec<Fragment>,
    pub data_len: usize,
    pub consts_len: usize,
    
    pub split: Arc<OnceLock<Shape>>
}

/// Merges last and one before last fragments of given poly
/// Assumes that they can be merged and are correct
fn merge_last_fragments(shape: &mut Vec<Fragment>, last: Fragment) {
    let prev = shape.last_mut().unwrap();
    match (&prev.content, last.content) {
        (Data, Data) => {
            prev.len += last.len;
        }
        (Data, Consts) => {
            prev.len += last.len;
        }
        (Consts, Data) => {
            unreachable!()
        }
        (Consts, Consts) => {
            prev.len += last.len;
        }
    }
}

const const_merge_thresh: usize = 2;

fn should_merge(f1: &Fragment, f2: &Fragment) -> bool {
    match (&f1.content, &f2.content) {
        (Data, Data) => true,
        (Data, Consts) => {
            f2.len < const_merge_thresh
        },
        (Consts, Data) => false,
        (Consts, Consts) => {
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
                if should_merge(&prev, &fragment) {
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

impl Shape {
    pub fn split(&self) -> &Self {
        self.split.get_or_init(|| {
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
                                content: Data,
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
        todo!()
    }

    pub fn evaluate(&self, r: &F) -> F {
        todo!()
    }

    fn get_by_fragment(&self, frag: &Fragment, idx: usize) -> &F {
        match frag.content {
            Data => &self.data[frag.idx + idx],
            Consts => &self.consts[frag.idx],
        }
    }
}

impl<F: From<u64>> FragmentedPoly<F> {
    pub fn rand<RNG: Rng>(rng: &mut RNG, frag_size: usize, frags: usize) -> Self {
        let shape = Arc::new(OnceLock::new());
        let s = shape.get_or_init(|| Shape::rand(rng, frag_size, frags));
        Self {
            data: (0..s.data_len).map(|_| F::from(rng.next_u64())).collect_vec(),
            consts: (0..s.consts_len).map(|_| F::from(rng.next_u64())).collect_vec(),
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
        let last_target = target.shape.last().unwrap();
        let data_size = last_target.idx + match last_target.content {
            Data => last_target.len,
            Consts => 1,
        };
        let (mut l, mut r) = (Self::new(Vec::with_capacity(data_size), self.consts.clone(), split_shape.clone()), Self::new(Vec::with_capacity(data_size), self.consts.clone(), split_shape));

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

impl<F: AddAssign + Mul<Output=F> + Sub<Output=F> + Send + Sync + Sized + Copy> FragmentedPoly<F> {
    pub fn bind(&self, f: &F) -> Self {
        let (mut l, r) = self.split();
        l.data.par_iter_mut()
            .chain(l.consts.par_iter_mut())
            .zip(r.data.par_iter().chain(r.consts.par_iter()))
            .map(|(l, r)| { *l += *f * (*r - *l) }).count();
        l
    }
}

impl <F: Clone> FragmentedPoly<F> {
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


#[cfg(test)]
mod tests {
    use std::cell::OnceCell;
    use std::sync::{Arc, OnceLock, RwLock, RwLockWriteGuard, TryLockError, TryLockResult};
    use ark_ed_on_bls12_381_bandersnatch::Fr;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;
    use itertools::Itertools;
    use liblasso::poly::dense_mlpoly::DensePolynomial;
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
                (0..shape.consts_len).map(|_| Fr::from(rng.next_u64())).collect_vec(),
                shape_cell,
            );
            let v = p.clone().into_vec(&shape);
            let mut ev = DensePolynomial::new(v.clone());
            let f = Fr::from(rng.next_u64());
            ev.bound_poly_var_bot(&f);
            let el = v.iter().cloned().step_by(2).collect_vec();
            let er = v.iter().cloned().skip(1).step_by(2).collect_vec();

            let l = p.bind(&f);

            assert_eq!(ev.vec().iter().take(1 << ev.num_vars).cloned().collect_vec(), l.into_vec(&split));
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
                (0..shape.consts_len).map(|_| rng.next_u64() % 10).collect_vec(),
                shape_cell,
            );
            let v = p.clone().into_vec(&shape);
            let el = v.iter().cloned().step_by(2).collect_vec();
            let er = v.iter().cloned().skip(1).step_by(2).collect_vec();
            let (l, r) = p.split();
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
        let shape_cell = Arc::new(OnceLock::new());
        shape_cell.set(shape.clone()).unwrap();
        let split = shape.split();
        let p = FragmentedPoly::new(d, c, shape_cell);
        assert_eq!(v, p.clone().into_vec(&shape));
        let el = v.iter().cloned().step_by(2).collect_vec();
        let er = v.iter().cloned().skip(1).step_by(2).collect_vec();
        let (l, r) = p.split();
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
        assert_eq!(l, &el);
        let ll = l.split();
        let ell =  Shape::new(vec![
            Fragment {
                idx: 0,
                len: 8,
                content: Data,
                start: 0,
            },
        ]);
        assert_eq!(ll, &ell);
    }
    
    #[test]
    fn onceLock() {
        let x = OnceLock::new();
        fn initialize(x: &OnceLock<usize>, marker: usize) {
            x.get_or_init(|| {
                println!("initializing in {}", marker);
                marker
            });
            println!("in {}: {:?}", marker, x.get())
        }

        rayon::scope(|s| {
            s.spawn(|_| initialize(&x, 0));
            s.spawn(|_| initialize(&x, 1));
            s.spawn(|_| initialize(&x, 2));
            s.spawn(|_| initialize(&x, 3));
            s.spawn(|_| initialize(&x, 4));
            s.spawn(|_| initialize(&x, 5));
        });
        println!("{:?}", x.get())
    }
}