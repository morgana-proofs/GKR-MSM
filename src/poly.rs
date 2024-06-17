use std::cmp::min;
use std::fmt::Debug;
use std::io::repeat;
use std::sync::Arc;
use ark_bls12_381::Fr;
use ark_std::iterable::Iterable;
use itertools::{Either, Itertools, repeat_n};
use crate::poly::FragmentContent::{Consts, Data};

pub trait Split: Sized {
    fn split(&self) -> (Self, Self);
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum FragmentContent {
    Data,
    Consts,
}

#[derive(Debug, Clone, Eq, PartialEq)]
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



#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Shape {
    shape: Vec<Fragment>,
    splits: Option<Arc<Shape>>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Poly<F> {
    data: Vec<F>,
    shape: Arc<Shape>,
}

impl<F> Poly<F> {
    pub fn new(data: Vec<F>, shape: Arc<Shape>) -> Self {
        Self {
            data,
            shape,
        }
    }

    fn get_by_fragment(&self, frag: &Fragment, idx: usize) -> &F {
        match frag.content {
            Data => &self.data[frag.idx + idx],
            Consts => &self.data[frag.idx],
        }
    }
}

impl<F: Clone> Poly<F> {
    fn split_into_shape(&self, target: &Arc<Shape>) -> (Self, Self) {
        let last_target = target.shape.last().unwrap();
        let data_size = last_target.idx + match last_target.content {
            Data => last_target.len,
            Consts => 1,
        };
        let (mut l, mut r) = (Self::new(Vec::with_capacity(data_size), target.clone()), Self::new(Vec::with_capacity(data_size), target.clone()));

        let mut self_iter = self.shape.shape.iter();
        let mut target_iter = target.shape.iter();

        let mut self_frag = self_iter.next();
        let mut self_frag_counter = 0;
        for target_frag in target_iter {
            match &target_frag.content {
                Data => {
                    for _ in 0..target_frag.len {
                        l.data.push(self.get_by_fragment(self_frag.unwrap(), self_frag_counter).clone());
                        self_frag_counter += 1;
                        r.data.push(self.get_by_fragment(self_frag.unwrap(), self_frag_counter).clone());
                        self_frag_counter += 1;

                        if self_frag_counter >= self_frag.unwrap().len {
                            self_frag = self_iter.next();
                            self_frag_counter = 0;
                        }
                    }
                }
                Consts => {
                    l.data.push(self.get_by_fragment(self_frag.unwrap(), self_frag_counter).clone());
                    r.data.push(self.get_by_fragment(self_frag.unwrap(), self_frag_counter).clone());
                    self_frag_counter += target_frag.len * 2;

                    if self_frag_counter >= self_frag.unwrap().len {
                        self_frag = self_iter.next();
                        self_frag_counter = 0;
                    }
                }
            }
        }

        (l, r)
    }
}

impl<F: Clone> Split for Poly<F> {
    fn split(&self) -> (Self, Self) {
        let Some(split) = &self.shape.splits else { panic!() };
        self.split_into_shape(split)
    }
}

// impl<F: Eq + Clone> Extend<F> for Poly<F> {
//     fn extend<T: IntoIterator<Item=F>>(&mut self, iter: T) {
//         let mut iter = iter.into_iter();
//         let Some(mut first) = iter.next() else { return; };
//         let mut f = Fragment::new_of(Consts);
//         f.idx = self.data.len();
//         f.len = 1;
//         f.start = self.shape.last().map_or(0, |l| l.start + l.len);
//         for item in iter {
//             if item != first {
//                 self.shape.push(f);
//                 self.data.push(first);
//                 optimise_tail(self);
//                 f = Fragment::new_of(Consts);
//                 f.idx = self.data.len();
//                 f.len = 1;
//                 f.start = self.shape.last().map_or(0, |l| l.start + l.len);
//                 first = item;
//             } else {
//                 f.len += 1;
//             }
//         }
//         self.shape.push(f);
//         self.data.push(first);
//         optimise_tail(self);
//     }
// }
//
// impl<F: Eq + Clone> From<Vec<F>> for Poly<F> {
//     fn from(value: Vec<F>) -> Self {
//         let mut new = Self::default();
//         new.extend(value.into_iter());
//         new
//     }
// }

impl <F: Clone> Into<Vec<F>> for Poly<F> {
    fn into(self) -> Vec<F> {
        let mut out = vec![];
        for fragment in &self.shape.shape {
            for idx in 0..fragment.len {
                out.push(self.get_by_fragment(fragment, idx).clone());
            }
        }
        out
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct PolyRef<'a, 'b, F> {
    data: &'a Vec<F>,
    shape: &'b Vec<Fragment>,
}


/// Merges last and one before last fragments of given poly
/// Assumes that they can be merged and are correct
fn merge_last_fragments(shape: &mut Vec<Fragment>) {
    let last = shape.pop().unwrap();
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
            unreachable!()
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
        (FragmentContent::Consts, FragmentContent::Consts) => false,
    }
}


fn optimise_tail(shape: &mut Vec<Fragment>) {
    while shape.len() >= 2 && should_merge(shape, &shape[shape.len() - 2], &shape[shape.len() - 1]) {
        merge_last_fragments(shape);
    }
}

impl Split for Vec<Fragment> {
    fn split(&self) -> (Self, Self) {
        let mut l = Self::default();
        let mut r = Self::default();

        let mut data_idx = 0;

        let mut stealing: Option<(Fragment, Fragment)> = None;

        for fragment in self {
            let Fragment { mut idx, mut len, content, mut start } = fragment;
            assert_eq!(len % 2, 0);
            let mut l_frag = Fragment::new_of(*content);
            let mut r_frag = Fragment::new_of(*content);

            if let Some((mut ls_frag, mut rs_frag)) = stealing.take() {
                match content {
                    Data => {
                        len += 2;
                        l_frag = ls_frag;
                        r_frag = rs_frag;
                    }
                    Consts => {
                        ls_frag.idx = data_idx;
                        rs_frag.idx = data_idx;
                        ls_frag.len = 2;
                        rs_frag.len = 2;
                        data_idx += 2;
                        l.push(ls_frag);
                        optimise_tail(&mut l);
                        r.push(rs_frag);
                        optimise_tail(&mut r);
                        len -= 2;
                    }
                }
            }

            if len == 0 {
                continue;
            }

            r_frag.start = start / 2;
            l_frag.start = start / 2;

            r_frag.len = len / 2;
            l_frag.len = len / 2;

            if (len / 2) % 2 == 1 {
                r_frag.len -= 1;
                l_frag.len -= 1;
                stealing = Some((
                    Fragment::new_of(Data),
                    Fragment::new_of(Data)
                ));
            }

            match content {
                Data => {
                    l_frag.idx = data_idx;
                    r_frag.idx = data_idx;
                    data_idx += l_frag.len;
                }
                Consts => {
                    l_frag.idx = data_idx;
                    r_frag.idx = data_idx;
                    data_idx += 1;
                }
            }
            if l_frag.len > 0 {
                l.push(l_frag);
                optimise_tail(&mut l);
                r.push(r_frag);
                optimise_tail(&mut r);
            }
        }
        if let Some((mut ls, mut rs)) = stealing {
            assert_eq!(data_idx, 0);
            rs.len = 1;
            ls.len = 1;

            l.push(ls);
            r.push(rs);
        }
        (l, r)
    }
}


impl Shape {
    pub fn split(&mut self) {
        match &mut self.splits {
            None => {
                self.splits = Some(Arc::new(Shape { shape: self.shape.split().0, splits: None }))
            }
            _ => {}
        }
    }
}


#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use itertools::Itertools;
    use crate::poly::{Fragment, Poly, Shape, Split};
    use crate::poly::FragmentContent::{Consts, Data};

    #[test]
    fn split_poly() {
        let v = vec![
            1, 2, 3, 4,
            0, 0, 0, 0,
            1, 2, 3, 4, 5, 6,
            0, 0,
            9, 9, 9, 9,
            1, 2, 3, 4, 5, 6, 7, 8,
            0, 0, 0, 0,
        ];
        let d = vec![
            1, 2, 3, 4,
            0,
            1, 2, 3, 4, 5, 6,
            0,
            9,
            1, 2, 3, 4, 5, 6, 7, 8,
            0,
        ];
        let s = vec![
            Fragment {
                idx: 0,
                len: 4,
                content: Data,
                start: 0,
            },
            Fragment {
                idx: 4,
                len: 4,
                content: Consts,
                start: 4,
            },
            Fragment {
                idx: 5,
                len: 6,
                content: Data,
                start: 8,
            },
            Fragment {
                idx: 11,
                len: 2,
                content: Consts,
                start: 14,
            },
            Fragment {
                idx: 12,
                len: 4,
                content: Consts,
                start: 16,
            },
            Fragment {
                idx: 13,
                len: 8,
                content: Data,
                start: 20,
            },
            Fragment {
                idx: 21,
                len: 4,
                content: Consts,
                start: 28,
            },
        ];

        let mut shape = Shape { shape: s, splits: None };
        shape.split();
        let p = Poly::new(d, Arc::new(shape).clone());
        assert_eq!(v, <Poly<i32> as Into<Vec<i32>>>::into(p.clone()));
        let el = v.iter().cloned().step_by(2).collect_vec();
        let er = v.iter().cloned().skip(1).step_by(2).collect_vec();
        let (l, r) = p.split();
        assert_eq!(el, <Poly<i32> as Into<Vec<i32>>>::into(l.clone()));
        assert_eq!(er, <Poly<i32> as Into<Vec<i32>>>::into(r.clone()));
    }

    #[test]
    fn split_shape() {
        let s = vec![
            Fragment {
                idx: 0,
                len: 4,
                content: Data,
                start: 0,
            },
            Fragment {
                idx: 4,
                len: 4,
                content: Consts,
                start: 4,
            },
            Fragment {
                idx: 5,
                len: 6,
                content: Data,
                start: 8,
            },
            Fragment {
                idx: 11,
                len: 2,
                content: Consts,
                start: 14,
            },
            Fragment {
                idx: 12,
                len: 4,
                content: Consts,
                start: 16,
            },
            Fragment {
                idx: 13,
                len: 8,
                content: Data,
                start: 20,
            },
            Fragment {
                idx: 21,
                len: 4,
                content: Consts,
                start: 28,
            },
        ];
        let (l, r) = s.split();
        assert_eq!(l, r);
        let es =  vec![
            Fragment {
                idx: 0,
                len: 2,
                content: Data,
                start: 0,
            },
            Fragment {
                idx: 2,
                len: 2,
                content: Consts,
                start: 2,
            },
            Fragment {
                idx: 3,
                len: 4,
                content: Data,
                start: 4,
            },
            Fragment {
                idx: 7,
                len: 2,
                content: Consts,
                start: 8,
            },
            Fragment {
                idx: 8,
                len: 4,
                content: Data,
                start: 10,
            },
            Fragment {
                idx: 12,
                len: 2,
                content: Consts,
                start: 14,
            },
        ];
        assert_eq!(l, es);
        let (ll, lr) = l.split();
        assert_eq!(ll, lr);
        let (lll, llr) = ll.split();
        assert_eq!(lll, llr);
        let (llll, lllr) = lll.split();
        assert_eq!(llll, lllr);
        let (lllll, llllr) = llll.split();
        assert_eq!(lllll, llllr);
    }
}