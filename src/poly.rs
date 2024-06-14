use std::cmp::min;
use std::fmt::Debug;
use std::io::repeat;
use ark_bls12_381::Fr;
use itertools::{Itertools, repeat_n};
use crate::poly::FragmentContent::{Consts, Data};

pub trait Split: Sized {
    fn split(&self) -> (Self, Self);
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum FragmentContent {
    Data,
    Consts,
}

#[derive(Debug, Clone, Eq, PartialEq)]
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

#[derive(Debug, Clone, Eq, PartialEq)]
struct Poly<F> {
    data: Vec<F>,
    // continuations: Vec<F>,
    shape: Vec<Fragment>,
}

impl<F> Default for Poly<F> {
    fn default() -> Self {
        Self {
            data: vec![],
            // continuations: vec![],
            shape: vec![],
        }
    }
}

impl<F: Eq + Clone> Extend<F> for Poly<F> {
    fn extend<T: IntoIterator<Item=F>>(&mut self, iter: T) {
        let mut iter = iter.into_iter();
        let Some(mut first) = iter.next() else { return; };
        let mut f = Fragment::new_of(Consts);
        f.idx = self.data.len();
        f.len = 1;
        f.start = self.shape.last().map_or(0, |l| l.start + l.len);
        for item in iter {
            if item != first {
                self.shape.push(f);
                self.data.push(first);
                optimise_tail(self);
                f = Fragment::new_of(Consts);
                f.idx = self.data.len();
                f.len = 1;
                f.start = self.shape.last().map_or(0, |l| l.start + l.len);
                first = item;
            } else {
                f.len += 1;
            }
        }
        self.shape.push(f);
        self.data.push(first);
        optimise_tail(self);
    }
}

impl<F: Eq + Clone> From<Vec<F>> for Poly<F> {
    fn from(value: Vec<F>) -> Self {
        let mut new = Self::default();
        new.extend(value.into_iter());
        new
    }
}

impl <F: Clone> Into<Vec<F>> for Poly<F> {
    fn into(self) -> Vec<F> {
        let mut out = vec![];
        for fragment in &self.shape {
            match fragment.content {
                Data => {
                    out.extend(self.data[fragment.idx..(fragment.idx + fragment.len)].iter().cloned());
                }
                Consts => {
                    out.extend(repeat_n(self.data[fragment.idx].clone(), fragment.len));
                }
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
fn merge_last_fragments<F: Clone>(poly: &mut Poly<F>) {
    let last = poly.shape.pop().unwrap();
    let prev = poly.shape.last_mut().unwrap();
    match (&prev.content, last.content) {
        (FragmentContent::Data, FragmentContent::Data) => {
            poly.data.pop().unwrap();
            prev.len += last.len;
        }
        (FragmentContent::Data, FragmentContent::Consts) => {
            for _ in 0..(last.len - 1) {
                poly.data.push(poly.data.last().unwrap().clone());
            }
            prev.len += last.len;
        }
        (FragmentContent::Consts, FragmentContent::Data) => {
            unreachable!()
        }
        (FragmentContent::Consts, FragmentContent::Consts) => {
            if prev.len == 1 && last.len == 1 {
                prev.content = Data;
            } else {
                poly.data.pop();
            }
            prev.len += last.len;
        }
    }
}


const const_merge_thresh: usize = 2;

fn should_merge<F: Eq>(poly: &Poly<F>, f1: &Fragment, f2: &Fragment) -> bool {
    match (&f1.content, &f2.content) {
        (FragmentContent::Data, FragmentContent::Data) => true,
        (FragmentContent::Data, FragmentContent::Consts) => {
            f2.len < const_merge_thresh
        },
        (FragmentContent::Consts, FragmentContent::Data) => false,
        (FragmentContent::Consts, FragmentContent::Consts) => {
            (poly.data[f1.idx] == poly.data[f2.idx]) || (f1.len == 1 && f2.len == 1)
        },
    }
}


fn optimise_tail<F: Clone + Eq>(poly: &mut Poly<F>) {
    while poly.shape.len() >= 2 && should_merge(&poly, &poly.shape[poly.shape.len() - 2], &poly.shape[poly.shape.len() - 1]) {
        merge_last_fragments(poly);
    }
    if poly.shape.len() > 0 && poly.shape.last().unwrap().len == 1 {
        poly.shape.last_mut().unwrap().content = Consts;
    }
}

impl<F: Clone + Eq> Split for Poly<F> {
    fn split(&self) -> (Self, Self) {
        let mut l = Self::default();
        let mut r = Self::default();

        for fragment in &self.shape {
            let mut l_frag = Fragment::new_of(fragment.content);
            let mut r_frag = Fragment::new_of(fragment.content);

            r_frag.start = fragment.start / 2;
            l_frag.start = fragment.start - r_frag.start;

            r_frag.len = fragment.len / 2;
            l_frag.len = fragment.len - r_frag.len;
            if fragment.start % 2 == 1 {
                (r_frag.len, l_frag.len) = (l_frag.len, r_frag.len)
            }

            match fragment.content {
                FragmentContent::Data => {
                    let (mut l_iter, mut r_iter) = self.data.iter().skip(fragment.idx).take(fragment.len).tee();
                    let (mut l_iter, mut r_iter) = if fragment.start % 2 == 1 {
                        (l_iter.skip(1).step_by(2), r_iter.skip(0).step_by(2))
                    } else {
                        (l_iter.skip(0).step_by(2), r_iter.skip(1).step_by(2))
                    };

                    if l_frag.len > 0 {
                        l_frag.idx = l.data.len();
                        l.data.extend(l_iter.cloned());
                    }
                    if r_frag.len > 0 {
                        r_frag.idx = r.data.len();
                        r.data.extend(r_iter.cloned());
                    }
                }
                FragmentContent::Consts => {
                    if l_frag.len > 0 {
                        l_frag.idx = l.data.len();
                        l.data.push(self.data[fragment.idx].clone());
                    }
                    if r_frag.len > 0 {
                        r_frag.idx = r.data.len();
                        r.data.push(self.data[fragment.idx].clone());
                    }
                }
            }

            if l_frag.len > 0 {
                l.shape.push(l_frag);
            }
            if r_frag.len > 0 {
                r.shape.push(r_frag);
            }
            optimise_tail(&mut l);
            optimise_tail(&mut r);
        }
        (l, r)
    }
}



#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use crate::poly::{Fragment, Poly, Split};
    use crate::poly::FragmentContent::{Consts, Data};


    #[test]
    fn from_vec() {
        let v = vec![
            1, 2, 3, 0,
            0, 0, 0, 4,
            5, 6, 7, 8,
            0, 0, 0, 9,
            0, 0, 0, 0,
            0, 0, 0, 0,
            1, 2, 2, 3,
            4, 4, 5, 5,
        ];
        let p = Poly::from(v.clone());
        let ep = Poly {
            data: vec![
                1, 2, 3, 0, 4, 5, 6, 7, 8, 0, 9, 0, 1, 2, 3, 4, 5,
            ],
            shape: vec![
                Fragment {
                    idx: 0,
                    len: 3,
                    content: Data,
                    start: 0,
                },
                Fragment {
                    idx: 3,
                    len: 4,
                    content: Consts,
                    start: 3,
                },
                Fragment {
                    idx: 4,
                    len: 5,
                    content: Data,
                    start: 7,
                },
                Fragment {
                    idx: 9,
                    len: 3,
                    content: Consts,
                    start: 12,
                },
                Fragment {
                    idx: 10,
                    len: 1,
                    content: Consts,
                    start: 15,
                },
                Fragment {
                    idx: 11,
                    len: 8,
                    content: Consts,
                    start: 16,
                },
                Fragment {
                    idx: 12,
                    len: 1,
                    content: Consts,
                    start: 24,
                },
                Fragment {
                    idx: 13,
                    len: 2,
                    content: Consts,
                    start: 25,
                },
                Fragment {
                    idx: 14,
                    len: 1,
                    content: Consts,
                    start: 27,
                },
                Fragment {
                    idx: 15,
                    len: 2,
                    content: Consts,
                    start: 28,
                },
                Fragment {
                    idx: 16,
                    len: 2,
                    content: Consts,
                    start: 30,
                },
            ],
        };
        assert_eq!(v, <Poly<i32> as Into<Vec<i32>>>::into(p.clone()));
        assert_eq!(p, ep);
    }

    #[test]
    fn split() {
        let v = vec![
            1, 2, 3, 0,
            0, 0, 0, 4,
            5, 6, 7, 8,
            0, 0, 0, 9,
            0, 0, 0, 0,
            0, 0, 0, 0,
            1, 2, 2, 3,
            4, 4, 5, 5,
        ];
        let (mut lvi,mut rvi) = v.iter().cloned().tee();
        let (lv, rv) = (lvi.step_by(2).collect_vec(), rvi.skip(1).step_by(2).collect_vec());
        let p = Poly::from(v);
        let el = Poly::from(lv);
        let er = Poly::from(rv);
        let (l, r) = p.split();
        assert_eq!(l, el);
        assert_eq!(r, er);
    }
}