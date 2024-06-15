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
    continuations: Vec<F>,
    shape: Vec<Fragment>,
}

impl<F> Default for Poly<F> {
    fn default() -> Self {
        Self {
            data: vec![],
            continuations: vec![],
            shape: vec![],
        }
    }
}
//
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



#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use crate::poly::{Fragment, Poly, Split};
    use crate::poly::FragmentContent::{Consts, Data};


    #[test]
    // fn from_vec() {
    //     let v = vec![
    //         1, 2, 3, 0,
    //         0, 0, 0, 4,
    //         5, 6, 7, 8,
    //         0, 0, 0, 9,
    //         0, 0, 0, 0,
    //         0, 0, 0, 0,
    //         1, 2, 2, 3,
    //         4, 4, 5, 5,
    //     ];
    //     let p = Poly::from(v.clone());
    //     let ep = Poly {
    //         data: vec![
    //             1, 2, 3, 0, 4, 5, 6, 7, 8, 0, 9, 0, 1, 2, 3, 4, 5,
    //         ],
    //         shape: vec![
    //             Fragment {
    //                 idx: 0,
    //                 len: 3,
    //                 content: Data,
    //                 start: 0,
    //             },
    //             Fragment {
    //                 idx: 3,
    //                 len: 4,
    //                 content: Consts,
    //                 start: 3,
    //             },
    //             Fragment {
    //                 idx: 4,
    //                 len: 5,
    //                 content: Data,
    //                 start: 7,
    //             },
    //             Fragment {
    //                 idx: 9,
    //                 len: 3,
    //                 content: Consts,
    //                 start: 12,
    //             },
    //             Fragment {
    //                 idx: 10,
    //                 len: 1,
    //                 content: Consts,
    //                 start: 15,
    //             },
    //             Fragment {
    //                 idx: 11,
    //                 len: 8,
    //                 content: Consts,
    //                 start: 16,
    //             },
    //             Fragment {
    //                 idx: 12,
    //                 len: 1,
    //                 content: Consts,
    //                 start: 24,
    //             },
    //             Fragment {
    //                 idx: 13,
    //                 len: 2,
    //                 content: Consts,
    //                 start: 25,
    //             },
    //             Fragment {
    //                 idx: 14,
    //                 len: 1,
    //                 content: Consts,
    //                 start: 27,
    //             },
    //             Fragment {
    //                 idx: 15,
    //                 len: 2,
    //                 content: Consts,
    //                 start: 28,
    //             },
    //             Fragment {
    //                 idx: 16,
    //                 len: 2,
    //                 content: Consts,
    //                 start: 30,
    //             },
    //         ],
    //     };
    //     assert_eq!(v, <Poly<i32> as Into<Vec<i32>>>::into(p.clone()));
    //     assert_eq!(p, ep);
    // }

    // #[test]
    // fn split() {
    //     let v = vec![
    //         1, 2, 3, 0,
    //         0, 0, 0, 4,
    //         5, 6, 7, 8,
    //         0, 0, 0, 9,
    //         0, 0, 0, 0,
    //         0, 0, 0, 0,
    //         1, 2, 2, 3,
    //         4, 4, 5, 5,
    //     ];
    //     let (mut lvi,mut rvi) = v.iter().cloned().tee();
    //     let (lv, rv) = (lvi.step_by(2).collect_vec(), rvi.skip(1).step_by(2).collect_vec());
    //     let p = Poly::from(v);
    //     let el = Poly::from(lv);
    //     let er = Poly::from(rv);
    //     let (l, r) = p.split();
    //     assert_eq!(l, el);
    //     assert_eq!(r, er);
    // }

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