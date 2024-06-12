use itertools::Itertools;

pub trait Split: Sized {
    fn split(&self) -> (Self, Self);
}


#[derive(Default, Debug, Clone, Eq, PartialEq)]
struct Fragment {
    data_idx: usize,
    data_len: usize,
    continuation_idx: usize,
    continuation_len: usize,
    start: usize,
}

type Shape = Vec<Fragment>;

impl Fragment {
    pub fn len(&self) -> usize {
        self.data_len + self.continuation_len
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct Poly<F> {
    data: Vec<F>,
    continuations: Vec<F>,
    shape: Shape,
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

#[derive(Debug, Clone, Eq, PartialEq)]
struct PolyRef<'a, 'b, F> {
    data: &'a Vec<F>,
    shape: &'b Shape,
}

impl<F: Clone> Split for Poly<F> {
    fn split(&self) -> (Self, Self) {
        let mut l = Self::default();
        let mut r = Self::default();
        let mut data_len_taken = 0;
        for fragment in &self.shape {
            if fragment.len() > 2 {
                let mut l_frag = Fragment::default();
                let mut r_frag = Fragment::default();
                l_frag.start = fragment.start / 2;
                r_frag.start = fragment.start / 2;

                r_frag.data_len = fragment.data_len / 2;
                l_frag.data_len = fragment.data_len - r_frag.data_len;

                l_frag.continuation_len = fragment.continuation_len / 2;
                r_frag.continuation_len = fragment.continuation_len - l_frag.continuation_len;

                { // THIS BLOCK IS ABSOLUTE BULLSHIT BUT RIGHT NOW IT IS A NECESSITY
                    if l_frag.continuation_len > 0 {
                        l.continuations.push(self.continuations[fragment.continuation_idx].clone());
                        l_frag.continuation_idx = l.continuations.len() - 1;
                    }
                    if r_frag.continuation_len > 0 {
                        r.continuations.push(self.continuations[fragment.continuation_idx].clone());
                        r_frag.continuation_idx = r.continuations.len() - 1;
                    }

                    l_frag.data_idx = l.data.len();
                    r_frag.data_idx = r.data.len();
                }
                let (mut l_iter, mut r_iter) = self.data.iter().skip(data_len_taken).take(fragment.data_len).tee();
                let (mut l_iter, mut r_iter) = (l_iter.step_by(2), r_iter.skip(1).step_by(2));

                data_len_taken += fragment.data_len;

                l.data.extend(l_iter.cloned());
                r.data.extend(r_iter.cloned());

                l.shape.push(l_frag);
                r.shape.push(r_frag);
            }
            else {
                todo!()
            }
        }
        (l, r)
    }
}



#[cfg(test)]
mod tests {
    use crate::poly::{Fragment, Poly, Split};

    #[test]
    fn split_poly() {
        let p = Poly {
            data: vec![
                1, 2, 3, // 0
                4, 5, // 1 1
                6, // 2 2 2 2 2 2 2
            ],
            continuations: vec![
                0,
                1,
                2
            ],
            shape: vec![
                Fragment {
                    data_idx: 0,
                    data_len: 3,
                    continuation_idx: 0,
                    continuation_len: 1,
                    start: 0,
                },
                Fragment {
                    data_idx: 3,
                    data_len: 2,
                    continuation_idx: 1,
                    continuation_len: 2,
                    start: 4,
                },
                Fragment {
                    data_idx: 5,
                    data_len: 1,
                    continuation_idx: 2,
                    continuation_len: 7,
                    start: 8,
                },
            ],
        };
        let (l, r) = p.split();
        assert_eq!(
            l,
            Poly {
                data: vec![
                    1, 3,
                    4, // 1
                    6, // 2 2 2
                ],
                continuations: vec![
                    // _
                    1,
                    2,
                ],
                shape: vec![
                    Fragment {
                        data_idx: 0,
                        data_len: 2,
                        continuation_idx: 0,
                        continuation_len: 0,
                        start: 0,
                    },
                    Fragment {
                        data_idx: 2,
                        data_len: 1,
                        continuation_idx: 0,
                        continuation_len: 1,
                        start: 2,
                    },
                    Fragment {
                        data_idx: 3,
                        data_len: 1,
                        continuation_idx: 1,
                        continuation_len: 3,
                        start: 4,
                    },
                ],
            }
        );
        assert_eq!(
            r,
            Poly {
                data: vec![
                    2, // 0
                    5, // 1
                    // 2, 2 2 2
                ],
                continuations: vec![
                    0,
                    1,
                    2,
                ],
                shape: vec![
                    Fragment {
                        data_idx: 0,
                        data_len: 1,
                        continuation_idx: 0,
                        continuation_len: 1,
                        start: 0,
                    },
                    Fragment {
                        data_idx: 1,
                        data_len: 1,
                        continuation_idx: 1,
                        continuation_len: 1,
                        start: 2,
                    },
                    Fragment {
                        data_idx: 2,
                        data_len: 0,
                        continuation_idx: 2,
                        continuation_len: 4,
                        start: 4,
                    },
                ],
            }
        )
    }
}