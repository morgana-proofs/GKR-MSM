use std::io;
use std::iter::FromIterator;
use std::iter::{once, repeat};
use std::cmp;
use std::ops::Index;
use ark_ff::Field;


#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct RleVec<T> {
    runs: Vec<InnerRun<T>>,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct InnerRun<F> {
    pub start: usize,
    pub len: usize,
    pub value: F,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Run<F> {
    pub len: usize,
    pub value: F,
}

impl <F> InnerRun<F> {
    pub fn end(&self) -> usize {
        self.start + self.len - 1
    }
}

impl<F> RleVec<F> {
    pub fn new() -> RleVec<F> {
        RleVec { runs: Vec::new() }
    }

    pub fn with_capacity(capacity: usize) -> RleVec<F> {
        RleVec { runs: Vec::with_capacity(capacity) }
    }

    pub fn len(&self) -> usize {
        match self.runs.last() {
            Some(run) => run.start + run.len,
            None => 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.runs.is_empty()
    }

    pub fn clear(&mut self) {
        self.runs.clear()
    }

    pub fn last(&self) -> Option<&F> {
        match self.runs.last() {
            Some(last) => Some(&last.value),
            None => None,
        }
    }

    pub fn last_run(&self) -> Option<&InnerRun<F>> {
        self.runs.last()
    }

    pub fn runs_len(&self) -> usize {
        self.runs.len()
    }

    pub fn starts(&self) -> Vec<usize> {
        if self.is_empty() { return Vec::new() }
        once(0).chain(self.runs.iter().take(self.runs_len() - 1).map(|r| r.end() + 1)).collect()
    }

    pub fn ends(&self) -> Vec<usize> {
        self.runs.iter().map(|r| r.end()).collect()
    }

    pub fn iter(&self) -> Iter<F> {
        Iter {
            rle: self,
            run_index: 0,
            index: 0,
            run_index_back: self.runs.len().saturating_sub(1),
            index_back: self.len(), // starts out of range
        }
    }

    pub fn runs(&self) -> Runs<F> {
        Runs { rle: self, run_index: 0 }
    }

    fn run_index(&self, index: usize) -> usize {
        match self.runs.binary_search_by(|run| run.end().cmp(&index)) {
            Ok(i) => i,
            Err(i) if i < self.runs.len() => i,
            _ => panic!("index out of bounds: the len is {} but the index is {}", self.len(), index)
        }
    }

    fn index_info(&self, index: usize) -> (usize, usize, usize) {
        match self.run_index(index) {
            0 => (0, self.runs[0].start, self.runs[0].end()),
            index => (index, self.runs[index].start, self.runs[index].end()),
        }
    }
}

impl<F: Eq> RleVec<F> {
    #[inline]
    pub fn push(&mut self, value: F) {
        self.push_n(1, value);
    }

    pub fn push_n(&mut self, n: usize, value: F) {
        if n == 0 { return; }

        let start = match self.runs.last_mut() {
            Some(ref mut last) if last.value == value => return last.len += n,
            Some(last) => last.end() + 1,
            None => 0,
        };

        self.runs.push(InnerRun { value, start, len: n });
    }
}

impl<F: Clone> RleVec<F> {
    pub fn to_vec(&self) -> Vec<F> {
        let mut res = Vec::with_capacity(self.len());
        let mut p = 0;
        for r in &self.runs {
            let n = r.end() - p + 1;
            res.extend(repeat(r.value.clone()).take(n));
            p += n;
        }
        res
    }
}

impl<F> RleVec<F> {
    pub fn set_by_global_idx(&mut self, index: usize, value: F) {
        let p = self.run_index(index);
        self.runs[p].value = value
    }

    pub fn set_by_run_idx(&mut self, index: usize, value: F) {
        self.runs[index].value = value
    }
}

impl<F> RleVec<F> {
    pub fn get_by_global_idx(&self, index: usize) -> &F {
        let p = self.run_index(index);
        &self.runs[p].value
    }

    pub fn get_by_run_idx(&self, index: usize) -> &F {
        &self.runs[index].value
    }
}

impl<F: Clone> Into<Vec<F>> for RleVec<F> {
    fn into(self) -> Vec<F> {
        self.to_vec()
    }
}

impl<'a, F: Eq + Clone> From<&'a [F]> for RleVec<F> {
    fn from(slice: &'a [F]) -> Self {
        let mut r = RleVec::new();
        r.extend(slice.iter().map(|x| x.clone()));
        r
    }
}

impl<F: Eq> FromIterator<F> for RleVec<F> {
    fn from_iter<I>(iter: I) -> Self where I: IntoIterator<Item=F> {
        let mut rle = RleVec::new();
        rle.extend(iter);
        rle
    }
}

impl<F: Eq> FromIterator<InnerRun<F>> for RleVec<F> {
    fn from_iter<I>(iter: I) -> Self where I: IntoIterator<Item=InnerRun<F>> {
        let iter = iter.into_iter();
        let (lower, _) = iter.size_hint();

        let mut rle = RleVec::with_capacity(lower);
        rle.extend(iter);
        rle
    }
}

impl<F> Default for RleVec<F> {
    fn default() -> Self {
        RleVec::new()
    }
}

impl<F: Eq> Extend<F> for RleVec<F> {
    fn extend<I>(&mut self, iter: I) where I: IntoIterator<Item=F> {
        let mut iter = iter.into_iter();

        let mut last_run = None;
        for v in iter {
            match &mut last_run {
                None => {
                    last_run = Some(InnerRun {
                        start: 0,
                        len: 1,
                        value: v,
                    });
                },
                Some(run) => {
                    if v == run.value {
                        run.len += 1;
                    } else {
                        let next_start = run.start + run.len;
                        self.runs.push(last_run.take().unwrap());
                        last_run = Some(InnerRun {
                            start: next_start,
                            len: 1,
                            value: v,
                        })
                    }
                }
            }
        }
        match last_run {
            None => {}
            Some(run) => {
                self.runs.push(run);
            }
        }
    }
}

impl<F: Eq> Extend<InnerRun<F>> for RleVec<F> {
    fn extend<I>(&mut self, iter: I) where I: IntoIterator<Item=InnerRun<F>> {
        for InnerRun { len, value , .. } in iter {
            self.push_n(len, value)
        }
    }
}

impl<F: Eq> Extend<Run<F>> for RleVec<F> {
    fn extend<I>(&mut self, iter: I) where I: IntoIterator<Item=Run<F>> {
        for Run { len, value } in iter {
            self.push_n(len, value)
        }
    }
}

impl<F: Field> RleVec<F> {
    pub fn bound_var_bot(&mut self, r: &F) {
        self.bind_least_significant_var(r);
    }
    pub fn bind_least_significant_var(&mut self, r: &F) {
        
    }
}

pub struct Iter<'a, F: 'a> {
    rle: &'a RleVec<F>,
    run_index: usize,
    index: usize,
    index_back: usize,
    run_index_back: usize,
}

impl<'a, F: 'a> IntoIterator for &'a RleVec<F> {
    type Item = &'a F;
    type IntoIter = Iter<'a, F>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            rle: self,
            run_index: 0,
            index: 0,
            run_index_back: self.runs.len().saturating_sub(1),
            index_back: self.len(), // starts out of range
        }
    }
}

impl<'a, F: 'a> Iterator for Iter<'a, F> {
    type Item = &'a F;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index == self.index_back {
            return None
        }
        let run = &self.rle.runs[self.run_index];
        self.index += 1;
        if self.index > run.end() {
            self.run_index += 1;
        }
        Some(&run.value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.rle.len() - self.index;
        (len, Some(len))
    }

    fn count(self) -> usize {
        // thanks to the ExactSizeIterator impl
        self.len()
    }

    fn last(self) -> Option<Self::Item> {
        if self.index == self.rle.len() {
            return None
        }
        self.rle.last()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.index = cmp::min(self.index + n, self.rle.len());
        self.run_index = if self.index < self.rle.len() {
            self.rle.run_index(self.index)
        } else {
            self.rle.runs.len() - 1
        };
        self.next()
    }
}

impl<'a, F: 'a> ExactSizeIterator for Iter<'a, F> { }

impl<'a, F: 'a> DoubleEndedIterator for Iter<'a, F> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index_back == self.index {
            return None
        }
        self.index_back -= 1;
        if self.run_index_back > 0 && self.index_back <= self.rle.runs[self.run_index_back - 1].end() {
            self.run_index_back -= 1;
        }
        Some(&self.rle.runs[self.run_index_back].value)
    }
}

pub struct Runs<'a, F:'a> {
    rle: &'a RleVec<F>,
    run_index: usize,
}

impl<'a, F: 'a> Iterator for Runs<'a, F> {
    type Item = &'a InnerRun<F>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.run_index == self.rle.runs.len() {
            return None
        }
        let run = self.rle.runs.index(self.run_index);
        self.run_index += 1;
        Some(&run)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.rle.runs.len() - self.run_index;
        (len, Some(len))
    }

    fn count(self) -> usize {
        // thanks to the ExactSizeIterator impl
        self.len()
    }

    fn last(self) -> Option<Self::Item> {
        if self.run_index == self.rle.runs.len() {
            return None
        }
        self.rle.last_run()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.run_index = cmp::min(self.run_index + n, self.rle.runs.len());
        self.next()
    }
}

impl<'a, F: 'a> ExactSizeIterator for Runs<'a, F> { }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rare_usage() {
        // from slice

        let rle: RleVec<i32> = RleVec::from(&[][..]);
        assert_eq!(rle.to_vec(), vec![]);
        let runs: Vec<_> = rle.runs().collect();
        assert_eq!(runs, vec![] as Vec<&InnerRun<i32>>);

        let rle: RleVec<i32> = RleVec::from(&[1][..]);
        assert_eq!(rle.to_vec(), vec![1]);
        let runs: Vec<_> = rle.runs().collect();
        assert_eq!(runs, vec![&InnerRun { start: 0, len: 1, value: 1 }]);

        let rle: RleVec<i32> = RleVec::from(&[1, 2][..]);
        assert_eq!(rle.to_vec(), vec![1, 2]);
        let runs: Vec<_> = rle.runs().collect();
        assert_eq!(runs, vec![&InnerRun { start: 0, len: 1, value: 1 }, &InnerRun { start: 1, len: 1, value: 2 }]);

        let rle: RleVec<i32> = RleVec::from(&[1, 1][..]);
        assert_eq!(rle.to_vec(), vec![1, 1]);
        let runs: Vec<_> = rle.runs().collect();
        assert_eq!(runs, vec![&InnerRun { start: 0, len: 2, value: 1 }]);

        // from iter

        let rle: RleVec<i32> = RleVec::from_iter(0..0);
        assert_eq!(rle.to_vec(), vec![]);
        let runs: Vec<_> = rle.runs().collect();
        assert_eq!(runs, vec![] as Vec<&InnerRun<i32>>);

        let rle: RleVec<i32> = RleVec::from_iter(1..2);
        assert_eq!(rle.to_vec(), vec![1]);
        let runs: Vec<_> = rle.runs().collect();
        assert_eq!(runs, vec![&InnerRun { start: 0, len: 1, value: 1 }]);

        let rle: RleVec<i32> = RleVec::from_iter(1..3);
        assert_eq!(rle.to_vec(), vec![1, 2]);
        let runs: Vec<_> = rle.runs().collect();
        assert_eq!(runs, vec![&InnerRun { start: 0, len: 1, value: 1 }, &InnerRun { start: 1, len: 1, value: 2 }]);

        use std::iter::repeat;
        let rle: RleVec<i32> = RleVec::from_iter(repeat(1).take(2));
        assert_eq!(rle.to_vec(), vec![1, 1]);
        let runs: Vec<_> = rle.runs().collect();
        assert_eq!(runs, vec![&InnerRun { start: 0, len: 2, value: 1 }]);
    }

    #[test]
    fn basic_usage() {
        let mut rle = RleVec::<i64>::new();
        rle.push(1);
        rle.push(1);
        rle.push(1);
        rle.push(1);
        rle.push(2);
        rle.push(2);
        rle.push(2);
        rle.push(3);
        rle.push(3);
        rle.push(4);
        assert_eq!(rle.len(), 10);
        assert_eq!(rle.runs_len(), 4);

        rle.push_n(3, 4);
        assert_eq!(rle.len(), 13);
        assert_eq!(rle.runs_len(), 4);
        assert_eq!(rle.last(), Some(&4));
        rle.push_n(3, 5);
        assert_eq!(rle.len(), 16);
        assert_eq!(rle.runs_len(), 5);
        assert_eq!(rle.last(), Some(&5));
        assert_eq!(rle.last_run(), Some(&InnerRun {start: 13, value: 5, len: 3}));
        rle.clear();
        assert_eq!(rle.len(), 0);
        assert_eq!(rle.runs_len(), 0);
        assert_eq!(rle.last(), None);
        assert_eq!(rle.last_run(), None);

        let mut rle = RleVec::default();
        rle.push(1);
        assert_eq!(rle.len(), 1);
    }

    #[test]
    fn from_slice() {
        let v = vec![0,0,0,1,1,1,1,1,1,1,3,3,1,0,99,99,9];
        let rle = RleVec::from(&v[..]);
        assert_eq!((0..v.len()).map(|i| *rle.get_by_global_idx(i)).collect::<Vec<_>>(), v);
        assert_eq!(rle.len(),17);

        let v2: Vec<_> = rle.into();
        assert_eq!(v2,v);
    }

    #[test]
    fn iterators() {
        let v = vec![0,0,0,1,1,1,1,1,1,1,3,3,123,0,90,90,99];
        let rle = v.iter().cloned().collect::<RleVec<_>>();
        assert_eq!((0..v.len()).map(|i| *rle.get_by_global_idx(i)).collect::<Vec<_>>(), v);
        assert_eq!(rle.len(), v.len());

        assert_eq!(rle.iter().cloned().collect::<Vec<_>>(), v);
        assert_eq!(RleVec::<i64>::new().iter().next(), None);

        let v2 = (0..100).collect::<Vec<usize>>();
        let rle2 = v2.iter().cloned().collect::<RleVec<_>>();
        assert_eq!(rle2.iter().cloned().collect::<Vec<_>>(), v2);
        assert_eq!(rle2.iter().skip(0).cloned().collect::<Vec<_>>(), v2);

        assert_eq!(rle2.iter().nth(0), Some(&0));
        assert_eq!(rle2.iter().nth(5), Some(&5));
        assert_eq!(rle2.iter().nth(99), Some(&99));
        assert_eq!(rle2.iter().nth(100), None);
        let mut it = rle2.iter();
        it.nth(0);
        assert_eq!(it.nth(0), Some(&1));

        assert_eq!(rle.iter().nth(3), Some(&1));
        assert_eq!(rle.iter().nth(14), Some(&90));
        assert_eq!(rle.iter().nth(15), Some(&90));

        assert_eq!(rle.iter().skip(2).next(), Some(&0));
        assert_eq!(rle.iter().skip(3).next(), Some(&1));

        assert_eq!(rle.iter().max(), Some(&123));
        assert_eq!(rle.iter().min(), Some(&0));
        assert_eq!(rle.iter().skip(13).max(), Some(&99));
        assert_eq!(rle.iter().skip(13).min(), Some(&0));
        assert_eq!(rle.iter().skip(13).take(2).max(), Some(&90));
        assert_eq!(rle.iter().skip(13).take(2).min(), Some(&0));

        assert_eq!(rle.iter().count(), 17);
        assert_eq!(rle.iter().skip(10).last(), Some(&99));
        assert_eq!(rle.iter().skip(30).last(), None);

        //runiters
        assert_eq!(rle.runs().map(|r| r.value).collect::<Vec<_>>(), vec![0,1,3,123,0,90,99]);
        assert_eq!(rle.runs().map(|r| r.len).collect::<Vec<_>>(), vec![3,7,2,1,1,2,1]);

        let mut copy = RleVec::new();
        for r in rle.runs() {
            copy.push_n(r.len, r.value.clone());
        }
        assert_eq!(copy.iter().cloned().collect::<Vec<_>>(), v);
        let copy2: RleVec<i32> = rle.runs().map(|r| InnerRun { start: r.start, value: r.value.clone(), len: r.len }).collect();
        assert_eq!(copy2.iter().cloned().collect::<Vec<_>>(), v);
    }

    #[test]
    fn back_iterators() {
        let rle = RleVec::from(&[0,1,1,3,3,9,99][..]);

        // only next_back()
        let mut iter = rle.iter();
        assert_eq!(iter.next_back(), Some(&99));
        assert_eq!(iter.next_back(), Some(&9));
        assert_eq!(iter.next_back(), Some(&3));
        assert_eq!(iter.next_back(), Some(&3));
        assert_eq!(iter.next_back(), Some(&1));
        assert_eq!(iter.next_back(), Some(&1));
        assert_eq!(iter.next_back(), Some(&0));
        assert_eq!(iter.next_back(), None);

        // next_back() combine with next()
        let mut iter = rle.iter();
        assert_eq!(iter.next_back(), Some(&99));
        assert_eq!(iter.next(),      Some(&0));
        assert_eq!(iter.next(),      Some(&1));
        assert_eq!(iter.next_back(), Some(&9));
        assert_eq!(iter.next_back(), Some(&3));
        assert_eq!(iter.next_back(), Some(&3));
        assert_eq!(iter.next(),      Some(&1));
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(),      None);

        // rare usages of next_back() combine with next()
        let rle = RleVec::from(&[0][..]);
        let mut iter = rle.iter();
        assert_eq!(iter.next_back(), Some(&0));
        assert_eq!(iter.next(),      None);

        let rle = RleVec::<i32>::from(&[][..]);
        let mut iter = rle.iter();
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(),      None);
    }

    #[test]
    fn run_iters() {
        let rle = RleVec::from(&[1,1,1,1,1,2,2,2,2,3,3,3,5,5,5,5][..]);

        let mut iterator = rle.runs();

        assert_eq!(iterator.next(), Some(&InnerRun { start: 0, len: 5, value: 1 }));
        assert_eq!(iterator.next(), Some(&InnerRun { start: 5, len: 4, value: 2 }));
        assert_eq!(iterator.next(), Some(&InnerRun { start: 9, len: 3, value: 3 }));
        assert_eq!(iterator.next(), Some(&InnerRun { start: 12, len: 4, value: 5 }));
        assert_eq!(iterator.next(), None);
        assert_eq!(iterator.next(), None);

        let mut iterator = rle.runs();

        assert_eq!(iterator.nth(0), Some(&InnerRun { start: 0, len: 5, value: 1 }));
        assert_eq!(iterator.nth(0), Some(&InnerRun { start: 5, len: 4, value: 2 }));
        assert_eq!(iterator.nth(0), Some(&InnerRun { start: 9, len: 3, value: 3 }));
        assert_eq!(iterator.nth(0), Some(&InnerRun { start: 12, len: 4, value: 5 }));
        assert_eq!(iterator.nth(0), None);

        let mut iterator = rle.runs();

        assert_eq!(iterator.nth(0), Some(&InnerRun { start: 0, len: 5, value: 1 }));
        assert_eq!(iterator.nth(1), Some(&InnerRun { start: 9, len: 3, value: 3 }));
        assert_eq!(iterator.nth(0), Some(&InnerRun { start: 12, len: 4, value: 5 }));
        assert_eq!(iterator.nth(0), None);

        assert_eq!(rle.runs().count(), 4);
        assert_eq!(rle.runs().last(), Some(&InnerRun { start: 12, len: 4, value: 5 }));
        assert_eq!(rle.runs().skip(10).last(), None);

    }

    #[test]
    fn starts_ends() {
        let v = vec![0,0,0,1,1,1,1,1,1,1,3,3,1,0,99,99,9];
        let rle = v.iter().cloned().collect::<RleVec<_>>();
        assert_eq!(rle.starts(), vec![0,3,10,12,13,14,16]);
        assert_eq!(rle.ends(),   vec![2,9,11,12,13,15,16]);

        let rle = RleVec::<i64>::new();
        assert!(rle.starts().is_empty());
        assert!(rle.ends().is_empty());
    }
}