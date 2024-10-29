use std::marker::PhantomData;
use std::ops::Index;
use std::sync::Arc;
use ark_ff::PrimeField;
use hashcaster::ptr_utils::{AsSharedMUConstPtr, AsSharedMUMutPtr, AsSharedMutPtr, UninitArr, UnsafeIndexRawMut};
use itertools::Itertools;
use rayon::iter::{IntoParallelIterator, ParallelIterator};


pub trait AlgFnSO<F: PrimeField> : Clone + Sync + Send {
    /// Executes function.
    fn exec(&self, args: &impl Index<usize, Output = F>) -> F;
    /// Declares the degree.
    fn deg(&self) -> usize;
    /// Declares the expected number of inputs.
    fn n_ins(&self) -> usize;
}

pub trait AlgFn<F: PrimeField> : Clone + Sync + Send {
    /// Executes function
    fn exec(&self, args: &impl Index<usize, Output = F>) -> impl Iterator<Item = F>;
    /// Declares the degree.
    fn deg(&self) -> usize;
    /// Declares the expected number of inputs.
    fn n_ins(&self) -> usize;
    /// Declares the expected number of outputs.
    fn n_outs(&self) -> usize;
}

pub struct VerticalIndexing<'a, T> {
    pub vecs: &'a [&'a [T]],
    pub place: usize,
}

impl<'a, T> Index<usize> for VerticalIndexing<'a, T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.vecs[index][self.place]
    }
}

pub trait AlgFnUtils<F: PrimeField> : AlgFn<F> {
    fn map(&self, args: &[&[F]]) -> Vec<Vec<F>>;
    fn map_split_hi(&self, args: &[&[F]]) -> [Vec<Vec<F>>; 2];
}

impl<F: PrimeField, Fun: AlgFn<F>> AlgFnUtils<F> for Fun {
    fn map(&self, args: &[&[F]]) -> Vec<Vec<F>> {
        let n_ins = self.n_ins();
        let n_outs = self.n_outs();
        
        assert!(args.len() == n_ins);
        let l = args[0].len();
        for i in 1..n_ins {
            assert!(args[i].len() == l)
        }

        let mut output = vec![];
        for i in 0..n_outs {
            output.push(UninitArr::<F>::new(l))
        }

        let mut output_ptrs : Vec<_> = output.iter_mut().map(|o| o.as_shared_mut_ptr()).collect();
        let ptr = output_ptrs.as_shared_mut_ptr();

        (0..l).into_par_iter().for_each(|place| {
            self.exec(&VerticalIndexing{vecs: &args, place}).zip(0 .. n_outs).for_each(|(x, s)| {
                unsafe{*(*ptr.get_mut(s)).get_mut(place) = x;}
            });
        });

        output.into_iter().map(|arr| unsafe{arr.assume_init()}).collect()
    }

    fn map_split_hi(&self, args: &[&[F]]) -> [Vec<Vec<F>>; 2] {
        let l = args[0].len();
        assert!(l % 2 == 0);
        let half = l / 2;

        let (args_l, args_r): (Vec<_>, Vec<_>) = args.iter().map(|slice| slice.split_at(half)).unzip();
        [self.map(&args_l), self.map(&args_r)]
    }
}

#[derive(Clone)]
pub struct ArcedAlgFn<F: PrimeField> {
    n_ins: usize,
    n_outs: usize,
    deg: usize,
    f: Arc<fn(&[&F]) -> Vec<F>>
}

impl<F: PrimeField> ArcedAlgFn<F> {
    pub fn new(f: Arc<fn(&[&F]) -> Vec<F>>, n_ins: usize, n_outs: usize, deg: usize) -> Self {
        Self {
            n_ins,
            n_outs,
            deg,
            f,
        }
    }
}

impl<F: PrimeField> AlgFn<F> for ArcedAlgFn<F> {
    fn exec(&self, args: &impl Index<usize, Output=F>) -> impl Iterator<Item=F> {
        self.f.as_ref()(&(0..self.n_ins).map(|i| &args[i]).collect_vec()).into_iter()
    }

    fn deg(&self) -> usize {
        self.deg
    }

    fn n_ins(&self) -> usize {
        self.n_ins
    }

    fn n_outs(&self) -> usize {
        self.n_outs
    }
}

#[derive(Clone, Copy)]
pub struct IdAlgFn<F: PrimeField> {
    n_ins: usize,
    _pd: PhantomData<F>
}

impl<F: PrimeField> IdAlgFn<F> {
    pub fn new(n_ins: usize) -> Self {
        Self {
            n_ins,
            _pd: Default::default(),
        }
    }
}

impl<F: PrimeField> AlgFn<F> for IdAlgFn<F> {
    fn exec(&self, args: &impl Index<usize, Output=F>) -> impl Iterator<Item=F> {
        (0..self.n_ins).map(|i| args[i])
    }

    fn deg(&self) -> usize {
        1
    }

    fn n_ins(&self) -> usize {
        self.n_ins
    }

    fn n_outs(&self) -> usize {
        self.n_ins
    }
}