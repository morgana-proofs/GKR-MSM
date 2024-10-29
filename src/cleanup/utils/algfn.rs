use std::marker::PhantomData;
use std::ops::Index;
use std::sync::Arc;
use ark_ff::PrimeField;
use itertools::Itertools;


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