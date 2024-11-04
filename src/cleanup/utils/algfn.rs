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
    
    #[cfg(debug_assertions)]
    fn description(&self) -> String {
        "Unspecified function".to_string()
    }
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

    #[cfg(debug_assertions)]
    fn description(&self) -> String {
        format!("Identity function on {} inputs", self.n_ins).to_string()
    }
}

struct OffsetIndexer<'a, F: PrimeField, T: Index<usize, Output=F>> {
    index: &'a T,
    offset: usize,
}

impl<'a, F:PrimeField, T: Index<usize, Output=F>> OffsetIndexer<'a, F, T> {
    fn new(index: &'a T, offset: usize) -> Self {
        Self { offset, index }
    }
}

impl<'a, F:PrimeField, T: Index<usize, Output=F>> Index<usize> for OffsetIndexer<'a, F, T> {
    type Output = F;

    fn index(&self, index: usize) -> &Self::Output {
        self.index.index(index + self.offset)
    }
}

#[derive(Clone)]
pub struct RepeatedAlgFn<F: PrimeField, Fun: AlgFn<F>> {
    fun: Fun,
    count: usize,
    _pd: PhantomData<F>
}

impl<F: PrimeField, Fun: AlgFn<F>> RepeatedAlgFn<F, Fun> {
    pub fn new(fun: Fun, count: usize) -> Self {
        Self { fun, count, _pd: Default::default() }
    }
}

impl<F: PrimeField, Fun: AlgFn<F>> AlgFn<F> for RepeatedAlgFn<F, Fun> {
    fn exec(&self, args: &impl Index<usize, Output=F>) -> impl Iterator<Item=F> {
        (0..self.count)
            .map(|i|
                self.fun.exec(&OffsetIndexer::new(args, i * self.fun.n_ins())).collect_vec()
            )
            .flatten()
    }

    fn deg(&self) -> usize {
        self.fun.deg()
    }

    fn n_ins(&self) -> usize {
        self.fun.n_ins() * self.count
    }

    fn n_outs(&self) -> usize {
        self.fun.n_outs() * self.count
    }

    #[cfg(debug_assertions)]
    fn description(&self) -> String {
        format!("Repeated {} of [{}]", self.count, self.fun.description())
    }
}

#[derive(Clone)]
pub struct StackedAlgFn<F: PrimeField, Fun1: AlgFn<F>, Fun2: AlgFn<F>> {
    fun1: Fun1,
    fun2: Fun2,
    _pd: PhantomData<F>
}

impl<F: PrimeField, Fun1: AlgFn<F>, Fun2: AlgFn<F>> StackedAlgFn<F, Fun1, Fun2> {
    pub fn new(fun1: Fun1, fun2: Fun2) -> Self {
        Self { fun1, fun2, _pd: Default::default() }
    }
}
impl<F: PrimeField, Fun1: AlgFn<F>, Fun2: AlgFn<F>> AlgFn<F> for StackedAlgFn<F, Fun1, Fun2> {
    fn exec(&self, args: &impl Index<usize, Output=F>) -> impl Iterator<Item=F> {
        self.fun1.exec(args).chain(self.fun2.exec(&OffsetIndexer::new(args, self.fun1.n_ins())).collect_vec().into_iter())
    }

    fn deg(&self) -> usize {
        self.fun1.deg().max(self.fun2.deg())
    }

    fn n_ins(&self) -> usize {
        self.fun1.n_ins() + self.fun2.n_ins()
    }

    fn n_outs(&self) -> usize {
        self.fun1.n_outs() + self.fun2.n_outs()
    }

    #[cfg(debug_assertions)]
    fn description(&self) -> String {
        format!("Stacked [{}] [{}]", self.fun1.description(), self.fun2.description())
    }
}