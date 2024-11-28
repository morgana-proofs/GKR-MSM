use std::cell::Cell;
use ark_ff::{Field, PrimeField};
use itertools::{repeat_n, Itertools};
use ark_ec::twisted_edwards::{Affine, Projective, TECurveConfig};
use rand::{Rng, RngCore};
use rayon::current_num_threads;
use hashcaster::ptr_utils::UninitArr;
use num_traits::{One, Zero};
use liblasso::utils::math::Math;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use ark_std::UniformRand;
use rayon::prelude::ParallelSliceMut;
use crate::cleanup::polys::common::{BindVar, BindVar21, Densify, EvaluateAtPoint, Make21, MapSplit, RandomlyGeneratedPoly};
use crate::cleanup::protocols::splits::SplitIdx;
use crate::cleanup::protocols::sumcheck::bind_dense_poly;
use crate::cleanup::utils::algfn::AlgFn;
use rayon::iter::IndexedParallelIterator;

pub const MIN_PAR_CHUNK_INPUT: Cell<usize> = Cell::new(1 << 13);

impl<F: PrimeField> EvaluateAtPoint<F> for Vec<F> {
    fn evaluate(&self, p: &[F]) -> F {
        assert_eq!(self.len(), 1 << p.len());
        let mut tmp = Some(self.clone());
        for f in p.iter().rev() {
            tmp = Some(tmp.unwrap().bind(*f));
        }
        tmp.unwrap()[0]
    }
}

impl<F: PrimeField> BindVar<F> for Vec<F> {
    fn bind(mut self, t: F) -> Self {
        bind_dense_poly(&mut self, t);
        self
    }
}

pub fn bind_21_single_thread<F: PrimeField>(vec: &mut Vec<F>, t: F) {
    let tm1 = t - F::one();
    {
        for i in 0..(vec.len() / 2) {
            vec[i] = vec[2 * i + 1] + tm1 * (vec[2 * i] - vec[2 * i + 1]);
        }
        let mut i = vec.len() / 2;
        if i % 2 == 1 {
            vec[i] = F::zero();
            i += 1;
        }
        vec.truncate(i);
    }

}

impl<F: PrimeField> BindVar21<F> for Vec<F> {
    fn bind_21(&mut self, t: F) {
        #[cfg(not(feature = "parallel"))]
        {
            bind_21_single_thread(self, t);
        }
        #[cfg(feature = "parallel")]
        {
            let tm1 = t - F::one();
            let num_threads = 1 << current_num_threads().log_2();

            let mut batch_size = (MIN_PAR_CHUNK_INPUT.get() * num_threads).min(self.len());

            for i in 0..(batch_size / 2) {
                self[i] = self[2 * i + 1] + tm1 * (self[2 * i] - self[2 * i + 1]);
            }

            while batch_size < self.len() {
                let (current, _) = self.split_at_mut(batch_size * 2);
                let (previous, input) = current.split_at_mut(batch_size);
                let (_, output) = previous.split_at_mut(batch_size / 2);
                let iter_out = output.par_chunks_mut(batch_size / 2 / num_threads);
                let iter_in = input.par_chunks_mut(batch_size / num_threads);
                iter_out.zip_eq(iter_in).for_each(|(output, input)| {
                    for i in 0..output.len() {
                        output[i] = input[2 * i + 1] + tm1 * (input[2 * i] - input[2 * i + 1]);
                    }
                });
                batch_size *= 2;
            }
            self.truncate(batch_size / 2);
        }
    }
}

impl<F: PrimeField> Make21<F> for Vec<F> {
    fn make_21(&mut self) {
        #[cfg(not(feature = "parallel"))]
        let iter = self.chunks_mut(2);
        #[cfg(feature = "parallel")]
        let iter = self.par_chunks_mut(2);

        iter.map(|c| {
            for i in 0..(c.len() / 2) {
                c[2 * i] = c[2 * i + 1].double() - c[2 * i];
            }
        }).count();
    }
}

impl<F: PrimeField> MapSplit<F> for Vec<F> {
    fn algfn_map_split<Fnc: AlgFn<F>>(polys: &[Self], func: Fnc, var_idx: SplitIdx, bundle_size: usize) -> Vec<Self> {
        #[cfg(debug_assertions)]
        println!("SPLIT MAP D->D   with {}", func.description());

        let mut outs = [
            (0..func.n_outs()).map(|_| Vec::with_capacity(polys[0].len() / 2)).collect_vec(),
            (0..func.n_outs()).map(|_| Vec::with_capacity(polys[0].len() / 2)).collect_vec(),
        ];

        let num_vars = polys[0].len().log_2();

        let segment_size = 1 << var_idx.lo_usize(num_vars);

        let mut inputs = polys.iter().map(|_| F::zero()).collect_vec();

        for idx in 0..polys[0].len() {
            inputs = polys.iter().map(|p| p[idx]).collect_vec();
            for (data, ret) in outs[(idx / segment_size) % 2].iter_mut().zip_eq(func.exec(&inputs)) {
                data.push(ret)
            }
        }

        let [l, r] = outs;
        l.into_iter().chunks(bundle_size).into_iter().interleave(r.into_iter().chunks(bundle_size).into_iter()).flatten().collect_vec()
    }

    fn algfn_map<Fnc: AlgFn<F>>(polys: &[Self], func: Fnc) -> Vec<Self> {
        #[cfg(debug_assertions)]
        println!("..... MAP D->D   with {}", func.description());
        #[cfg(feature = "parallel")]
        let chunk_size = {
            let split_factor = 4 * current_num_threads();
            (polys[0].len() + split_factor - 1) / split_factor
        };
        #[cfg(not(feature = "parallel"))]
        let chunk_size = {
            polys[0].len()
        };

        let mut outs = (0..func.n_outs()).map(|_| UninitArr::new(polys[0].len())).collect_vec();
        let mut iter_ins = polys.iter().map(|i| i.chunks(chunk_size)).collect_vec();
        let mut iter_out = outs.iter_mut().map(|i| i.chunks_mut(chunk_size)).collect_vec();

        let mut row_chunked_iterator = (0..iter_ins[0].len()).map(|_| {
            (
                iter_ins.iter_mut().map(|c| c.next().unwrap()).collect_vec(),
                iter_out.iter_mut().map(|c| c.next().unwrap()).collect_vec()
            )
        }).collect_vec();

        #[cfg(feature = "parallel")]
        let iter = row_chunked_iterator.into_par_iter();
        #[cfg(not(feature = "parallel"))]
        let iter = row_chunked_iterator.into_iter();

        iter.map(|(input_chunks, mut output_chunks)| {
            let mut inputs = input_chunks.iter().map(|c| c[0]).collect_vec();

            for idx in 0..input_chunks[0].len() {
                let out = func.exec(&inputs);
                for (tgt, val) in out.enumerate() {
                    output_chunks[tgt][idx].write(val);
                }
                if idx + 1 < input_chunks[0].len() {
                    inputs = input_chunks.iter().map(|c| c[idx + 1]).collect_vec();
                }
            }
        }).count();
        unsafe { outs.into_iter().map(|o| o.assume_init()).collect_vec() }
    }
}

pub struct DensePolyRndConfig {
    pub num_vars: usize,
}

impl<F: PrimeField> RandomlyGeneratedPoly<F> for Vec<F> {
    type Config = DensePolyRndConfig;

    fn rand_points<CC: TECurveConfig<BaseField=F>, RNG: Rng>(rng: &mut RNG, cfg: Self::Config) -> [Self; 3] {
        // let count = (0..(rng.next_u64() as usize % ((1 << (cfg.num_vars - 1)) + 1)) * 2);
        let count = 0..(1 << cfg.num_vars);
        let data = count.map(|_| {
            let p = Projective::<CC>::rand(rng);
            (p.x, p.y, p.z)
        }).collect_vec();

        let (x, y, z) = data.into_iter().multiunzip();

        [
            x,
            y,
            z
        ]
    }

    fn rand_points_affine<CC: TECurveConfig<BaseField=F>, RNG: Rng>(rng: &mut RNG, cfg: Self::Config) -> [Self; 2] {
        let data = (0..(rng.next_u64() as usize % (1 << (cfg.num_vars - 1) + 1)) * 2).map(|_| {
            let p = Affine::<CC>::rand(rng);
            (p.x, p.y)
        }).collect_vec();

        let (x, y) = data.into_iter().multiunzip();

        [
            x,
            y,
        ]
    }
}

impl<F: PrimeField> Densify<F> for Vec<F> {
    type Hint = usize;

    fn to_dense(&self, hint: Self::Hint) -> Vec<F> {
        let mut out = self.clone();
        out.extend(repeat_n(F::zero(), (1 << hint) - out.len()));
        out
    }
}