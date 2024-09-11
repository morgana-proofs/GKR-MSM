use std::marker::PhantomData;

use ark_ff::PrimeField;
use itertools::Itertools;
use crate::polynomial::fragmented::FragmentedPoly;
use crate::protocol::protocol::{EvalClaim, Protocol, ProtocolProver, ProtocolVerifier};
use crate::transcript::{Challenge, TranscriptReceiver};
use crate::utils::{fix_var_bot, fix_var_top};

pub struct SplitAt<F: PrimeField> {
    _marker: PhantomData<F>,
}

pub struct SplitAtProver<F: PrimeField> {
    claims_to_reduce: <Self as ProtocolProver<F>>::ClaimsToReduce,
    done: bool,
    params: SplitAtParams,
    _marker: PhantomData<F>,
}

pub struct SplitAtVerifier<F: PrimeField> {
    claims_to_reduce: <Self as ProtocolVerifier<F>>::ClaimsToReduce,
    done: bool,
    params: SplitAtParams,
    _marker: PhantomData<F>,
}

#[derive(Copy, Clone)]
pub struct SplitAtParams {
    pub var: usize,
    pub poly_grp_size: usize,
}

impl<F: PrimeField> Protocol<F> for SplitAt<F> {
    type Prover = SplitAtProver<F>;
    type Verifier = SplitAtVerifier<F>;
    type ClaimsToReduce = EvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type WitnessInput = Vec<FragmentedPoly<F>>;
    type Trace = Vec<Vec<FragmentedPoly<F>>>;
    type WitnessOutput = Self::WitnessInput;
    type Proof = ();
    type Params = SplitAtParams;

    fn witness(args: Self::WitnessInput, _params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
        let num_vars = args[0].num_vars();
        assert!(num_vars > 0);
        for arg in &args {
            assert_eq!(arg.num_vars(), num_vars);
        }

        let (mut l, r): (Vec<FragmentedPoly<F>>, Vec<FragmentedPoly<F>>) = args.iter().map(|p| p.split_at(_params.var.clone())).unzip();

        l = l.into_iter().chunks(_params.poly_grp_size).into_iter().interleave(r.into_iter().chunks(_params.poly_grp_size).into_iter()).flatten().collect_vec();

        (vec![args], l)
    }
}

impl<F: PrimeField> ProtocolProver<F> for SplitAtProver<F> {
    type ClaimsToReduce = EvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type Proof = ();
    type Params = SplitAtParams;
    type Trace = Vec<Vec<FragmentedPoly<F>>>;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        _args: Self::Trace,
        _params: &Self::Params,
    ) -> Self {
        Self { claims_to_reduce, done: false, params: _params.clone(), _marker: PhantomData}
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, _transcript: &mut T)
                                       ->
                                       Option<(Self::ClaimsNew, Self::Proof)> {
        let Self{ claims_to_reduce, done , ..} = self;
        assert!(!*done);
        *done = true;
        let r = challenge.value;
        let EvalClaim { point, evs } = claims_to_reduce;
        let (iter_l, iter_r) = evs.chunks(self.params.poly_grp_size).tee();
        let evs_l = iter_l.step_by(2).flatten();
        let evs_r = iter_r.skip(1).step_by(2).flatten();

        let evs_new = evs_l.zip(evs_r).map(|(x, y)| *x + r * (*y - x)).collect();

        point.insert(self.params.var, r);

        Some((EvalClaim{point: point.clone(), evs: evs_new}, ()))
    }
}

impl<F: PrimeField> ProtocolVerifier<F> for SplitAtVerifier<F> {
    type ClaimsToReduce = EvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type Proof = ();
    type Params = SplitAtParams;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        _proof: Self::Proof,
        _params: &Self::Params,
    ) -> Self {
        Self { claims_to_reduce, done: false, params: _params.clone(), _marker: PhantomData }
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, _transcript: &mut T)
                                       ->
                                       Option<Self::ClaimsNew> {
        let Self{ claims_to_reduce, done, .. } = self;
        assert!(!*done);
        *done = true;
        let r = challenge.value;
        let EvalClaim { point, evs } = claims_to_reduce;
        let (iter_l, iter_r) = evs.chunks(self.params.poly_grp_size).tee();
        let evs_l = iter_l.step_by(2).flatten();
        let evs_r = iter_r.skip(1).step_by(2).flatten();

        let evs_new = evs_l.zip(evs_r).map(|(x, y)| *x + r * (*y - x)).collect();
        point.insert(self.params.var, r);

        Some(EvalClaim{point: point.clone(), evs: evs_new})
    }
}


#[cfg(test)]
mod tests {
    use std::iter::repeat_with;
    use std::sync::{Arc, OnceLock};
    use ark_bls12_381::{Fr, G1Projective};
    use ark_ff::PrimeField;
    use ark_std::rand::{Rng, RngCore};
    use ark_std::test_rng;
    use liblasso::utils::test_lib::TestTranscript;
    use crate::polynomial::fragmented::{Fragment, Shape};
    use crate::polynomial::fragmented::FragmentContent::{Consts, Data};
    use crate::transcript::{IndexedProofTranscript, TranscriptSender};
    use crate::utils::fix_var_bot;

    use super::*;

    fn gen_random_vec<F: PrimeField>(rng: &mut impl Rng,size: usize) -> Vec<F> {
        repeat_with(|| F::rand(rng)).take(size).collect()
    }


    #[test]
    fn split_at_protocol() {
        let rng = &mut test_rng();
        let num_vars = 5;
        let num_polys = 12;
        let possible_group_sizes = [1, 2, 3, 4, 6, 12];

        fn no_const_gen<RNG: Rng>(rng: &mut RNG, num_vars: usize) -> (FragmentedPoly<Fr>, usize, usize) {
            let split_var = rng.next_u64() as usize % num_vars;
            let sector_size: usize = 1 << (num_vars - 1 - split_var);
            let data_len = 1 << num_vars;

            let s = Shape::new(
                vec![
                    Fragment {
                        mem_idx: 0,
                        len: data_len,
                        content: Data,
                        start: 0,
                    }
                ],
                1,
            );

            let shape = Arc::new(OnceLock::new());
            shape.get_or_init(|| s);
            let d = FragmentedPoly::<Fr>::rand_with_shape(rng, shape);
            (d, split_var, sector_size)
        }
        fn rng_gen<RNG: Rng>(rng: &mut RNG, num_vars: usize) -> (FragmentedPoly<Fr>, usize, usize) {
            let split_var = rng.next_u64() as usize % num_vars;
            let sector_size = 1 << (num_vars - 1 - split_var);
            let max_data_sectors_pairs = 1 << (split_var);
            let data_sectors = 2 * (rng.next_u64() as usize % max_data_sectors_pairs + 1);
            let data_len = data_sectors * sector_size;
            let consts_len = (1 << num_vars) - data_len;

            let s = Shape::new(
                vec![
                    Fragment {
                        mem_idx: 0,
                        len: data_len,
                        content: Data,
                        start: 0,
                    },
                    Fragment {
                        mem_idx: 0,
                        len: consts_len,
                        content: Consts,
                        start: data_len,
                    }
                ],
                1,
            );

            let shape = Arc::new(OnceLock::new());
            shape.get_or_init(|| s);
            let d = FragmentedPoly::<Fr>::rand_with_shape(rng, shape);
            (d, split_var, sector_size)
        }

        fn len_2_consts<RNG: Rng>(rng: &mut RNG, num_vars: usize) -> (FragmentedPoly<Fr>, usize, usize) {
            let split_var = num_vars - 1;
            let sector_size: usize = 1;
            let consts_len = 2;
            let data_len = (1 << num_vars) - consts_len;

            let s = Shape::new(
                vec![
                    Fragment {
                        mem_idx: 0,
                        len: data_len,
                        content: Data,
                        start: 0,
                    },
                    Fragment {
                        mem_idx: 0,
                        len: consts_len,
                        content: Consts,
                        start: data_len,
                    }
                ],
                1,
            );
            let shape = Arc::new(OnceLock::new());
            shape.get_or_init(|| s);
            let d = FragmentedPoly::<Fr>::rand_with_shape(rng, shape);

            (d, split_var, sector_size)
        }

        for gen in [no_const_gen, rng_gen, len_2_consts] {
            for _ in 0..100 {
                let (d, split_var, sector_size) = gen(rng, num_vars);
                let shape = d.shape.clone();
                let mut polys = vec![d];
                let poly_grp_size= possible_group_sizes[rng.next_u64() as usize % possible_group_sizes.len()];

                for _ in 1..num_polys {
                    polys.push(FragmentedPoly::rand_with_shape(rng, shape.clone()))
                }

                let point: Vec<Fr> = gen_random_vec(rng, num_vars - 1);

                let params = SplitAtParams{var: split_var, poly_grp_size};

                let (trace, out) = SplitAt::witness(polys.clone(), &params);

                let evals : Vec<_> = out.iter().map(|p| p.evaluate(&point)).collect();

                let p_transcript: &mut IndexedProofTranscript<G1Projective, _> = &mut IndexedProofTranscript::new(TestTranscript::new());

                let claims_to_reduce = EvalClaim{point: point.clone(), evs: evals.clone()};

                let c = p_transcript.challenge_scalar(b"split");

                let mut expected_point = point.clone();
                expected_point.insert(split_var, c.value);

                let expected_evals : Vec<_> = polys.iter().map(|poly| poly.evaluate(&expected_point)).collect();

                let mut prover = SplitAtProver::start(claims_to_reduce, trace, &params);

                let (evs, _) = (&mut prover).round(c, p_transcript).unwrap();

                assert_eq!(evs.point, expected_point);
                assert_eq!(evs.evs, expected_evals);

                let v_transcript : &mut IndexedProofTranscript<G1Projective, _> = &mut IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));

                let claims_to_reduce = EvalClaim { point: point.clone(), evs: evals.clone() };
                let c : Challenge<Fr> = v_transcript.challenge_scalar(b"split");
                let mut verifier = SplitAtVerifier::start(claims_to_reduce, (), &params);
                let EvalClaim{point: v_point, evs: v_evals} = verifier.round(c, v_transcript).unwrap();

                assert_eq!(v_point, evs.point);
                assert_eq!(v_evals, evs.evs);
                (*v_transcript).transcript.assert_end();

                for i in 0..num_polys {
                    let (t_vec, l_vec, r_vec) = (polys[i].vec(), out[i + poly_grp_size * (i / poly_grp_size)].vec(), out[i + poly_grp_size * (i / poly_grp_size) + poly_grp_size].vec());
                    assert_eq!(t_vec, l_vec.chunks(sector_size).interleave(r_vec.chunks(sector_size)).flatten().cloned().collect_vec(), "poly {}", i);
                }
            }
        }
    }
}