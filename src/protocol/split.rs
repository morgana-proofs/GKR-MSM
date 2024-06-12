use std::marker::PhantomData;

use ark_ff::PrimeField;
use itertools::Itertools;
use crate::nested_poly::{NestedPolynomial, SplitablePoly};
use crate::protocol::protocol::{EvalClaim, Protocol, ProtocolProver, ProtocolVerifier};
use crate::transcript::{Challenge, TranscriptReceiver};
use crate::utils::{fix_var_bot, fix_var_top};

pub struct Split<F: PrimeField> {
    _marker: PhantomData<F>,
}

pub struct SplitProver<F: PrimeField> {
    claims_to_reduce: <Self as ProtocolProver<F>>::ClaimsToReduce,
    done: bool,
    _marker: PhantomData<F>,
}

pub struct SplitVerifier<F: PrimeField> {
    claims_to_reduce: <Self as ProtocolVerifier<F>>::ClaimsToReduce,
    done: bool,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Protocol<F> for Split<F> {
    type Prover = SplitProver<F>;
    type Verifier = SplitVerifier<F>;
    type ClaimsToReduce = EvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type WitnessInput = Vec<NestedPolynomial<F>>;
    type Trace = Vec<Vec<NestedPolynomial<F>>>;
    type WitnessOutput = Self::WitnessInput;
    type Proof = ();
    type Params = ();

    fn witness(args: Self::WitnessInput, _params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
        let num_vars = args[0].num_vars();
        assert!(num_vars > 0);
        for arg in &args {
            assert_eq!(arg.num_vars(), num_vars);
        }

        let (mut l, r): (Vec<NestedPolynomial<F>>, Vec<NestedPolynomial<F>>) = args.iter().map(|p| p.split_bot()).unzip();
        l.extend(r);

        (vec![args], l)
    }
}

impl<F: PrimeField> ProtocolProver<F> for SplitProver<F> {
    type ClaimsToReduce = EvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type Proof = ();
    type Params = ();
    type Trace = Vec<Vec<NestedPolynomial<F>>>;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        _args: Self::Trace,
        _params: &Self::Params,
    ) -> Self {
        Self { claims_to_reduce, done: false, _marker: PhantomData}
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, _transcript: &mut T)
                                       ->
                                       Option<(Self::ClaimsNew, Self::Proof)> {
        let Self{ claims_to_reduce, done , ..} = self;
        assert!(!*done);
        *done = true;
        let r = challenge.value;
        let EvalClaim { point, evs } = claims_to_reduce;
        let (evs_l, evs_r) = evs.split_at(evs.len() / 2);
        let (evs_l, evs_r) = (evs_l.iter(), evs_r.iter());

        let evs_new = evs_l.zip(evs_r).map(|(x, y)| *x + r * (*y - x)).collect();

        fix_var_top(point, r);

        Some((EvalClaim{point: point.clone(), evs: evs_new}, ()))
    }
}

impl<F: PrimeField> ProtocolVerifier<F> for SplitVerifier<F> {
    type ClaimsToReduce = EvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type Proof = ();
    type Params = ();

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        _proof: Self::Proof,
        _params: &Self::Params,
    ) -> Self {
        Self { claims_to_reduce, done: false, _marker: PhantomData }
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, _transcript: &mut T)
                                       ->
                                       Option<Self::ClaimsNew> {
        let Self{ claims_to_reduce, done, .. } = self;
        assert!(!*done);
        *done = true;
        let r = challenge.value;
        let EvalClaim { point, evs } = claims_to_reduce;
        let (evs_l, evs_r) = evs.split_at(evs.len() / 2);
        let (evs_l, evs_r) = (evs_l.iter(), evs_r.iter());

        let evs_new = evs_l.zip(evs_r).map(|(x, y)| *x + r * (*y - x)).collect();
        fix_var_top(point, r);

        Some(EvalClaim{point: point.clone(), evs: evs_new})
    }
}


#[cfg(test)]
mod tests {
    use std::iter::repeat_with;

    use ark_bls12_381::{Fr, G1Projective};
    use ark_ff::PrimeField;
    use ark_std::rand::Rng;
    use liblasso::utils::test_lib::TestTranscript;

    use crate::transcript::{IndexedProofTranscript, TranscriptSender};
    use crate::utils::fix_var_bot;

    use super::*;

    fn gen_random_vec<F: PrimeField>(rng: &mut impl Rng,size: usize) -> Vec<F> {
        repeat_with(|| F::rand(rng)).take(size).collect()
    }
    #[test]
    fn split_protocol() -> () {
        let num_vars: usize = 5;
        let rng = &mut ark_std::test_rng();

        let polys: Vec<NestedPolynomial<Fr>> = (0..3).map(|_| {
            NestedPolynomial::rand(rng, num_vars)
        }).collect();
        let point: Vec<Fr> = gen_random_vec(rng, num_vars - 1);

        let (trace, out) = Split::witness(polys.clone(), &());

        let evals : Vec<_> = out.iter().map(|p| p.evaluate(&point)).collect();

        let p_transcript: &mut IndexedProofTranscript<G1Projective, _> = &mut IndexedProofTranscript::new(TestTranscript::new());

        let claims_to_reduce = EvalClaim{point: point.clone(), evs: evals.clone()};

        let c = p_transcript.challenge_scalar(b"split");

        let mut expected_point = point.clone();
        fix_var_top(&mut expected_point, c.value);

        let mut unexpected_point = point.clone();
        fix_var_bot(&mut unexpected_point, c.value);

        let expected_evals : Vec<_> = polys.iter().map(|poly| poly.evaluate(&expected_point)).collect();
        let unexpected_evals : Vec<_> = polys.iter().map(|poly| poly.evaluate(&unexpected_point)).collect();

        let mut prover = SplitProver::start(claims_to_reduce, trace, &());


        let (evs, _) = (&mut prover).round(c, p_transcript).unwrap();

        assert_eq!(evs.point, expected_point);
        assert_eq!(evs.evs, expected_evals);

        let v_transcript : &mut IndexedProofTranscript<G1Projective, _> = &mut IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));

        let claims_to_reduce = EvalClaim { point: point.clone(), evs: evals.clone() };
        let c : Challenge<Fr> = v_transcript.challenge_scalar(b"split");
        let mut verifier = SplitVerifier::start(claims_to_reduce, (), &());
        let EvalClaim{point: v_point, evs: v_evals} = verifier.round(c, v_transcript).unwrap();

        assert_eq!(v_point, evs.point);
        assert_eq!(v_evals, evs.evs);
        (*v_transcript).transcript.assert_end();


    }
}