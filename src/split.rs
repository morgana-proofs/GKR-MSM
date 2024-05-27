use std::marker::PhantomData;
use ark_ff::PrimeField;
use liblasso::poly::dense_mlpoly::DensePolynomial;
use crate::protocol::{Challenge, Protocol, ProtocolProver, ProtocolVerifier, TranscriptReceiver};
use crate::sumcheck_trait::{EvalClaim, MultiEvalClaim};

pub struct Split<F: PrimeField> {
    _marker: PhantomData<F>,
}

pub struct SplitProver<F: PrimeField> {
    claims_to_reduce: <Self as ProtocolProver<F>>::ClaimsToReduce,
    done: bool,
}

pub struct SplitVerifier<F: PrimeField> {
    claims_to_reduce: <Self as ProtocolVerifier<F>>::ClaimsToReduce,
    done: bool,
}

impl<F: PrimeField> Protocol<F> for Split<F> {
    type Prover = SplitProver<F>;
    type Verifier = SplitVerifier<F>;
    type ClaimsToReduce = EvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type Proof = ();
    type Params = ();
    type WitnessInput = Vec<DensePolynomial<F>>;
    type Trace = Vec<Vec<DensePolynomial<F>>>;
    type WitnessOutput = Self::WitnessInput;

    fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
        let num_vars = args[0].num_vars;
        assert!(num_vars > 0);
        for arg in &args {
            assert!(arg.num_vars == num_vars);
        }

        let (mut l, r): (Vec<DensePolynomial<F>>, Vec<DensePolynomial<F>>) = args.iter().map(|p| p.split(1 << (num_vars - 1))).unzip();
        l.extend(r);

        (vec![args], l)
    }
}

impl<F: PrimeField> ProtocolProver<F> for SplitProver<F> {
    type ClaimsToReduce = EvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type Proof = ();
    type Params = ();
    type Trace = Vec<Vec<DensePolynomial<F>>>;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        args: Self::Trace,
        params: &Self::Params,
    ) -> Self {
        Self { claims_to_reduce, done: false}
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
                                       ->
                                       Option<(Self::ClaimsNew, Self::Proof)> {
        let Self{ claims_to_reduce, done } = self;
        assert!(!*done);
        *done = true;
        let r = challenge.value;
        let EvalClaim { point, evs } = claims_to_reduce;
        let (evs_l, evs_r) = evs.split_at(evs.len() / 2);

        let evs_new = evs_l.iter().zip(evs_r.iter()).map(|(x, y)| *x + r * (*y - x)).collect();
        let mut r = vec![r];
        r.extend(point.iter());
        Some((EvalClaim{point: r, evs: evs_new}, ()))
    }
}

impl<F: PrimeField> ProtocolVerifier<F> for SplitVerifier<F> {
    type ClaimsToReduce = EvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type Proof = ();
    type Params = ();

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        proof: Self::Proof,
        params: &Self::Params,
    ) -> Self {
        Self { claims_to_reduce, done: false }
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
                                       ->
                                       Option<Self::ClaimsNew> {
        let Self{ claims_to_reduce, done } = self;
        assert!(!*done);
        *done = true;
        let r = challenge.value;
        let EvalClaim { point, evs } = claims_to_reduce;
        let (evs_l, evs_r) = evs.split_at(evs.len() / 2);

        let evs_new = evs_l.iter().zip(evs_r.iter()).map(|(x, y)| *x + r * (*y - x)).collect();
        let mut r = vec![r];
        r.extend(point.iter());
        Some(EvalClaim{point: r, evs: evs_new})
    }
}


#[cfg(test)]
mod tests {
    use std::iter::repeat_with;
    use ark_bls12_381::{Fr, G1Projective};
    use ark_ff::PrimeField;
    use ark_std::rand::Rng;
    use liblasso::poly::dense_mlpoly::DensePolynomial;
    use liblasso::utils::test_lib::TestTranscript;
    use crate::protocol::{Challenge, IndexedProofTranscript, TranscriptSender};

    use super::*;

    fn gen_random_vec<F: PrimeField>(rng: &mut impl Rng,size: usize) -> Vec<F> {
        repeat_with(|| F::rand(rng)).take(size).collect()
    }
    #[test]
    fn split_protocol() -> () {
        let num_vars: usize = 5;
        let rng = &mut ark_std::test_rng();

        let polys: Vec<DensePolynomial<Fr>> = (0..3).map(|_| {
            DensePolynomial::new(gen_random_vec(rng, 1 << num_vars))
        }).collect();
        let point: Vec<Fr> = gen_random_vec(rng, num_vars - 1);

        let (trace, out) = Split::witness(polys.clone(), &());

        let mut evals : Vec<_> = out.iter().map(|p| p.evaluate(&point)).collect();

        let p_transcript: &mut IndexedProofTranscript<G1Projective, _> = &mut IndexedProofTranscript::new(TestTranscript::new());

        let claims_to_reduce = EvalClaim{point: point.clone(), evs: evals.clone()};

        let c = p_transcript.challenge_scalar(b"split");
        let mut expected_point = vec![c.value];
        expected_point.extend(&point);
        let expected_evals : Vec<_> = polys.iter().map(|poly| poly.evaluate(&expected_point)).collect();

        let mut prover = SplitProver::start(claims_to_reduce, trace, &());


        let (evs, _) = (&mut prover).round(c, p_transcript).unwrap();

        assert!(evs.point == expected_point);
        assert!(evs.evs == expected_evals);

        let v_transcript : &mut IndexedProofTranscript<G1Projective, _> = &mut IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));

        let claims_to_reduce = EvalClaim { point: point.clone(), evs: evals.clone() };
        let c : Challenge<Fr> = v_transcript.challenge_scalar(b"split");
        let mut verifier = SplitVerifier::start(claims_to_reduce, (), &());
        let EvalClaim{point: v_point, evs: v_evals} = verifier.round(c, v_transcript).unwrap();

        assert!(v_point == evs.point);
        assert!(v_evals == evs.evs);
        (*v_transcript).transcript.assert_end();


    }
}