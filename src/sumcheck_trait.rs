use core::panic;
use std::{borrow::Borrow, marker::PhantomData, sync::{atomic::{AtomicU64, Ordering}, Arc}};

use ark_bls12_381::Fr;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use itertools::Itertools;
use liblasso::{poly::{dense_mlpoly::DensePolynomial, eq_poly::{self, EqPolynomial}, unipoly::{CompressedUniPoly, UniPoly}}, subprotocols::sumcheck::SumcheckRichProof, utils::transcript::{AppendToTranscript, ProofTranscript}};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator};

use crate::map_over_poly;


#[derive(Clone)]
pub struct PolynomialMapping<F: PrimeField> {
    exec: Arc<dyn Fn(&[F]) -> Vec<F> + Send + Sync>,
    degree: usize,
    num_i: usize,
    num_o: usize,
}

// Claim
pub struct Claim<F: PrimeField> {
    point: Vec<F>,
    value: F,
}
pub enum Either<T1, T2>{
    A(T1),
    B(T2),
}


pub trait Protocol<F: PrimeField> {
    
    type Prover : ProtocolProver<
        F,
        ClaimsToReduce = Self::ClaimsToReduce,
        ClaimsNew = Self::ClaimsNew,
        Proof = Self::Proof,
        Params = Self::Params,
        WitnessInput = Self::WitnessInput,
    >;

    type Verifier : ProtocolVerifier<
        F,
        ClaimsToReduce = Self::ClaimsToReduce,
        ClaimsNew = Self::ClaimsNew,
        Proof = Self::Proof,
        Params = Self::Params,
    >;

    type ClaimsToReduce;
    type ClaimsNew;

    type WitnessInput;
    type WitnessOutput;

    type Proof;
    type Params;

    fn witness(args: &Self::WitnessInput, params: &Self::Params) -> Self::WitnessOutput;

}


pub trait ProtocolProver<F: PrimeField> {

    type ClaimsToReduce;
    type ClaimsNew;
    type Proof;
    type Params;
    type WitnessInput;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        args: Self::WitnessInput,
        params: &Self::Params,
    ) -> Self;


    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
        ->
    Option<(Self::ClaimsNew, Self::Proof)>;
}

pub trait ProtocolVerifier<F: PrimeField> {
    type Params;
    type ClaimsToReduce;
    type ClaimsNew;
    type Proof;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        proof: Self::Proof,
        params: &Self::Params,
    ) -> Self;


    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
        ->
    Option<Self::ClaimsNew>;
}

pub trait TranscriptReceiver<F: PrimeField> {
    fn append_scalar(&mut self, label: &'static [u8], scalar: &F);
    fn append_scalars(&mut self, label: &'static [u8], scalars: &[F]);
}

pub trait TranscriptSender<F: PrimeField> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Challenge<F>;
}

#[derive(Clone, Copy)]
pub struct Challenge<X> {
    pub value: X,
    pub round_id: usize,
}

/// A very thin wrapper over normal proof transcript from liblasso,
/// counting amount of challenges. Protocols under parallel composition
/// should check that their index monotonically increases.
pub struct IndexedProofTranscript<G : CurveGroup, P: ProofTranscript<G>> {
    global_round: usize,
    transcript: P,
    _marker: PhantomData<G>,
}

impl<G: CurveGroup, P: ProofTranscript<G>> IndexedProofTranscript<G, P> {
    pub fn new(transcript: P) -> Self {
        Self { global_round: 0, transcript, _marker: PhantomData }
    }

    pub fn release(self) -> P {
        self.transcript
    }

    pub fn current_global_round(&self) -> usize {
        self.global_round
    }
}

impl<G: CurveGroup, P: ProofTranscript<G>> TranscriptReceiver<G::ScalarField> for IndexedProofTranscript<G, P> {
    fn append_scalar(&mut self, label: &'static [u8], scalar: &<G>::ScalarField) {
        self.transcript.append_scalar(label, scalar)
    }
    fn append_scalars(&mut self, label: &'static [u8], scalars: &[<G>::ScalarField]) {
        self.transcript.append_scalars(label, scalars)
    }
}

impl<G: CurveGroup, P: ProofTranscript<G>> TranscriptSender<G::ScalarField> for IndexedProofTranscript<G, P> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Challenge<<G>::ScalarField> {
        let ret = Challenge {value: self.transcript.challenge_scalar(label), round_id : self.global_round};
        self.global_round += 1;
        ret
    }
}


// Impls


pub struct Split<F: PrimeField> {
    _marker: PhantomData<F>,
}

pub struct SplitProver<F: PrimeField> {
    claims_to_reduce: (Vec<F>, Vec<(F, F)>),
    done: bool,
}

pub struct SplitVerifier<F: PrimeField> {
    claims_to_reduce: (Vec<F>, Vec<(F, F)>),
    done: bool,
}

impl<F: PrimeField> Protocol<F> for Split<F> {
    type Prover = SplitProver<F>;
    type Verifier = SplitVerifier<F>;
    type ClaimsToReduce = (Vec<F>, Vec<(F, F)>);
    type ClaimsNew = (Vec<F>, Vec<F>);
    type Proof = ();
    type Params = ();
    type WitnessInput = Vec<DensePolynomial<F>>;
    type WitnessOutput = Vec<(DensePolynomial<F>, DensePolynomial<F>)>;

    fn witness(args: &Self::WitnessInput, params: &Self::Params) -> Self::WitnessOutput {
        let num_vars = args[0].num_vars;
        assert!(num_vars > 0);
        for arg in args {
            assert!(arg.num_vars == num_vars);
        }

        let mut ret = vec![];

        for arg in args {
            ret.push(arg.split(1 << (num_vars - 1)));
        }

        ret
    }
}

impl<F: PrimeField> ProtocolProver<F> for SplitProver<F> {
    type ClaimsToReduce = (Vec<F>, Vec<(F, F)>);
    type ClaimsNew = (Vec<F>, Vec<F>);
    type Proof = ();
    type Params = ();
    type WitnessInput = Vec<DensePolynomial<F>>;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        args: Vec<DensePolynomial<F>>,
        params: &Self::Params,
    ) -> Self {
        let num_vars = args[0].num_vars;
        assert!(num_vars > 0);
        for arg in args {
            assert!(arg.num_vars == num_vars);
        }
        
        Self { claims_to_reduce, done: false}
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
        ->
    Option<(Self::ClaimsNew, Self::Proof)> {
        let Self{ claims_to_reduce, done } = self;
        assert!(!*done);
        let r = challenge.value;
        let (pt, evs) = claims_to_reduce;
        let evs_new = evs.iter().map(|(x, y)| *x + r * (*y - x)).collect();
        let mut r = vec![r];
        r.extend(pt.iter());
        Some(((r, evs_new), ()))
    }
}

impl<F: PrimeField> ProtocolVerifier<F> for SplitVerifier<F> {
    type ClaimsToReduce = (Vec<F>, Vec<(F, F)>);
    type ClaimsNew = (Vec<F>, Vec<F>);
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
        let r = challenge.value;
        let (pt, evs) = claims_to_reduce;
        let evs_new = evs.iter().map(|(x, y)| *x + r * (*y - x)).collect();
        let mut r = vec![r];
        r.extend(pt.iter());
        Some((r, evs_new))
    }
}


pub struct SumcheckPolyMap<F: PrimeField> {
    _marker: PhantomData<F>,
}

pub struct SumcheckPolyMapProver<F: PrimeField> {
    polys : Vec<DensePolynomial<F>>,
    round_polys : Option<Vec<CompressedUniPoly<F>>>,
    rs: Vec<F>,
    f: PolynomialMapping<F>,
    f_folded: Option<Box<dyn Fn(&[F]) -> F + Sync + Send>>,
    claims: MultiEvalClaim<F>,
    ev_folded: Option<F>,
    num_vars: usize,
}

pub struct SumcheckPolyMapVerifier<F: PrimeField> {
    _marker: PhantomData<F>,
}

pub struct SumcheckPolyMapProof<F: PrimeField> {
    round_polys : Vec<CompressedUniPoly<F>>,
    final_evaluations: Vec<F>,
}

pub struct SumcheckPolyMapParams<F: PrimeField> {
    pub f: PolynomialMapping<F>,
    pub num_vars: usize,
}

#[derive(Clone)]
pub struct MultiEvalClaim<F: PrimeField> {
    pub points: Vec<Vec<F>>,
    pub evs: Vec<Vec<(usize, F)>>,
}

#[derive(Clone)]
pub struct EvalClaim<F: PrimeField> {
    pub point: Vec<F>,
    pub evs: Vec<F>,
}

impl<F: PrimeField> Protocol<F> for SumcheckPolyMap<F> {
    type Prover = SumcheckPolyMapProver<F>;

    type Verifier = SumcheckPolyMapVerifier<F>;

    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type WitnessInput = Vec<DensePolynomial<F>>;

    type WitnessOutput = Vec<DensePolynomial<F>>;

    type Proof = SumcheckPolyMapProof<F>;

    type Params = SumcheckPolyMapParams<F>;

    fn witness(args: &Self::WitnessInput, params: &Self::Params) -> Self::WitnessOutput {
        map_over_poly(args, |x|(params.f.exec)(x))
    }
}

impl<F: PrimeField> ProtocolProver<F> for SumcheckPolyMapProver<F> {
    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type Proof = SumcheckPolyMapProof<F>;

    type Params = SumcheckPolyMapParams<F>;

    type WitnessInput = Vec<DensePolynomial<F>>;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        mut args: Self::WitnessInput,
        params: &Self::Params,
    ) -> Self {
        assert!(args.len() == params.f.num_i);
        
        
        let eqs_iter = claims_to_reduce
            .points
            .iter()
            .map(|r|
                DensePolynomial::new(EqPolynomial::new(r.clone()).evals())
            );

        args.extend(eqs_iter);


        Self {
            polys: args,
            round_polys: Some(vec![]),
            rs: vec![],
            f: params.f.clone(),
            claims: claims_to_reduce,
            f_folded: None,
            ev_folded: None,
            num_vars: params.num_vars,
        }
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
        ->
    Option<(Self::ClaimsNew, Self::Proof)> {

        let Self {
            claims,
            polys,
            round_polys,
            rs,
            f,
            f_folded,
            ev_folded,
            num_vars,
        } = self;

        let round_polys = round_polys.as_mut().unwrap();

        assert!(rs.len() < *num_vars);


        if let None = f_folded {

            let num_claims = claims.evs.iter().fold(0, |acc, upd| acc + upd.len());

            let gamma = challenge.value;
            let mut gamma_pows = vec![F::one(), gamma];
            for i in 2..num_claims {
                let tmp = gamma_pows[i-1];
                gamma_pows.push(tmp * gamma);
            }

            let mut i = 0;
            *ev_folded = Some(claims.evs.iter()
                .flatten()
                .fold(F::zero(), |acc, upd| {i+=1; acc + gamma_pows[i-1] * upd.1}));

            let PolynomialMapping{num_i, num_o: _, exec, degree: _} = f;

            let exec = exec.clone();
            let claims = claims.clone();
            let num_i = *num_i;

            *f_folded = Some(Box::new(
                move |args: &[F]| {
                let (args, eqpolys) = args.split_at(num_i);
                let out = exec(args);
                let mut i = 0;
                (claims.evs.iter().enumerate()).fold(
                    F::zero(),
                    |acc, (j, evs)| {
                        let mut _acc = F::zero();
                        for ev in evs {
                            _acc += out[ev.0] * gamma_pows[i];
                            i += 1;
                        }
                        acc + _acc * eqpolys[j]

                    }
                )
            }));
        } else {
            let r_j = challenge.value;
            rs.push(r_j);
        
            // bound all tables to the verifier's challenege
            for poly in polys.iter_mut() {
                poly.bound_poly_var_top(&r_j);
            }

            if rs.len() == *num_vars {
                let final_evaluations: Vec<F> = polys.iter().map(|poly| poly[0]).collect();

                transcript.append_scalars(b"sumcheck_final_evals", &final_evaluations[0..f.num_i]);
    
                return Some((
                    EvalClaim{
                        point: rs.clone(),
                        evs: final_evaluations[0..f.num_i].to_vec(),
                    },
                    SumcheckPolyMapProof{
                        round_polys : self.round_polys.take().unwrap(),
                        final_evaluations,
                    }
                ))
            }

        }


        let combined_degree = f.degree + 1;

        let mut eval_points = vec![F::zero(); combined_degree + 1];

        let mle_half = polys[0].len() / 2;
    
        // let mut accum = vec![vec![F::zero(); combined_degree + 1]; mle_half];
        #[cfg(feature = "multicore")]
        let iterator = (0..mle_half).into_par_iter();
    
        #[cfg(not(feature = "multicore"))]
        let iterator = 0..mle_half;
    
        let comb_func = f_folded.as_ref().unwrap();

        let accum: Vec<Vec<F>> = iterator
            .map(|poly_term_i| {
            let diffs: Vec<F> = polys.iter().map(|p| p[mle_half + poly_term_i] - p[poly_term_i]).collect();
            let mut accum = vec![F::zero(); combined_degree + 1];
            // Evaluate P({0, ..., |g(r)|})
    
            // TODO(#28): Optimize
            // Tricks can be used here for low order bits {0,1} but general premise is a running sum for each
            // of the m terms in the Dense multilinear polynomials. Formula is:
            // half = | D_{n-1} | / 2
            // D_n(index, r) = D_{n-1}[half + index] + r * (D_{n-1}[half + index] - D_{n-1}[index])
    
            // eval 0: bound_func is A(low)
            // eval_points[0] += comb_func(&polys.iter().map(|poly| poly[poly_term_i]).collect());
            let eval_at_zero: Vec<F> = polys.iter().map(|p| p[poly_term_i]).collect();
            accum[0] += comb_func(&eval_at_zero);
    
            // TODO(#28): Can be computed from prev_round_claim - eval_point_0
            let eval_at_one: Vec<F> = polys.iter().map(|p| p[mle_half + poly_term_i]).collect();
            accum[1] += comb_func(&eval_at_one);
    
            // D_n(index, r) = D_{n-1}[half + index] + r * (D_{n-1}[half + index] - D_{n-1}[index])
            // D_n(index, 0) = D_{n-1} +
            // D_n(index, 1) = D_{n-1} + (D_{n-1}[HIGH] - D_{n-1}[LOW])
            // D_n(index, 2) = D_{n-1} + (D_{n-1}[HIGH] - D_{n-1}[LOW]) + (D_{n-1}[HIGH] - D_{n-1}[LOW])
            // D_n(index, 3) = D_{n-1} + (D_{n-1}[HIGH] - D_{n-1}[LOW]) + (D_{n-1}[HIGH] - D_{n-1}[LOW]) + (D_{n-1}[HIGH] - D_{n-1}[LOW])
            // ...
    
            let mut existing_term = eval_at_one;
            for acc in accum.iter_mut().skip(2) {
                for poly_i in 0..polys.len() {
                existing_term[poly_i] += diffs[poly_i];
                }
    
                *acc += comb_func(&existing_term)
            }
            accum
            })
            .collect();
    
        #[cfg(feature = "multicore")]
        eval_points
            .par_iter_mut()
            .enumerate()
            .for_each(|(poly_i, eval_point)| {
            *eval_point = accum
                .par_iter()
                .take(mle_half)
                .map(|mle| mle[poly_i])
                .sum::<F>();
            });
    
        #[cfg(not(feature = "multicore"))]
        for (poly_i, eval_point) in eval_points.iter_mut().enumerate() {
            for mle in accum.iter().take(mle_half) {
            *eval_point += mle[poly_i];
            }
        }
        
        let round_uni_poly = UniPoly::from_evals(&eval_points);
    
        // append the prover's message to the transcript
        transcript.append_scalars(b"poly", &round_uni_poly.as_vec());
        // and to proof
        round_polys.push(round_uni_poly.compress());


        // let r_j = challenge.value;
        // rs.push(r_j);
    
        // // bound all tables to the verifier's challenege
        // for poly in polys {
        //     poly.bound_poly_var_top(&r_j);
        // }
        // round_polys.push(round_uni_poly.compress());

        None

    }
}

impl<F: PrimeField> ProtocolVerifier<F> for SumcheckPolyMapVerifier<F> {
    type Params = SumcheckPolyMapParams<F>;

    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type Proof = SumcheckPolyMapProof<F>;
    
    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        proof: Self::Proof,
        params: &Self::Params,
    ) -> Self {
        todo!()
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
        ->
    Option<Self::ClaimsNew> {
        todo!()
    }
}



#[cfg(test)]
mod test {
    use std::iter::repeat;
    use ark_bls12_381::G1Projective;
    use ark_ff::Field;
    use liblasso::utils::test_lib::TestTranscript;

    use super::*;


    pub fn scale_c00l<F: Field, T: Fn (&[F]) -> Vec<F>>(f: T) -> impl Fn (&[F]) -> Vec<F> {
        move |data| -> Vec<F> {
            let (pts, factor) = data.split_at(data.len() - 1);
            f(&pts.to_vec()).iter().map(|p| *p * factor[0]).collect()
        }
    }


    #[test]
    fn our_prover_against_liblasso_verifier() {
        let num_vars: usize = 5;
        let polys: Vec<DensePolynomial<Fr>> = (0..3).map(|i| DensePolynomial::new((0..32).map(|i| Fr::from(i)).collect())).collect();
        let point: Vec<Fr> = (0..(num_vars as u64)).map(|i| Fr::from(i * 13)).collect();
        let claims = polys.iter().enumerate().map(|(i, p)| (i, p.evaluate(&point))).collect();
        let known_poly = EqPolynomial::new(point.clone());

        fn combfunc(i: &[Fr]) -> Vec<Fr> {
            vec![i[0], i[1], i[2] * i[2] * i[0], i[2] * i[2] * i[0]]
        }

        let multiclaim = MultiEvalClaim {
            points: vec![point],
            evs: vec![claims],
        };

        let params = SumcheckPolyMapParams {
            f: PolynomialMapping {
                exec: Arc::new(combfunc),
                degree: 3,
                num_i: 3,
                num_o: 4,
            },
            num_vars,
        };

        let mut prover = SumcheckPolyMapProver::start(
            multiclaim,
            polys.clone(),
            &params,
        );

        let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new((0..100).map(|i| Fr::from(i)).collect(), vec![]));
        let gamma_c = p_transcript.challenge_scalar(b"challenge_combine_outputs");
        let Challenge { value: gamma, round_id: _ } = gamma_c;
        let mut res = prover.round(gamma_c, &mut p_transcript);
        while res.is_none() {
            let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
            res = prover.round(challenge, &mut p_transcript);
        }

        println!("{:?}", p_transcript.transcript.log);

        let (EvalClaim{point: proof_point, evs}, proof) = res.unwrap();
        assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

        let _claim = prover.ev_folded.unwrap();

        let SumcheckPolyMapProof { round_polys, final_evaluations } = proof;
        let frankenproof = SumcheckRichProof::<Fr> {
            compressed_polys: round_polys,
            final_evals: final_evaluations,
        };

        let mut _final_evals = frankenproof.final_evals.clone();
        _final_evals.pop();
        assert!(evs == _final_evals, "1");

        let combfunc = scale_c00l(combfunc);

        let final_eval = combfunc(&frankenproof.final_evals).iter().rev().fold(Fr::from(0), |acc, n| acc * gamma + n);
        let final_eval_2 = prover.f_folded.unwrap()(&frankenproof.final_evals);

        assert!(final_eval == final_eval_2, "2");

        let known_poly_evaluator = |x: &[Fr]| known_poly.evaluate(x);
        let verifier_evaluators = vec![&known_poly_evaluator as &dyn Fn(&[Fr]) -> Fr];
        let mut v_transcript = TestTranscript::as_this(&p_transcript.transcript);
        assert_eq!(gamma, <TestTranscript<Fr> as ProofTranscript<G1Projective>>::challenge_scalar(&mut v_transcript,b"challenge_combine_outputs"));
        
        
        frankenproof.verify::<G1Projective, _, _>(
            _claim,
            num_vars,
            4,
            &verifier_evaluators,
            |d: &Vec<Fr>| combfunc(&d).iter().rev().fold(Fr::from(0), |acc, n| acc * gamma + n),
            &mut v_transcript,
        ).unwrap();

        v_transcript.assert_end()
    }
}
