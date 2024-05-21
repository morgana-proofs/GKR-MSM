use std::{borrow::Borrow, marker::PhantomData, sync::{atomic::{AtomicU64, Ordering}, Arc}};

use ark_bls12_381::Fr;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use itertools::Itertools;
use liblasso::{poly::{dense_mlpoly::DensePolynomial, eq_poly::{self, EqPolynomial}, unipoly::{CompressedUniPoly, UniPoly}}, subprotocols::sumcheck::SumcheckRichProof, utils::transcript::{AppendToTranscript, ProofTranscript}};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator};

use crate::utils::{map_over_poly, make_gamma_pows};
use crate::protocol::{Protocol, ProtocolProver, ProtocolVerifier, TranscriptSender, TranscriptReceiver, IndexedProofTranscript, Challenge, PolynomialMapping};


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
    type Trace = Self::WitnessInput;
    type WitnessOutput = Vec<(DensePolynomial<F>, DensePolynomial<F>)>;

    fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
        let num_vars = args[0].num_vars;
        assert!(num_vars > 0);
        for arg in &args {
            assert!(arg.num_vars == num_vars);
        }

        let mut ret = vec![];

        for arg in &args {
            ret.push(arg.split(1 << (num_vars - 1)));
        }

        (args, ret)
    }
}

impl<F: PrimeField> ProtocolProver<F> for SplitProver<F> {
    type ClaimsToReduce = (Vec<F>, Vec<(F, F)>);
    type ClaimsNew = (Vec<F>, Vec<F>);
    type Proof = ();
    type Params = ();
    type Trace = Vec<DensePolynomial<F>>;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        args: Self::Trace,
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
        *done = true;
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
        *done = true;
        let r = challenge.value;
        let (pt, evs) = claims_to_reduce;
        let evs_new = evs.iter().map(|(x, y)| *x + r * (*y - x)).collect();
        let mut r = vec![r];
        r.extend(pt.iter());
        Some((r, evs_new))
    }
}

pub struct ExtProd<F: PrimeField> {
    _marker: PhantomData<F>,
}

pub struct ExtProdProof<F: PrimeField> {
    claim_a: F,
    claim_b: F,
}

// We do not implement "protocol" traits because they assume there is at least a single round, and this is
// a direct reduction.

impl<F: PrimeField> ExtProd<F> {

    pub fn witness(a: &DensePolynomial<F>, b: &DensePolynomial<F>) -> DensePolynomial<F> {
        DensePolynomial::new(
            a.Z.par_iter()
                .map(|a_coeff| {
                    b.Z.par_iter()
                        .map(|b_coeff| *a_coeff * b_coeff)
                    }
                ).flatten().collect()
        )
    }

    pub fn compute_claims(claim: (Vec<F>, F), split: usize, a: DensePolynomial<F>, b: DensePolynomial<F>) -> ExtProdProof<F> {
        assert!(split == a.num_vars);
        let (point, value) = claim;
        let (point_a, point_b) = point.split_at(split);
        let val_a = a.evaluate(&point_a);
        let val_b = b.evaluate(&point_b);

        assert!(val_a * val_b == value);

        ExtProdProof{
            claim_a: val_a,
            claim_b: val_b
        }
    }

    pub fn validate_claims(claim: (Vec<F>, F), split: usize, proof: ExtProdProof<F>) -> ((Vec<F>, F), (Vec<F>, F)) {
        let ExtProdProof{claim_a, claim_b} = proof;

        let (point, value) = claim;
        assert!(split <= point.len());
        let (point_a, point_b) = point.split_at(split);
        assert!(claim_a * claim_b == value);

        ((point_a.to_vec(), claim_a), (point_b.to_vec(), claim_b))
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
    f: PolynomialMapping<F>,
    num_vars: usize,
    proof: SumcheckPolyMapProof<F>,
    claims_to_reduce: MultiEvalClaim<F>,

    f_folded: Option<Box<dyn Fn(&[F]) -> F + Sync + Send>>,
    current_sum: Option<F>,
    current_poly: Option<UniPoly<F>>,
    rs: Vec<F>,
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

pub fn to_multieval<F: PrimeField>(claim: EvalClaim<F>) -> MultiEvalClaim<F> {
    let points = vec![claim.point];
    let evs = vec![std::iter::repeat(0).zip(claim.evs.into_iter()).collect()];
    MultiEvalClaim{points, evs}
}

impl<F: PrimeField> Protocol<F> for SumcheckPolyMap<F> {
    type Prover = SumcheckPolyMapProver<F>;

    type Verifier = SumcheckPolyMapVerifier<F>;

    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type WitnessInput = Vec<DensePolynomial<F>>;

    type Trace = Self::WitnessInput;

    type WitnessOutput = Vec<DensePolynomial<F>>;

    type Proof = SumcheckPolyMapProof<F>;

    type Params = SumcheckPolyMapParams<F>;

    fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
        let out = map_over_poly(&args, |x|(params.f.exec)(x));
        (args, out)
    }
}

impl<F: PrimeField> ProtocolProver<F> for SumcheckPolyMapProver<F> {
    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type Proof = SumcheckPolyMapProof<F>;

    type Params = SumcheckPolyMapParams<F>;

    type Trace = Vec<DensePolynomial<F>>;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        mut args: Self::Trace,
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

            let gamma = challenge.value;
            let gamma_pows = make_gamma_pows(claims, gamma);

            *ev_folded = Some(make_folded_claim(claims, &gamma_pows));
            *f_folded = Some(make_folded_f(claims, &gamma_pows, f));

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
                        final_evaluations : final_evaluations[0..f.num_i].to_vec(),
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
        
        let f = params.f.clone();

        let num_ins = f.num_i;
        let num_outs = f.num_o;
        let num_vars = params.num_vars;
        let num_points = claims_to_reduce.points.len();
        
        // Validate that claims are well-formed.
        
        assert!(
            claims_to_reduce.evs.len() == num_points,
            "Verifier failure. Claim ill-formed: number of points {} != number of evaluation groups {}",
            num_points,
            claims_to_reduce.evs.len(),
        );

        for (i, point) in claims_to_reduce.points.iter().enumerate() {
            assert!(
                point.len() == num_vars,
                "Verifier failure. Claim ill-formed: point {} has num variables {}, but declared num variables is {}",
                i,
                point.len(),
                num_vars
            );
        }

        for ptevs in &claims_to_reduce.evs {
            for ev in ptevs {
                assert!(
                    ev.0 < num_outs,
                    "Verifier failure. Claim ill-formed: argument index {} out of range {}",
                    ev.0,
                    num_outs,
                );
            }
        }

        // Validate that proof is well-formed.
        // We can not validate round_polys size here (compressed polynomial does not expose
        // degree and I'm too lazy to vandalize liblasso once again),so this will be done during
        // round function.
        // TODO: Vandalize liblasso once again to expose this method ;)

        assert!(proof.round_polys.len() == num_vars);
        assert!(proof.final_evaluations.len() == num_ins);
        
        Self {
            proof,
            f,
            num_vars,
            claims_to_reduce,

            current_sum: None,
            current_poly: None,
            f_folded: None,
            rs: vec![],
            
        }
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
        ->
    Option<Self::ClaimsNew> {

        let Self {current_sum, f, f_folded, num_vars, claims_to_reduce, proof, rs, current_poly} = self;

        let SumcheckPolyMapProof { round_polys, final_evaluations } = proof;

        assert!(rs.len() < *num_vars, "Verifier failure: attempt to call already finished verifier.");

        let sumcheck_round_idx;
        // Detect 0-th round (gamma challenge).
        if let None = current_sum {
            let gamma = challenge.value;
            let gamma_pows = make_gamma_pows(&claims_to_reduce, gamma);
            *current_sum = Some(make_folded_claim(&claims_to_reduce, &gamma_pows));
            *f_folded = Some(make_folded_f(&claims_to_reduce, &gamma_pows, &f));
            sumcheck_round_idx = 0;
        } else {

            let r_j = challenge.value;
            let current_sum = current_sum.as_mut().unwrap();
            rs.push(r_j);
            
            sumcheck_round_idx = rs.len();

            // This unwrap never fails, because rounds after 0th always have the poly (which is last prover's message).
            let current_poly = current_poly.as_ref().unwrap();
            assert!(
                current_poly.degree() == f.degree + 1,
                "Verifier failure: polynomial degree {} at round {} incorrect",
                current_poly.degree(),
                sumcheck_round_idx
            );

            *current_sum = current_poly.evaluate(&r_j);

            if rs.len() == *num_vars {

                transcript.append_scalars(b"sumcheck_final_evals", &final_evaluations[0..f.num_i]);
                
                // Cloning final evals to not change the proof. We probably do not need it, as we consume it anyway.
                let mut args = final_evaluations.clone();
                args.extend(claims_to_reduce.points.iter().map(|p| EqPolynomial::new(p.to_vec()).evaluate(&rs)));

                assert!((f_folded.as_ref().unwrap())(&args) == *current_sum, "Verifier failure: final check incorrect");

                return Some(
                    EvalClaim{
                        point: rs.clone(),
                        evs: final_evaluations.clone(),
                    }
                )
            }
        }

        let new_poly = round_polys[sumcheck_round_idx].decompress(&current_sum.unwrap());
        // This indexing never fails, because n-th round will return from the else clause.
        transcript.append_scalars(b"poly", &new_poly.as_vec());
        *current_poly = Some(new_poly);

        None
    }
}

fn make_folded_claim<F: PrimeField>(claims: &MultiEvalClaim<F>, gamma_pows: &[F]) -> F {
    let mut i = 0; 
    (claims.evs.iter().enumerate()).fold(
        F::zero(),
        |acc, (_, evs)| {
            let mut _acc = F::zero();
            for ev in evs {
                _acc += ev.1 * gamma_pows[i];
                i += 1;
            }
            acc + _acc 
        }
    )
}

fn make_folded_f<F: PrimeField>(claims: &MultiEvalClaim<F>, gamma_pows: &[F], f: &PolynomialMapping<F>)
        -> Box<dyn Fn(&[F]) -> F + Send + Sync> 
{
    let claims = claims.clone();
    let gamma_pows = gamma_pows.to_vec();
    let PolynomialMapping{exec, degree: _, num_i, num_o: _} = f.clone();
    Box::new(
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
        }
    )
}




#[cfg(test)]
mod test {
    use std::iter::repeat_with;
    use ark_bls12_381::G1Projective;
    use ark_ff::Field;
    use ark_std::{rand::Rng, UniformRand};
    use liblasso::{benches::bench::gen_random_point, utils::test_lib::TestTranscript};
    use crate::utils::scale;

    use super::*;

    #[test]
    fn our_prover_against_liblasso_verifier() {
        let num_vars: usize = 5;
        let polys: Vec<DensePolynomial<Fr>> = (0..3).map(|i| DensePolynomial::new((0..32).map(|i| Fr::from(i)).collect())).collect();
        
        fn combfunc(i: &[Fr]) -> Vec<Fr> {
            vec![i[0], i[1], i[2] * i[2] * i[0], i[2] * i[2] * i[0]]
        }

        let params = SumcheckPolyMapParams {
            f: PolynomialMapping {
                exec: Arc::new(combfunc),
                degree: 3,
                num_i: 3,
                num_o: 4,
            },
            num_vars,
        };

        let (trace, image_polys) = SumcheckPolyMap::witness(polys.clone(), &params);

        let point: Vec<Fr> = (0..(num_vars as u64)).map(|i| Fr::from(i * 13)).collect();
        let claims : Vec<_> = image_polys.iter().enumerate().map(|(i, p)| (i, p.evaluate(&point))).collect();
        
        
        let point: Vec<Fr> = (0..(num_vars as u64)).map(|i| Fr::from(i * 13)).collect();
        let known_poly = EqPolynomial::new(point.clone());

        let _point = point.clone();


        let multiclaim = MultiEvalClaim {
            points: vec![point],
            evs: vec![claims.clone()],
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
            trace,
            &params,
        );

        let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
        let gamma_c = p_transcript.challenge_scalar(b"challenge_combine_outputs");
        let Challenge { value: gamma } = gamma_c;
        let mut res = prover.round(gamma_c, &mut p_transcript);
        while res.is_none() {
            let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
            res = prover.round(challenge, &mut p_transcript);
        }

        println!("{:?}", p_transcript.transcript.log);

        let (EvalClaim{point: proof_point, evs}, proof) = res.unwrap();
        assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

        let eq_eval = EqPolynomial::new(proof_point).evaluate(&_point);

        let SumcheckPolyMapProof { round_polys, final_evaluations } = proof;
        let mut extended_final_evaluations = final_evaluations.clone();
        extended_final_evaluations.push(eq_eval);

        let frankenproof = SumcheckRichProof::<Fr> {
            compressed_polys: round_polys,
            final_evals: extended_final_evaluations,
        };

        let combfunc = scale(combfunc);

        let folded_claim = claims.iter().rev().fold(Fr::from(0), |acc, (_, n)| acc * gamma + n);

        let known_poly_evaluator = |x: &[Fr]| known_poly.evaluate(x);
        let verifier_evaluators = vec![&known_poly_evaluator as &dyn Fn(&[Fr]) -> Fr];
        let mut v_transcript = TestTranscript::as_this(&p_transcript.transcript);
        assert_eq!(gamma, <TestTranscript<Fr> as ProofTranscript<G1Projective>>::challenge_scalar(&mut v_transcript,b"challenge_combine_outputs"));

        frankenproof.verify::<G1Projective, _, _>(
            folded_claim,
            num_vars,
            4,
            &verifier_evaluators,
            |d: &[Fr]| combfunc(&d).iter().rev().fold(Fr::from(0), |acc, n| acc * gamma + n),
            &mut v_transcript,
        ).unwrap();

        v_transcript.assert_end()
    }


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

        let (trace, split_polys) = Split::witness(polys.clone(), &());


        let evals : Vec<_> = split_polys.iter().map(|(p0, p1)| (p0.evaluate(&point), p1.evaluate(&point))).collect();

        let p_transcript: &mut IndexedProofTranscript<G1Projective, _> = &mut IndexedProofTranscript::new(TestTranscript::new());

        let claims_to_reduce = (point.clone(), evals.clone());

        let c = p_transcript.challenge_scalar(b"split");
        let mut expected_point = vec![c.value];
        expected_point.extend(point.iter());
        let expected_evals : Vec<_> = polys.iter().map(|poly| poly.evaluate(&expected_point)).collect();

        let mut prover = SplitProver::start(claims_to_reduce, trace, &());


       let ((p_point, p_evals), _) = (&mut prover).round(c, p_transcript).unwrap();

       assert!(p_point == expected_point);
       assert!(p_evals == expected_evals);

       let v_transcript : &mut IndexedProofTranscript<G1Projective, _> = &mut IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));

       let claims_to_reduce = (point.clone(), evals.clone());
       let c : Challenge<Fr> = v_transcript.challenge_scalar(b"split");
       let mut verifier = SplitVerifier::start(claims_to_reduce, (), &());
       let (v_point, v_evals) = verifier.round(c, v_transcript).unwrap();

       assert!(v_point == p_point);
       assert!(v_evals == p_evals);
       (*v_transcript).transcript.assert_end();


    }

    #[test]
    fn test_sumcheck_lite() {
        let num_vars: usize = 5;
        let polys: Vec<DensePolynomial<Fr>> = (0..3).map(|i| DensePolynomial::new((0..32).map(|i| Fr::from(i)).collect())).collect();

        fn combfunc(i: &[Fr]) -> Vec<Fr> {
            vec![i[0], i[1], i[2] * i[2] * i[0], i[2] * i[2] * i[0]]
        }

        let params = SumcheckPolyMapParams {
            f: PolynomialMapping {
                exec: Arc::new(combfunc),
                degree: 3,
                num_i: 3,
                num_o: 4,
            },
            num_vars,
        };

        let (trace, image_polys) = SumcheckPolyMap::witness(polys.clone(), &params);

        let point: Vec<Fr> = (0..(num_vars as u64)).map(|i| Fr::from(i * 13)).collect();
        let claims : Vec<_> = image_polys.iter().enumerate().map(|(i, p)| (i, p.evaluate(&point))).collect();
//        let known_poly = EqPolynomial::new(point.clone());

        let _point = point.clone();

        let multiclaim = MultiEvalClaim {
            points: vec![point],
            evs: vec![claims.clone()],
        };


        let mut prover = SumcheckPolyMapProver::start(
            multiclaim.clone(),
            trace,
            &params,
        );

        let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
        let gamma_c = p_transcript.challenge_scalar(b"challenge_combine_outputs");
        let Challenge { value: gamma } = gamma_c;
        let mut res = prover.round(gamma_c, &mut p_transcript);
        while res.is_none() {
            let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
            res = prover.round(challenge, &mut p_transcript);
        }

        println!("{:?}", p_transcript.transcript.log);

        let (EvalClaim{point: proof_point, evs}, proof) = res.unwrap();
        assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

        let mut verifier = SumcheckPolyMapVerifier::start(
            multiclaim,
            proof,
            &params,
        );

        let mut v_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));
        let gamma_c = v_transcript.challenge_scalar(b"challenge_combine_outputs");
        let Challenge { value: gamma } = gamma_c;
        let mut res = verifier.round(gamma_c, &mut v_transcript);
        while res.is_none() {
            let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
            res = verifier.round(challenge, &mut v_transcript);
        }

        println!("{:?}", v_transcript.transcript.log);

        let EvalClaim{point: proof_point, evs} = res.unwrap();
        assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());
    }

    #[test]
    fn test_sumcheck_multiclaim() {
        let num_vars: usize = 5;
        let num_points: usize = 3;
        let num_polys: usize = 4;
        let poly_eval_matrix = vec![
            vec![1, 1, 0, 1, 0],
            vec![1, 0, 1, 1, 0],
            vec![1, 1, 0, 0, 1],
        ];
        let polys: Vec<DensePolynomial<Fr>> = (0..num_polys).map(|j| DensePolynomial::new((0..32).map(|i| Fr::from((j * i + i + j * 18) as u64)).collect())).collect();

        fn combfunc(i: &[Fr]) -> Vec<Fr> {
            vec![
                i[0],
                i[1],
                i[2] * i[2] * i[0],
                i[2] * i[2] * i[0],
                i[3] * i[2]
            ]
        }


        let params = SumcheckPolyMapParams {
            f: PolynomialMapping {
                exec: Arc::new(combfunc),
                degree: 3,
                num_i: 4,
                num_o: 5,
            },
            num_vars,
        };

        let (trace, image_polys) = SumcheckPolyMap::witness(polys.clone(), &params);

        let points: Vec<Vec<Fr>> = (0..(num_points as u64)).map(|j| (0..(num_vars as u64)).map(|i| Fr::from(i * i * 13 + i * j + j )).collect()).collect();
        let claims = poly_eval_matrix.iter().zip_eq(points.iter()).map(
            |(selector, point)| {
                image_polys.iter().enumerate().zip_eq(selector.iter()).filter(|(_, &y)| y == 1).map(
                    |((i, poly), _)| {
                        (i, poly.evaluate(point))
                    }
                ).collect()
            }
        ).collect();

        let known_polys: Vec<EqPolynomial<Fr>> = points.iter().map(|p| EqPolynomial::new(p.clone())).collect();



        let multiclaim = MultiEvalClaim {
            points,
            evs: claims,
        };

        let mut prover = SumcheckPolyMapProver::start(
            multiclaim.clone(),
            trace,
            &params,
        );

        let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
        let gamma_c = p_transcript.challenge_scalar(b"challenge_combine_outputs");
        let Challenge { value: gamma } = gamma_c;
        let mut res = prover.round(gamma_c, &mut p_transcript);
        while res.is_none() {
            let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
            res = prover.round(challenge, &mut p_transcript);
        }

        println!("{:?}", p_transcript.transcript.log);

        let (EvalClaim{point: proof_point, evs}, proof) = res.unwrap();
        assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

        let mut verifier = SumcheckPolyMapVerifier::start(
            multiclaim,
            proof,
            &params,
        );

        let mut v_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));
        let gamma_c = v_transcript.challenge_scalar(b"challenge_combine_outputs");
        let Challenge { value: gamma } = gamma_c;
        let mut res = verifier.round(gamma_c, &mut v_transcript);
        while res.is_none() {
            let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
            res = verifier.round(challenge, &mut v_transcript);
        }

        println!("{:?}", v_transcript.transcript.log);

        let EvalClaim{point: proof_point, evs} = res.unwrap();
        assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());
    }
}
