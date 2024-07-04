use std::{marker::PhantomData};
use std::ops::AddAssign;
use std::sync::Arc;

use ark_ff::{Field, PrimeField};
use ark_std::iterable::Iterable;
use itertools::Itertools;
use liblasso::{poly::{eq_poly::EqPolynomial, unipoly::{CompressedUniPoly, UniPoly}}};
use liblasso::poly::dense_mlpoly::DensePolynomial;
#[cfg(feature = "prof")]
use profi::{prof, prof_guard};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator};

use crate::{transcript::{Challenge, TranscriptReceiver}, utils::{make_gamma_pows, map_over_poly_legacy}};
use crate::copoly::{CopolyData, Copolynomial, EqPoly};
use crate::polynomial::fragmented::{FragmentedPoly, InterOp};
use crate::utils::{fix_var_bot};

use super::protocol::{EvalClaim, MultiEvalClaim, PolynomialMapping, Protocol, ProtocolProver, ProtocolVerifier};

// Impls

// Fragmented

pub struct SumcheckPolyMap<F: PrimeField> {
    phantom_data: PhantomData<F>
}

pub struct Splits<F: PrimeField> {
    pub lpolys: Vec<FragmentedPoly<F>>,
    pub rpolys: Vec<FragmentedPoly<F>>,
    pub lcopolys: Vec<CopolyData<F>>,
    pub rcopolys: Vec<CopolyData<F>>,
}

pub struct FragmentedLincomb<F: PrimeField> {
    polys: Vec<FragmentedPoly<F>>,
    splits: Option<Splits<F>>,
    copolys: Vec<Box<dyn Copolynomial<F> + Send + Sync>>,
    folded_f: Option<Arc<dyn Fn(&[F]) -> F + Sync + Send>>,
    degree: usize,
}

pub struct SumcheckPolyMapProver<F: PrimeField> {
    sumcheckable: Option<Box<dyn Sumcheckable<F>>>,
    polys: Option<Vec<FragmentedPoly<F>>>,
    mapping: PolynomialMapping<F>,
    ev_folded: Option<F>,
    num_vars: usize,
    claims: MultiEvalClaim<F>,
    rs: Vec<F>,
    round_polys: Option<Vec<CompressedUniPoly<F>>>,
}

pub(crate) trait Sumcheckable<F: PrimeField> {
    fn bind(&mut self, f: &F);

    fn split(&mut self) {
        unimplemented!()
    }
    fn unipoly(&mut self) -> UniPoly<F>;

    fn final_evals(&self) -> Vec<F>;
}

impl<F: PrimeField> Sumcheckable<F> for FragmentedLincomb<F> {
    fn split(&mut self) {
        if self.splits.is_some() {
            return;
        }
        let (lpolys, rpolys): (Vec<FragmentedPoly<F>>, Vec<FragmentedPoly<F>>) = self.polys.par_iter().map(|p| p.split()).unzip();
        let (lcopolys, rcopolys): (Vec<CopolyData<F>>, Vec<CopolyData<F>>) = self.copolys.par_iter_mut().map(|p| p.materialize_split()).unzip();
        self.splits = Some(Splits {
            lpolys,
            rpolys,
            lcopolys,
            rcopolys,
        })
    }

    fn bind(&mut self, f: &F) {
        self.split();
        let Splits { mut lpolys, rpolys, .. } = self.splits.take().unwrap();
        lpolys.par_iter_mut().zip(rpolys.par_iter()).map(|(l, r)| {
            l.bind_from(r, f);
        }).count();
        self.polys = lpolys;

        self.copolys.par_iter_mut().map(|copoly| {
            copoly.bind(f);
        }).count();
    }

    fn unipoly(&mut self) -> UniPoly<F> {
        self.split();
        let Splits { lpolys, rpolys, lcopolys, rcopolys } = self.splits.take().unwrap();

        let poly_diffs = lpolys
            .par_iter()
            .zip(rpolys.par_iter())
            .map(|(l, r)| {let mut r = r.clone(); r -= l; r})
            .collect::<Vec<_>>();

        let copoly_diffs = lcopolys
            .par_iter()
            .zip(rcopolys.par_iter())
            .map(|(l, r)| {let mut r = r.clone(); r -= l; r})
            .collect::<Vec<_>>();

        let mut poly_extensions = Vec::with_capacity(self.degree + 2);
        poly_extensions.push(lpolys);
        poly_extensions.push(rpolys);

        let mut copoly_extensions = Vec::with_capacity(self.degree + 2);
        copoly_extensions.push(lcopolys);
        copoly_extensions.push(rcopolys);

        for i in 2..(self.degree + 2) {
            poly_extensions.push(poly_extensions[i - 1].clone());
            poly_extensions[i].par_iter_mut().zip(poly_diffs.par_iter()).map(|(p, d)| p.add_assign(d)).count();

            copoly_extensions.push(copoly_extensions[i - 1].clone());
            copoly_extensions[i].par_iter_mut().zip(copoly_diffs.par_iter()).map(|(p, d)| p.add_assign(d)).count();
        }
        let folded = self.folded_f.as_ref().unwrap().clone();
        let results = poly_extensions.par_iter().zip(copoly_extensions.par_iter()).map(|(polys, eqpolys)| {
            let tmp = (0..polys[0].items_len()).into_par_iter().map(|i| {
                folded(&polys.iter().map(|p| p[i]).chain(eqpolys.iter().map(|ep| ep[i])).collect_vec())
            }).collect::<Vec<_>>();
            tmp.par_iter().sum()
        }).collect::<Vec<F>>();

        UniPoly::from_evals(&results)
    }

    fn final_evals(&self) -> Vec<F> {
        self.polys.par_iter().map(|poly| poly[0]).collect()
    }
}

impl<F: PrimeField> Protocol<F> for SumcheckPolyMap<F> {
    type Prover = SumcheckPolyMapProver<F>;
    type Verifier = SumcheckPolyMapVerifier<F>;
    type ClaimsToReduce = MultiEvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type WitnessInput = Vec<FragmentedPoly<F>>;
    type Trace = Vec<Vec<FragmentedPoly<F>>>;
    type WitnessOutput = Vec<FragmentedPoly<F>>;
    type Proof = SumcheckPolyMapProof<F>;
    type Params = SumcheckPolyMapParams<F>;

    fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
        let out = FragmentedPoly::map_over_poly(&args, params.f.clone());
        (vec![args], out)
    }
}

impl<F: PrimeField> ProtocolProver<F> for SumcheckPolyMapProver<F> {
    type ClaimsToReduce = MultiEvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type Proof = SumcheckPolyMapProof<F>;
    type Params = SumcheckPolyMapParams<F>;
    type Trace = Vec<Vec<FragmentedPoly<F>>>;

    fn start(claims_to_reduce: Self::ClaimsToReduce, args: Self::Trace, params: &Self::Params) -> Self {
        assert_eq!(args[0].len(), params.f.num_i);

        Self {
            sumcheckable: None,
            polys: Some(args[0].clone()),
            mapping: params.f.clone(),
            claims: claims_to_reduce,
            ev_folded: None,
            num_vars: params.num_vars,
            rs: vec![],
            round_polys: Some(vec![]),
        }
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T) -> Option<(Self::ClaimsNew, Self::Proof)> {
        match &mut self.sumcheckable {
            None => {
                let gamma = challenge.value;
                let gamma_pows = make_gamma_pows(&self.claims, gamma);


                let polys = self.polys.take().unwrap();
                let shape = polys[0].shape.clone();
                self.sumcheckable = Some(Box::new(FragmentedLincomb {
                    polys,
                    copolys: self.claims.points.par_iter().map(|r| {let mut eq = EqPoly::new(r.clone()); eq.take_shape(shape.clone()); Box::new(eq) as Box<dyn Copolynomial<F> + Send + Sync>}).collect(),
                    splits: None,
                    folded_f: Some(make_folded_f(&self.claims, &gamma_pows, &self.mapping)),
                    degree: self.mapping.degree,
                }));
            }
            Some(s) => {
                let r_j = challenge.value;
                fix_var_bot(&mut self.rs, r_j);
                s.bind(&r_j);

                if self.rs.len() == self.num_vars {
                    let final_evaluations: Vec<F> =s.final_evals();

                    transcript.append_scalars(b"sumcheck_final_evals", &final_evaluations[0..self.mapping.num_i]);

                    return Some((
                        EvalClaim{
                            point: self.rs.clone(),
                            evs: final_evaluations[0..self.mapping.num_i].to_vec(),
                        },
                        SumcheckPolyMapProof{
                            round_polys : self.round_polys.take().unwrap(),
                            final_evaluations : final_evaluations[0..self.mapping.num_i].to_vec(),
                        }
                    ))
                }
            }
        }

        let round_uni_poly = self.sumcheckable.as_mut().unwrap().unipoly();

        // append the prover's message to the transcript
        transcript.append_scalars(b"poly", &round_uni_poly.as_vec());
        // and to proof
        self.round_polys.as_mut().unwrap().push(round_uni_poly.compress());

        None

    }
}

// Polyfill

pub struct LameSumcheckPolyMap<F: PrimeField> {
    _marker: PhantomData<F>,
}

pub struct LameSumcheckPolyMapProver<F: PrimeField> {
    polys : Vec<DensePolynomial<F>>,
    round_polys : Option<Vec<CompressedUniPoly<F>>>,
    rs: Vec<F>,
    f: PolynomialMapping<F>,
    f_folded: Option<Arc<dyn Fn(&[F]) -> F + Sync + Send>>,
    claims: MultiEvalClaim<F>,
    ev_folded: Option<F>,
    num_vars: usize,
}

pub struct SumcheckPolyMapVerifier<F: PrimeField> {
    f: PolynomialMapping<F>,
    num_vars: usize,
    proof: SumcheckPolyMapProof<F>,
    claims_to_reduce: MultiEvalClaim<F>,

    f_folded: Option<Arc<dyn Fn(&[F]) -> F + Sync + Send>>,
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

pub fn to_multieval<F: PrimeField>(claim: EvalClaim<F>) -> MultiEvalClaim<F> {
    let points = vec![claim.point];
    let evs = vec![(0..).zip(claim.evs.into_iter()).collect()];
    MultiEvalClaim{points, evs}
}

impl<F: PrimeField> Protocol<F> for LameSumcheckPolyMap<F> {
    type Prover = LameSumcheckPolyMapProver<F>;

    type Verifier = SumcheckPolyMapVerifier<F>;

    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type WitnessInput = Vec<FragmentedPoly<F>>;

    type Trace = Vec<Vec<FragmentedPoly<F>>>;

    type WitnessOutput = Vec<FragmentedPoly<F>>;

    type Proof = SumcheckPolyMapProof<F>;

    type Params = SumcheckPolyMapParams<F>;

    fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
        let _args = Vec::<_>::interop_into(args.clone());
        let out = Vec::<_>::interop_from(map_over_poly_legacy(&_args, |x|(params.f.exec)(x)));
        (vec![args], out)
    }
}

impl<F: PrimeField> ProtocolProver<F> for LameSumcheckPolyMapProver<F> {
    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type Proof = SumcheckPolyMapProof<F>;

    type Params = SumcheckPolyMapParams<F>;

    type Trace = Vec<Vec<FragmentedPoly<F>>>;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        mut args: Self::Trace,
        params: &Self::Params,
    ) -> Self {
        assert_eq!(args[0].len(), params.f.num_i);
        let mut args = Vec::<_>::interop_into(args);

        let eqs_iter = claims_to_reduce
            .points
            .iter()
            .map(|r|
                DensePolynomial::new(EqPolynomial::new(r.clone()).evals())
            );

        args[0].extend(eqs_iter);

        Self {
            polys: args.pop().unwrap(),
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
        #[cfg(feature = "prof")]
        prof!("SumcheckPolyMapProver::round");

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
            fix_var_bot(rs, r_j);

            // bound all tables to the verifier's challenege
            for poly in polys.iter_mut() {
                poly.bound_poly_var_bot(&r_j)
            }

            if rs.len() == *num_vars {
                let final_evaluations: Vec<F> = polys.par_iter().map(|poly| poly[0]).collect();

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

        let mut accum = vec![vec![F::zero(); combined_degree + 1]; mle_half];
        #[cfg(feature = "multicore")]
        let iterator = (0..mle_half).into_par_iter();

        #[cfg(not(feature = "multicore"))]
        let iterator = 0..mle_half;

        let comb_func = f_folded.as_ref().unwrap();

        let accum: Vec<Vec<F>> = iterator
            .map(|poly_term_i| {
                #[cfg(feature = "prof")]
                prof!("SumcheckPolyMapProver::accum_aggr");

                let idx_zero = 2 * poly_term_i;
                let idx_one = 1 + 2 * poly_term_i;

                let diffs: Vec<F> = polys.par_iter().map(|p| p[idx_one] - p[idx_zero]).collect();
                let mut accum = vec![F::zero(); combined_degree + 1];
                // Evaluate P({0, ..., |g(r)|})

                // TODO(#28): Optimize
                // Tricks can be used here for low order bits {0,1} but general premise is a running sum for each
                // of the m terms in the Dense multilinear polynomials. Formula is:
                // half = | D_{n-1} | / 2
                // D_n(index, r) = D_{n-1}[half + index] + r * (D_{n-1}[half + index] - D_{n-1}[index])

                // eval 0: bound_func is A(low)
                // eval_points[0] += comb_func(&polys.par_iter().map(|poly| poly[poly_term_i]).collect());
                let eval_at_zero: Vec<F> = polys.par_iter().map(|p| p[idx_zero]).collect();
                accum[0] += comb_func(&eval_at_zero);

                // TODO(#28): Can be computed from prev_round_claim - eval_point_0
                let eval_at_one: Vec<F> = polys.par_iter().map(|p| p[idx_one]).collect();
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

        #[cfg(feature = "prof")]
        let guard = prof_guard!("SumcheckPolyMapProver::eval_points_collection");

        #[cfg(feature = "multicore")]
        eval_points
            .par_iter_mut()
            .enumerate()
            .for_each(|(poly_i, eval_point)| {
            *eval_point = accum
                .par_iter()
                .map(|mle| mle[poly_i])
                .sum::<F>();
            });

        #[cfg(not(feature = "multicore"))]
        for (poly_i, eval_point) in eval_points.iter_mut().enumerate() {
            for mle in accum.iter().take(mle_half) {
            *eval_point += mle[poly_i];
            }
        }

        #[cfg(feature = "prof")]
        drop(guard);

        let round_uni_poly = UniPoly::from_evals(&eval_points);

        // append the prover's message to the transcript
        transcript.append_scalars(b"poly", &round_uni_poly.as_vec());
        // and to proof
        round_polys.push(round_uni_poly.compress());

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

        assert_eq!(
            claims_to_reduce.evs.len(), num_points,
            "Verifier failure. Claim ill-formed: number of points {} != number of evaluation groups {}", num_points, claims_to_reduce.evs.len()
        );

        for (i, point) in claims_to_reduce.points.iter().enumerate() {
            assert_eq!(
                point.len(), num_vars,
                "Verifier failure. Claim ill-formed: point {} has num variables {}, but declared num variables is {}", i, point.len(), num_vars
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

        assert_eq!(proof.round_polys.len(), num_vars);
        assert_eq!(proof.final_evaluations.len(), num_ins);

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

            let current_sum = current_sum.as_mut().unwrap();
            let r_j = challenge.value;
            fix_var_bot(rs, r_j);

            sumcheck_round_idx = rs.len();

            // This unwrap never fails, because rounds after 0th always have the poly (which is last prover's message).
            let current_poly = current_poly.as_ref().unwrap();
            assert_eq!(
                current_poly.degree(), f.degree + 1,
                "Verifier failure: polynomial degree {} at round {} incorrect", current_poly.degree(), sumcheck_round_idx
            );

            *current_sum = current_poly.evaluate(&r_j);

            if rs.len() == *num_vars {

                transcript.append_scalars(b"sumcheck_final_evals", &final_evaluations[0..f.num_i]);

                // Cloning final evals to not change the proof. We probably do not need it, as we consume it anyway.
                let mut args = final_evaluations.clone();
                args.extend(claims_to_reduce.points.iter().map(|p| EqPolynomial::new(p.to_vec()).evaluate(&rs)));

                assert_eq!((f_folded.as_ref().unwrap())(&args), *current_sum, "Verifier failure: final check incorrect");

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
        -> Arc<dyn Fn(&[F]) -> F + Send + Sync>
{
    let claims = claims.clone();
    let gamma_pows = gamma_pows.to_vec();
    let PolynomialMapping{exec, degree: _, num_i, num_o: _} = f.clone();
    Arc::new(
        move |args: &[F]| {
            #[cfg(feature = "prof")]
            prof!("SumcheckPolyMapProver::folded_f");

            let (args, eqpolys) = args.split_at(num_i);
            let out = exec(args);
            let mut i = 0;
            claims.evs.iter().enumerate().fold(
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
    use std::sync::{Arc, OnceLock};
    use ark_bls12_381::G1Projective;
    use ark_bls12_381::Fr;
    use ark_std::{test_rng, UniformRand};
    use itertools::Itertools;

    use liblasso::utils::test_lib::TestTranscript;
    use merlin::Transcript;
    use crate::grand_add::affine_twisted_edwards_add_l1;
    use crate::polynomial::fragmented::{Fragment, FragmentContent, FragmentedPoly, Shape};

    use crate::transcript::{IndexedProofTranscript, TranscriptSender};

    use super::*;

    #[test]
    fn test_sumcheck_lite_simple_shape() {
        let gen = &mut test_rng();

        let num_vars: usize = 5;
        let shape = Arc::new(OnceLock::new());
        shape.get_or_init(||Shape::new(vec![Fragment {
            mem_idx: 0,
            len: 1 << 5,
            content: FragmentContent::Data,
            start: 0,
        }], 0));
        let polys: Vec<FragmentedPoly<Fr>> = (0..3).map(|_| FragmentedPoly::rand_with_shape(gen, shape.clone())).collect();

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

        let (e_trace, e_image_polys) = LameSumcheckPolyMap::witness(polys.clone(), &params);
        let (trace, image_polys) = SumcheckPolyMap::witness(polys.clone(), &params);

        assert_eq!(e_trace, trace);
        assert_eq!(e_image_polys.iter().map(|p| p.vec()).collect_vec(), image_polys.iter().map(|p| p.vec()).collect_vec());

        let point: Vec<Fr> = (0..(num_vars as u64)).map(|i| Fr::from(i * 13)).collect();
        let claims : Vec<_> = image_polys.par_iter().enumerate().map(|(i, p)| (i, p.evaluate(&point))).collect();

        let _point = point.clone();

        let multiclaim = MultiEvalClaim {
            points: vec![point],
            evs: vec![claims.clone()],
        };


        let mut e_prover = LameSumcheckPolyMapProver::start(
            multiclaim.clone(),
            e_trace,
            &params,
        );

        let mut prover = SumcheckPolyMapProver::start(
            multiclaim.clone(),
            trace,
            &params,
        );

        let mut e_p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
        let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
        let gamma_c = p_transcript.challenge_scalar(b"challenge_combine_outputs");
        let mut e_res = e_prover.round(gamma_c, &mut e_p_transcript);
        let mut res = prover.round(gamma_c, &mut p_transcript);
        while res.is_none() {
            let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
            e_res = e_prover.round(challenge, &mut e_p_transcript);
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
        let mut res = verifier.round(gamma_c, &mut v_transcript);
        while res.is_none() {
            let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
            res = verifier.round(challenge, &mut v_transcript);
        }

        println!("{:?}", v_transcript.transcript.log);

        v_transcript.transcript.assert_end();

        let EvalClaim{point: proof_point, evs} = res.unwrap();
        assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

    }
    #[test]
    fn test_sumcheck_lite() {
        let gen = &mut test_rng();

        let num_vars: usize = 5;
        let shape = Arc::new(OnceLock::new());
        shape.get_or_init(||Shape::rand(gen, num_vars));
        let polys: Vec<FragmentedPoly<Fr>> = (0..3).map(|_| FragmentedPoly::rand_with_shape(gen, shape.clone())).collect();

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

        let (e_trace, e_image_polys) = LameSumcheckPolyMap::witness(polys.clone(), &params);
        let (trace, image_polys) = SumcheckPolyMap::witness(polys.clone(), &params);

        assert_eq!(e_trace, trace);
        assert_eq!(e_image_polys.iter().map(|p| p.vec()).collect_vec(), image_polys.iter().map(|p| p.vec()).collect_vec());

        let point: Vec<Fr> = (0..(num_vars as u64)).map(|i| Fr::from(i * 13)).collect();
        let claims : Vec<_> = image_polys.iter().enumerate().map(|(i, p)| (i, p.evaluate(&point))).collect();

        let _point = point.clone();

        let multiclaim = MultiEvalClaim {
            points: vec![point],
            evs: vec![claims.clone()],
        };


        let mut e_prover = LameSumcheckPolyMapProver::start(
            multiclaim.clone(),
            e_trace,
            &params,
        );

        let mut prover = SumcheckPolyMapProver::start(
            multiclaim.clone(),
            trace,
            &params,
        );

        let mut e_p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
        let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
        let gamma_c = p_transcript.challenge_scalar(b"challenge_combine_outputs");
        let mut e_res = e_prover.round(gamma_c, &mut e_p_transcript);
        let mut res = prover.round(gamma_c, &mut p_transcript);
        while res.is_none() {
            let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
            e_res = e_prover.round(challenge, &mut e_p_transcript);
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
        let mut res = verifier.round(gamma_c, &mut v_transcript);
        while res.is_none() {
            let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
            res = verifier.round(challenge, &mut v_transcript);
        }

        println!("{:?}", v_transcript.transcript.log);

        v_transcript.transcript.assert_end();

        let EvalClaim{point: proof_point, evs} = res.unwrap();
        assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

    }

    #[test]
    fn test_sumcheck_multiclaim() {
        let gen = &mut test_rng();

        let num_vars: usize = 5;
        let num_points: usize = 3;
        let num_polys: usize = 4;
        let poly_eval_matrix = vec![
            vec![1, 1, 0, 1, 0],
            vec![1, 0, 1, 1, 0],
            vec![1, 1, 0, 0, 1],
        ];
        let shape = Arc::new(OnceLock::new());
        shape.get_or_init(||Shape::rand(gen, num_vars));
        let polys: Vec<FragmentedPoly<Fr>> = (0..num_polys).map(|j| FragmentedPoly::rand_with_shape(gen, shape.clone())).collect();

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
        let mut res = verifier.round(gamma_c, &mut v_transcript);
        while res.is_none() {
            let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
            res = verifier.round(challenge, &mut v_transcript);
        }

        println!("{:?}", v_transcript.transcript.log);

        v_transcript.transcript.assert_end();

        let EvalClaim{point: proof_point, evs} = res.unwrap();
        assert_eq!(evs, polys.iter().map(|p| p.evaluate(&proof_point)).collect_vec());
    }
}
