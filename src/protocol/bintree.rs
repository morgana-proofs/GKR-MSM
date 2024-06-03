use std::{collections::VecDeque, marker::PhantomData, sync::Arc};

use ark_ff::PrimeField;
use itertools::{Either, Itertools};
#[cfg(feature = "prof")]
use profi::prof;

use crate::{protocol::{protocol::{EvalClaim, MultiEvalClaim, PolynomialMapping, Protocol, ProtocolProver, ProtocolVerifier}, sumcheck::{SumcheckPolyMap, SumcheckPolyMapParams, SumcheckPolyMapProof, SumcheckPolyMapProver, SumcheckPolyMapVerifier, to_multieval}, split::{Split, SplitProver, SplitVerifier}}, transcript::{Challenge, TranscriptReceiver}};
use crate::poly::NestedPolynomial;

#[derive(Clone)]
pub enum Layer<F: PrimeField> {
    Mapping(PolynomialMapping<F>),
    Split(usize),
}

impl<F: PrimeField> Layer<F> {
    pub fn new_split(num_polys: usize) -> Self {
        Layer::Split(num_polys)
    }

    pub fn new_pmap(f: Box<dyn Fn(&[F]) -> Vec<F> + Send + Sync>, degree: usize, num_i: usize, num_o: usize) -> Self {
        Layer::Mapping(
            PolynomialMapping {
                exec: Arc::new(f),
                degree,
                num_i,
                num_o
            }
        )
    }

    pub fn num_i(&self) -> usize {
        match self {
            Self::Mapping(PolynomialMapping{num_i, ..}) => *num_i,
            Self::Split(n) => *n,
        }
    }

    pub fn num_o(&self) -> usize {
        match self {
            Self::Mapping(PolynomialMapping{num_o, ..}) => *num_o,
            Self::Split(n) => 2 * n,
        }
    }

    pub fn layer_wtns(&self, num_vars: usize, input: Vec<NestedPolynomial<F>>) -> (Vec<Vec<NestedPolynomial<F>>>, Vec<NestedPolynomial<F>>) {
        match self {
            Self::Mapping(f) => {
                SumcheckPolyMap::witness(
                    input,
                    &SumcheckPolyMapParams{num_vars, f: f.clone()}
                )
            },
            Self::Split(_) => {
                Split::witness(input, &())
            }
        }
    }

}


pub enum LayerProof<F: PrimeField> {
    Mapping(SumcheckPolyMapProof<F>),
    Split,
}

pub struct BintreeParams<F: PrimeField> {
    pub layers: Vec<Layer<F>>,
    pub num_vars: usize,
}

impl<F: PrimeField> BintreeParams<F> {
    pub fn new(layers: Vec<Layer<F>>, num_vars: usize) -> Self {
        Self {layers, num_vars}
    }

    pub fn unroll(&self) -> Vec<(Layer<F>, usize)> {
        let mut num_vars = self.num_vars;
        let mut last_num_o = None;

        let ret : Vec<_> = self.layers.iter().map(|layer| {

            let layer = layer.clone();

            let mut split_flag = false;


            let (num_i, num_o) = (layer.num_i(), layer.num_o());

            match &layer {
                Layer::Split(_) => split_flag = true,
                _ => (),
            }

            let tmp = (layer, num_vars);

            if split_flag {
                assert!(num_vars > 0, "Can not split 0-variable vector.");
                num_vars -= 1;
            }

            match last_num_o {
                None => (),
                Some(o) => {
                    assert!(o == num_i, "Amount of inputs differs from amount of outputs");
                    last_num_o = Some(num_o);
                }
            }

            tmp
        }).collect();

        match ret.last().unwrap() {
            (Layer::Split(_), _) => panic!("Technical condition: split can not be last operation."),
            _ => (),
        };

        ret
    }

}


pub struct Bintree<F: PrimeField> {
    _marker: PhantomData<F>,
}

pub struct BintreeProver<F: PrimeField> {
    proofs: Option<VecDeque<LayerProof<F>>>,
    trace: Vec<Vec<NestedPolynomial<F>>>,
    params: Vec<(Layer<F>, usize)>,
    current_claims: Option<Either<MultiEvalClaim<F>, EvalClaim<F>>>,
    current_prover: Option<Either<SumcheckPolyMapProver<F>, SplitProver<F>>>,
}

pub struct BintreeVerifier<F: PrimeField> {
    proofs: VecDeque<LayerProof<F>>,
    params: Vec<(Layer<F>, usize)>,
    current_claims: Option<Either<MultiEvalClaim<F>, EvalClaim<F>>>,
    current_verifier: Option<Either<SumcheckPolyMapVerifier<F>, SplitVerifier<F>>>,
}

pub type BintreeProof<F> = VecDeque<LayerProof<F>>;

impl<F: PrimeField> Protocol<F> for Bintree<F> {
    type Prover = BintreeProver<F>;

    type Verifier = BintreeVerifier<F>;

    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type WitnessInput = Vec<NestedPolynomial<F>>;

    type Trace = Vec<Vec<NestedPolynomial<F>>>;

    type WitnessOutput = Vec<NestedPolynomial<F>>;

    type Proof = BintreeProof<F>;

    type Params = BintreeParams<F>;

    fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
        let mut trace = vec![];
        let num_vars = params.num_vars;
        assert_eq!(args[0].num_vars(), num_vars);
        let layers = params.unroll();
        assert_eq!(layers[0].0.num_i(), args.len());

        let mut layer_trace;
        let mut output = args;

        for (layer, curr_num_vars) in layers {
            (layer_trace, output) = layer.layer_wtns(curr_num_vars, output);
            trace.extend(layer_trace)
        }

        (trace, output)
    }
}

impl<F: PrimeField> ProtocolProver<F> for BintreeProver<F> {
    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type Proof = VecDeque<LayerProof<F>>;

    type Params = BintreeParams<F>;

    type Trace = Vec<Vec<NestedPolynomial<F>>>;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        args: Self::Trace,
        params: &Self::Params,
    ) -> Self {

        Self {
            proofs: Some(VecDeque::new()),
            trace: args,
            params: params.unroll(),
            current_claims: Some(Either::Left(claims_to_reduce)),
            current_prover: None,
        }
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
        ->
    Option<(Self::ClaimsNew, Self::Proof)> {
        #[cfg(feature = "prof")]
        prof!("BintreeProver::round");

        let Self{proofs, trace, params, current_claims, current_prover} = self;

        match current_prover {
            None => {
                let current_trace = trace.pop().unwrap();
                let (current_params, current_num_vars) = params.pop().unwrap();
                *current_prover = Some(
                    match current_params {
                        Layer::Mapping(f) => {
                            let _current_claims = match current_claims.take().unwrap() {
                                Either::Left(c) => c,
                                Either::Right(c) => to_multieval(c),
                            };

                            Either::Left(SumcheckPolyMapProver::start(
                                _current_claims.clone(),
                                vec![current_trace],
                                &SumcheckPolyMapParams{f, num_vars: current_num_vars}
                            ))
                        },
                        Layer::Split(_) => {
                            let _current_claims = match current_claims.take().unwrap() {
                                Either::Right(c) => c,
                                Either::Left(_) => panic!("Unexpected multi-evaluation claim."),
                            };

                            Either::Right(SplitProver::start(
                                _current_claims,
                                vec![current_trace],
                                &()
                            ))
                        }
                    }
                )
            },
            Some(_) => (),
        };

        match current_prover.as_mut().unwrap() {
            Either::Right(prover) => {
                match prover.round(challenge, transcript) {
                    None => (),
                    Some((claim, ())) => {
                        *current_claims = Some(Either::Right(claim));
                        proofs.as_mut().unwrap().push_back(LayerProof::Split);
                        *current_prover = None;
                    },
                }
            },
            Either::Left(prover) => {
                match prover.round(challenge, transcript) {
                    None => (),
                    Some((claim, proof)) => {
                        *current_claims = Some(Either::Right(claim));
                        proofs.as_mut().unwrap().push_back(LayerProof::Mapping(proof));
                        *current_prover = None;
                    }
                }
            },
        };

        if let None = current_prover.as_ref() {
            if params.len() > 0 {return None};
            if let Either::Right(claim) = current_claims.take().unwrap() {
                Some((claim, proofs.take().unwrap()))
            } else {unreachable!("Multi-eval claim found, should never happen.")}
        } else {
            None
        }
    }
}

impl<F: PrimeField> ProtocolVerifier<F> for BintreeVerifier<F> {
    type Params = BintreeParams<F>;

    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type Proof = VecDeque<LayerProof<F>>;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        proof: Self::Proof,
        params: &Self::Params,
    ) -> Self {
        Self {
            proofs: proof,
            params: params.unroll(),
            current_claims: Some(Either::Left(claims_to_reduce)),
            current_verifier: None
        }
    }

    fn round<T: TranscriptReceiver<F>>(
        &mut self,
        challenge: Challenge<F>,
        transcript: &mut T)
        ->
    Option<Self::ClaimsNew> {
        let Self { proofs, params, current_claims, current_verifier } = self;

        println!("{:?}, {:?}, {:?}, {:?}", proofs.len(), params.len(), current_claims.is_some(), current_verifier.is_some());

        match current_verifier {
            None => {
                let current_proof = proofs.pop_front().unwrap();
                let (current_params, current_num_vars) = params.pop().unwrap();
                *current_verifier = Some(
                    match current_params {
                        Layer::Mapping(f) => {
                            println!("Mapping");
                            let _current_claims = match current_claims.take().unwrap() {
                                Either::Left(c) => c,
                                Either::Right(c) => to_multieval(c),
                            };

                            let LayerProof::Mapping(_current_proof) = current_proof else {panic!()};

                            Either::Left(SumcheckPolyMapVerifier::start(
                                _current_claims,
                                _current_proof,
                                &SumcheckPolyMapParams{ f, num_vars: current_num_vars }
                            ))
                        },
                        Layer::Split(_) => {
                            println!("Split");
                            let _current_claims = match current_claims.take().unwrap() {
                                Either::Right(c) => c,
                                Either::Left(_) => panic!("Unexpected multi-evaluation claim."),
                            };

                            let LayerProof::Split = current_proof else {panic!()};

                            Either::Right(SplitVerifier::start(
                                _current_claims,
                                (),
                                &(),
                            ))

                        },
                    }
                )
            },
            Some(_) => (),
        }

        match current_verifier.as_mut().unwrap() {
            Either::Right(verifier) => {
                match verifier.round(challenge, transcript) {
                    None => (),
                    Some(claim) => {
                        *current_claims = Some(Either::Right(claim));
                        *current_verifier = None;
                    },
                }
            },
            Either::Left(verifier) => {
                match verifier.round(challenge, transcript) {
                    None => (),
                    Some(claim) => {
                        *current_claims = Some(Either::Right(claim));
                        *current_verifier = None;
                    }
                }
            },
        }

        if let None = current_verifier.as_ref() {
            if params.len() > 0 {return None};
            if let Either::Right(claim) = current_claims.take().unwrap() {
                Some(claim)
            } else {unreachable!("Multi-eval claim found, should never happen.")}
        } else {
            None
        }
    }
}


#[cfg(test)]
mod test {
    use ark_bls12_381::{Fr, G1Projective};
    use ark_std::{test_rng, UniformRand};
    use itertools::Itertools;
    use liblasso::utils::test_lib::TestTranscript;

    use crate::transcript::{IndexedProofTranscript, TranscriptSender};
    use crate::utils::{map_over_poly, split_vecs};

    use super::*;

    fn f62(v: &[Fr]) -> Vec<Fr> {
        vec![
            v[0] * v[1] * v[2],
            v[3] * v[4] * v[5],
        ]
    }

    fn f23(v: &[Fr]) -> Vec<Fr> {
        vec![
            v[0],
            v[1],
            v[0] * v[1],
        ]
    }

    fn f61(v: &[Fr]) -> Vec<Fr> {
        vec![
            v[0] * v[1] * v[2] * v[3] * v[4] * v[5],
        ]
    }

    fn f34(v: &[Fr]) -> Vec<Fr> {
        vec![
            v[1] * v[2],
            v[2] * v[0],
            v[0] * v[1],
            v[0] * v[1] * v[2],
        ]
    }

    fn f45(v: &[Fr]) -> Vec<Fr> {
        vec![
            v[1] * v[2],
            v[2] * v[3],
            v[3] * v[0],
            v[0] * v[1],
            v[0] * v[1] * v[2] * v[3],
        ]
    }

    fn f53(v: &[Fr]) -> Vec<Fr> {
        vec![
            v[0] * v[1] * v[2],
            v[2] * v[3],
            v[3] * v[4],
        ]
    }

    fn f63(v: &[Fr]) -> Vec<Fr> {
        vec![
            v[0] * v[3],
            v[1] * v[4],
            v[2] * v[5],
        ]
    }
    #[test]
    fn witness_generation() {
        let gen = &mut test_rng();

        let num_vars = 5;
        let input = (0..3).map(|_|
            NestedPolynomial::rand(gen, num_vars)
        ).collect_vec();

        let params = BintreeParams::new(
            vec![
                Layer::new_split(3),
                Layer::new_pmap(Box::new(f63), 10, 6, 3),
                Layer::new_pmap(Box::new(f34), 10, 3, 4),
                Layer::new_pmap(Box::new(f45), 10, 4, 5),
                Layer::new_pmap(Box::new(f53), 10, 5, 3),
                Layer::new_split(3),
                Layer::new_pmap(Box::new(f62), 10, 6, 2),
                Layer::new_pmap(Box::new(f23), 10, 2, 3),
                Layer::new_split(3),
                Layer::new_pmap(Box::new(f62), 10, 6, 2),
                Layer::new_pmap(Box::new(f23), 10, 2, 3),
                Layer::new_split(3),
                Layer::new_pmap(Box::new(f61), 10, 6, 1),
            ],
            5,
        );

        let (trace, output) = Bintree::witness(input.clone(), &params);
        let mut i = 0;
        trace[i].iter().zip_eq(input.iter()).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last();
        trace[i + 1].iter().zip_eq(split_vecs(&(trace[i].iter().map(|p| p.into()).collect_vec())).iter().map(|p| NestedPolynomial::from(p))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&(trace[i].iter().map(|p| p.into()).collect_vec()), f63).iter().map(|p| NestedPolynomial::from(p))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&(trace[i].iter().map(|p| p.into()).collect_vec()), f34).iter().map(|p| NestedPolynomial::from(p))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&(trace[i].iter().map(|p| p.into()).collect_vec()), f45).iter().map(|p| NestedPolynomial::from(p))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&(trace[i].iter().map(|p| p.into()).collect_vec()), f53).iter().map(|p| NestedPolynomial::from(p))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(split_vecs(&(trace[i].iter().map(|p| p.into()).collect_vec())).iter().map(|p| NestedPolynomial::from(p))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&(trace[i].iter().map(|p| p.into()).collect_vec()), f62).iter().map(|p| NestedPolynomial::from(p))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&(trace[i].iter().map(|p| p.into()).collect_vec()), f23).iter().map(|p| NestedPolynomial::from(p))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(split_vecs(&(trace[i].iter().map(|p| p.into()).collect_vec())).iter().map(|p| NestedPolynomial::from(p))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&(trace[i].iter().map(|p| p.into()).collect_vec()), f62).iter().map(|p| NestedPolynomial::from(p))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&(trace[i].iter().map(|p| p.into()).collect_vec()), f23).iter().map(|p| NestedPolynomial::from(p))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(split_vecs(&(trace[i].iter().map(|p| p.into()).collect_vec())).iter().map(|p| NestedPolynomial::from(p))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        output.iter().zip_eq(map_over_poly(&(trace[i].iter().map(|p| p.into()).collect_vec()), f61).iter().map(|p| NestedPolynomial::from(p))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        assert_eq!(i, trace.len());
    }

    #[test]
    fn prover_vs_verifier() {
        let gen = &mut test_rng();

        let num_vars = 5;
        let input = (0..3).map(|_|
            NestedPolynomial::rand(gen, num_vars)
        ).collect_vec();
        let point = (0..1).map(|_| Fr::rand(gen)).collect_vec();

        let params = BintreeParams::new(
            vec![
                Layer::new_split(3),
                Layer::new_pmap(Box::new(f63), 2, 6, 3),
                Layer::new_pmap(Box::new(f34), 3, 3, 4),
                Layer::new_pmap(Box::new(f45), 4, 4, 5),
                Layer::new_pmap(Box::new(f53), 3, 5, 3),
                Layer::new_split(3),
                Layer::new_pmap(Box::new(f62), 3, 6, 2),
                Layer::new_pmap(Box::new(f23), 2, 2, 3),
                Layer::new_split(3),
                Layer::new_pmap(Box::new(f62), 3, 6, 2),
                Layer::new_pmap(Box::new(f23), 2, 2, 3),
                Layer::new_split(3),
                Layer::new_pmap(Box::new(f61), 6, 6, 1),
            ],
            5,
        );

        let (trace, output) = Bintree::witness(input.clone(), &params);


        let claims_to_reduce = to_multieval(EvalClaim {
            evs: output.iter().map(|p| p.evaluate(&point)).collect(),
            point,
        });

        let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());

        let mut prover = BintreeProver::start(claims_to_reduce.clone(), trace, &params);
        let mut res = None;
        while res.is_none() {
            let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
            res = prover.round(challenge, &mut p_transcript);
        }
        let (EvalClaim{point: proof_point, evs: proof_evs}, proof) = res.unwrap();

        assert_eq!(proof_evs, input.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

        let mut v_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));

        let mut verifier =  BintreeVerifier::start(
            claims_to_reduce,
            proof,
            &params,
        );

        let mut res = None;
        while res.is_none() {
            let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
            res = verifier.round(challenge, &mut v_transcript);
        }
        let EvalClaim{point: verify_point, evs: verify_evs} = res.unwrap();

        assert_eq!(proof_point, verify_point);
        assert_eq!(proof_evs, verify_evs);
    }
}
