use std::{collections::VecDeque, marker::PhantomData, sync::Arc};

use ark_ff::PrimeField;
use itertools::Either;
use liblasso::poly::dense_mlpoly::DensePolynomial;

use crate::{protocol::{PolynomialMapping, Protocol, ProtocolProver, ProtocolVerifier}, sumcheck_trait::{to_multieval, EvalClaim, MultiEvalClaim, Split, SplitProver, SplitVerifier, SumcheckPolyMap, SumcheckPolyMapParams, SumcheckPolyMapProof, SumcheckPolyMapProver, SumcheckPolyMapVerifier}};

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

    pub fn layer_wtns(&self, num_vars: usize, input: Vec<DensePolynomial<F>>) -> (Vec<DensePolynomial<F>>, Vec<DensePolynomial<F>>) {
        match self {
            Self::Mapping(f) => {
                SumcheckPolyMap::witness(
                    input, 
                    &SumcheckPolyMapParams{num_vars, f: f.clone()}
                )
            },
            Self::Split(_) => {
                let (a, tmp) = Split::witness(input, &());
                let (mut b, tmp) : (Vec<_>, Vec<_>) = tmp.into_iter().unzip();
                b.extend(tmp.into_iter());
                (a, b)
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
    trace: Vec<Vec<DensePolynomial<F>>>,
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

impl<F: PrimeField> Protocol<F> for Bintree<F> {
    type Prover = BintreeProver<F>;

    type Verifier = BintreeVerifier<F>;

    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type WitnessInput = Vec<DensePolynomial<F>>;

    type Trace = Vec<Vec<DensePolynomial<F>>>;

    type WitnessOutput = Vec<DensePolynomial<F>>;

    type Proof = VecDeque<LayerProof<F>>;

    type Params = BintreeParams<F>;

    fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
        let mut trace = vec![];
        let num_vars = params.num_vars;
        assert!(args[0].num_vars == num_vars);
        let layers = params.unroll();
        assert!(layers[0].0.num_i() == args.len());

        let mut layer_trace;
        let mut output = args;

        for (layer, curr_num_vars) in layers {
            (layer_trace, output) = layer.layer_wtns(curr_num_vars, output);
            trace.push(layer_trace)
        }

        (trace, output)
    }
}

impl<F: PrimeField> ProtocolProver<F> for BintreeProver<F> {
    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type Proof = VecDeque<LayerProof<F>>;

    type Params = BintreeParams<F>;

    type Trace = Vec<Vec<DensePolynomial<F>>>;

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

    fn round<T: crate::protocol::TranscriptReceiver<F>>(&mut self, challenge: crate::protocol::Challenge<F>, transcript: &mut T)
        ->
    Option<(Self::ClaimsNew, Self::Proof)> {


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
                                current_trace,
                                &SumcheckPolyMapParams{f, num_vars: current_num_vars}
                            ))
                        },
                        Layer::Split(n) => {
                            let _current_claims = match current_claims.take().unwrap() {
                                Either::Right(c) => c,
                                Either::Left(_) => panic!("Unexpected multi-evaluation claim."),
                            };

                            let EvalClaim { point: _point, evs: _evs } = _current_claims;
                            let (e0, e1) = _evs.split_at(n);
                            let _current_claims = (
                                _point,
                                itertools::Itertools::zip_eq(
                                    e0.iter().map(|x|*x), 
                                    e1.iter().map(|x|*x)
                                ).collect()
                            );

                            Either::Right(SplitProver::start(
                                _current_claims,
                                current_trace,
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
                        *current_claims = Some(Either::Right(EvalClaim { point: claim.0, evs: claim.1 }));
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

    fn round<T: crate::protocol::TranscriptReceiver<F>>(
        &mut self,
        challenge: crate::protocol::Challenge<F>,
        transcript: &mut T)
        ->
    Option<Self::ClaimsNew> {
        let Self { proofs, params, current_claims, current_verifier } = self;

        match current_verifier {
            None => {
                let current_proof = proofs.pop_front().unwrap();
                let (current_params, current_num_vars) = params.pop().unwrap();
                *current_verifier = Some(
                    match current_params {
                        Layer::Mapping(f) => {
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
                        Layer::Split(n) => {
                            let _current_claims = match current_claims.take().unwrap() {
                                Either::Right(c) => c,
                                Either::Left(_) => panic!("Unexpected multi-evaluation claim."),
                            };

                            let EvalClaim { point: _point, evs: _evs } = _current_claims;
                            let (e0, e1) = _evs.split_at(n);
                            let _current_claims = (
                                _point,
                                itertools::Itertools::zip_eq(
                                    e0.iter().map(|x|*x), 
                                    e1.iter().map(|x|*x)
                                ).collect()
                            );

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
                        *current_claims = Some(Either::Right(EvalClaim { point: claim.0, evs: claim.1 }));
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
