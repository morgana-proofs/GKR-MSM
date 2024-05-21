use std::marker::PhantomData;
use std::os::linux::raw::stat;
use ark_ff::PrimeField;
use itertools::{Either, Itertools};
use liblasso::poly::dense_mlpoly::DensePolynomial;
use liblasso::utils::math;
use log::trace;
use crate::gkr::GKRClaim::MULTI;
use crate::gkr::GKRProverState::{SPLIT, SUMCHECK};
use crate::protocol::{IndexedProofTranscript, TranscriptReceiver, TranscriptSender, Challenge, Protocol, ProtocolProver, ProtocolVerifier, PolynomialMapping};
use crate::sumcheck_trait::{EvalClaim, MultiEvalClaim, Split, SplitProver, SumcheckPolyMap, SumcheckPolyMapParams, SumcheckPolyMapProof, SumcheckPolyMapProver};
use crate::utils::{map_over_poly, split_vecs};

pub struct GKR<F: PrimeField> {
    _pd: PhantomData<F>,
}

pub struct GKRProver<F: PrimeField> {
    next_claims: Option<GKRClaim<F>>,
    params: <Self as ProtocolProver<F>>::Params,
    proof: Option<<Self as ProtocolProver<F>>::Proof>,
    trace: <Self as ProtocolProver<F>>::Trace,
    state: GKRProverState,
    current_prover: Option<Either<SumcheckPolyMapProver<F>, SplitProver<F>>>,
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum GKRProverState {
    INIT,
    SUMCHECK(usize, usize),
    SPLIT(usize, usize),
    DONE,
}

impl GKRProverState {
    fn next<F: PrimeField>(self, params: &GKRParams<F>) -> Self {
        match self {
            GKRProverState::SUMCHECK(l, i) => match params.should_split(i - 1) {
                true => GKRProverState::SPLIT(l, i - 1),
                false => GKRProverState::SUMCHECK(l, i - 1),
            },
            GKRProverState::SPLIT(l, i) => match i {
                0 => GKRProverState::DONE,
                _ => GKRProverState::SUMCHECK(l - 1, i - 1),
            }
            GKRProverState::INIT => match params.num_layers {
                0 => GKRProverState::DONE,
                _ => GKRProverState::SUMCHECK(params.num_layers - 1, params.get_total_length() - 1),
            }
            GKRProverState::DONE => unreachable!(),
        }
    }

    fn wtns_next<F: PrimeField>(self, params: &GKRParams<F>) -> Self {
        match self {
            GKRProverState::SUMCHECK(l, i) => {
                if i + 1 == params.get_total_length() {
                    GKRProverState::INIT
                } else {
                    match params.should_split(i + 1) {
                        true => GKRProverState::SPLIT(l + 1, i + 1),
                        false => GKRProverState::SUMCHECK(l, i + 1),
                    }
                }
            },
            GKRProverState::SPLIT(l, i) => GKRProverState::SUMCHECK(l, i + 1),
            GKRProverState::INIT => unreachable!(),
            GKRProverState::DONE => match params.num_layers {
                0 => GKRProverState::INIT,
                _ => GKRProverState::SPLIT(0, 0),
            }
        }
    }
}

pub struct GKRVerifier<F: PrimeField> {
    _pd: PhantomData<F>,
}

pub struct GKRProof<F: PrimeField> {
    proofs: Vec<Either<SumcheckPolyMapProof<F>, ()>>
}

/// if mapping for first or last layer is None we assume it is the same as for the inner layer
#[derive(Clone)]
pub struct GKRMappings<F: PrimeField> {
    first_layer: Option<Vec<PolynomialMapping<F>>>,
    layer: Vec<PolynomialMapping<F>>,
    last_layer: Option<Vec<PolynomialMapping<F>>>,
}

impl<F: PrimeField> GKRMappings<F> {
    fn first_layer_length(&self) -> usize {
        match &self.first_layer {
            None => self.layer.len(),
            Some(l) => l.len(),
        }
    }

    fn last_layer_length(&self) -> usize {
        match &self.last_layer {
            None => self.layer.len(),
            Some(l) => l.len(),
        }
    }

    fn inner_layer_length(&self) -> usize {
        self.layer.len()
    }

}

/// We assume that if num layers is :
///   0         : there are no layers
///   1         : there is only first layer
///   2         : there are last and first layers
///   3 and more: there are last and first layers and n - 2 inner layers
#[derive(Clone)]
pub struct GKRParams<F: PrimeField> {
    mappings: GKRMappings<F>,
    num_layers: usize,
}

impl<F: PrimeField> GKRParams<F> {
    fn get_mappings(&self, mut state: GKRProverState) -> &PolynomialMapping<F> {
        match state {
            GKRProverState::INIT => unreachable!(),
            SUMCHECK(l, mut i) => {
                i -= l + 1;
                if i < self.mappings.first_layer_length() {
                    return match &self.mappings.first_layer {
                        None => &self.mappings.layer[i],
                        Some(l) => &l[i],
                    }
                }
                i -= self.mappings.first_layer_length();
                if i < (self.num_layers - 2) * self.mappings.inner_layer_length() {
                    return &self.mappings.layer[i % self.mappings.inner_layer_length()];
                }
                i -= (self.num_layers - 2) * self.mappings.inner_layer_length();
                match &self.mappings.last_layer {
                    None => &self.mappings.layer[i],
                    Some(l) => &l[i],
                }
            }
            SPLIT(_, _) => panic!("Attempt to get mapping for split operation"),
            GKRProverState::DONE => unreachable!(),
        }
    }

    fn get_total_length(&self) -> usize {
        let mut total = 0;
        if self.num_layers == 0 {
            return total;
        }
        total += 1;
        total += self.mappings.first_layer_length();
        if self.num_layers == 1 {
            return total;
        }
        total += 1;
        total += self.mappings.last_layer_length();
        if self.num_layers == 2 {
            return total;
        }
        total += self.num_layers - 2;
        total + self.mappings.inner_layer_length() * (self.num_layers - 2)
    }

    fn should_split(&self, mut idx: usize) -> bool {
        if idx == 0 {
            return true;
        }
        idx -= 1;
        if idx < self.mappings.first_layer_length() {
            return false;
        }
        idx -= self.mappings.first_layer_length();
        if idx % (self.mappings.inner_layer_length() + 1) == 0 {
            return true
        }
        if idx < (self.mappings.inner_layer_length() + 1) * (self.num_layers - 2) {
            return false;
        }
        idx -= (self.mappings.inner_layer_length() + 1) * (self.num_layers - 2);
        idx == self.mappings.last_layer_length() + 1
    }
}

pub enum GKRClaim<F: PrimeField> {
    MULTI(MultiEvalClaim<F>),
    SINGLE(EvalClaim<F>),
}

impl<F: PrimeField> GKRClaim<F> {
    fn multiply(self) -> Self {
        match self {
            GKRClaim::SINGLE(c) => {
                let EvalClaim { point, evs } = c;
                GKRClaim::MULTI(MultiEvalClaim {
                    points: vec![point],
                    evs: vec![evs.into_iter().enumerate().collect_vec()],
                })
            },
            _ => self,
        }
    }
}


impl<F: PrimeField> Protocol<F> for GKR<F> {
    type Prover = GKRProver<F>;
    type Verifier = GKRVerifier<F>;
    type ClaimsToReduce = MultiEvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type WitnessInput = Vec<DensePolynomial<F>>;

    type Trace = Vec<Vec<DensePolynomial<F>>>;
    type WitnessOutput = Vec<DensePolynomial<F>>;
    type Proof = GKRProof<F>;
    type Params = GKRParams<F>;

    fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
        let mut state = GKRProverState::DONE.wtns_next(params);
        let mut trace = vec![];
        let mut next_layer = args;
        while state != GKRProverState::INIT {
            println!("{:?}", state);
            match state {
                SUMCHECK(_, idx) => {
                    let (t, o) = SumcheckPolyMap::witness(next_layer, &SumcheckPolyMapParams {
                        f: GKR::get_current_mapping(params, state).clone(),
                        num_vars: 0,
                    });
                    trace.push(t);
                    next_layer = o;
                },
                SPLIT(_, _) => {
                    let (t, o) = Split::witness(next_layer, &());
                    trace.push(t);
                    let (mut tmp, right): (Vec<DensePolynomial<F>>, Vec<DensePolynomial<F>>) = o.into_iter().unzip();
                    tmp.extend(right);
                    next_layer = tmp;
                },
                _ => unreachable!(),
            };
            state = state.wtns_next(params);
        }
        (trace, next_layer)
    }
}

impl<F: PrimeField> GKR<F> {
    fn get_current_input(trace: &<Self as Protocol<F>>::Trace, state: GKRProverState) -> &Vec<DensePolynomial<F>> {
        match state {
            GKRProverState::INIT => unreachable!(),
            SUMCHECK(_, idx) => trace.get(idx).unwrap(),
            SPLIT(_, idx) => trace.get(idx).unwrap(),
            GKRProverState::DONE => unreachable!(),
        }
    }

    fn get_current_mapping(params: &<Self as Protocol<F>>::Params, state: GKRProverState) -> &PolynomialMapping<F> {
        params.get_mappings(state)
    }
}

impl<F: PrimeField> ProtocolProver<F> for GKRProver<F> {
    type ClaimsToReduce = MultiEvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type Proof = GKRProof<F>;
    type Params = GKRParams<F>;
    type Trace = Vec<Vec<DensePolynomial<F>>>;
    fn start(claims_to_reduce: Self::ClaimsToReduce, args: Self::Trace, params: &Self::Params) -> Self {
        Self {
            next_claims: Some(GKRClaim::MULTI(claims_to_reduce)),
            proof: Some(Self::Proof {
                proofs: vec![],
            }),
            params: params.clone(),
            trace: args,
            state: GKRProverState::INIT.next(params),
            current_prover: None,
        }
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T) -> Option<(Self::ClaimsNew, Self::Proof)> {
        let Self {next_claims, state, params, trace, proof, current_prover} = self;


        match current_prover {
            None => {
                match state {
                    GKRProverState::INIT => unreachable!(),
                    SUMCHECK(_, _) => {
                        let GKRClaim::MULTI(claims) = next_claims.take().unwrap().multiply() else { unreachable!() };
                        *current_prover = Some(Either::Left(SumcheckPolyMapProver::start(
                            claims,
                            trace.pop().unwrap(),
                            &SumcheckPolyMapParams {
                                f: GKR::get_current_mapping(params, *state).clone(),
                                num_vars: 0,
                            },
                        )));
                    }
                    SPLIT(_, _) => {
                        let GKRClaim::SINGLE(claims) = next_claims.take().unwrap() else { unreachable!() };
                        let EvalClaim { point: _point, evs: _evs } = claims;
                        assert_eq!(_evs.len() % 2, 0);
                        let (e0, e1) = _evs.split_at(_evs.len() / 2);
                        let _current_claims = (
                            _point,
                            itertools::Itertools::zip_eq(
                                e0.iter().map(|x|*x),
                                e1.iter().map(|x|*x)
                            ).collect()
                        );

                        *current_prover = Some(Either::Right(SplitProver::start(
                            _current_claims,
                            trace.pop().unwrap(),
                            &()
                        )));
                    }
                    GKRProverState::DONE => {
                        if *state == GKRProverState::DONE {
                            let GKRClaim::SINGLE(claims) = next_claims.take().unwrap() else { unreachable!() };
                            return Some((claims, proof.take().unwrap()))
                        }
                    }
                }
                *state = state.next(params);
            }
            Some(prover) => {
                let Some(proof) = proof else { unreachable!() };
                match prover {
                    Either::Left(sumcheck) => {
                        match sumcheck.round(challenge, transcript) {
                            None => {}
                            Some((eval, part_proof)) => {
                                proof.proofs.push(Either::Left(part_proof));
                                *next_claims = Some(GKRClaim::SINGLE(eval));
                            }
                        }
                    }
                    Either::Right(split) => {
                        match split.round(challenge, transcript) {
                            None => {}
                            Some((eval, part_proof)) => {
                                proof.proofs.push(Either::Right(part_proof));
                                *next_claims = Some(GKRClaim::SINGLE(EvalClaim {
                                    point: eval.0,
                                    evs: eval.1,
                                }))
                            }
                        }
                    }
                }
            }
        }
        None
    }
}

impl<F: PrimeField> ProtocolVerifier<F> for GKRVerifier<F> {
    type Params = GKRParams<F>;
    type ClaimsToReduce = MultiEvalClaim<F>;
    type ClaimsNew = EvalClaim<F>;
    type Proof = GKRProof<F>;

    fn start(claims_to_reduce: Self::ClaimsToReduce, proof: Self::Proof, params: &Self::Params) -> Self {
        todo!()
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T) -> Option<Self::ClaimsNew> {
        todo!()
    }
}

#[cfg(test)]
mod test {
    use std::sync::Arc;
    use ark_bls12_381::{Fr, G1Projective};
    use ark_std::{test_rng, UniformRand, Zero};
    use itertools::Itertools;
    use liblasso::utils::test_lib::TestTranscript;
    use crate::bintree::{Bintree, BintreeParams, BintreeProver, Layer};
    use crate::sumcheck_trait::to_multieval;
    use super::*;

    #[test]
    fn test_state_iteration() {
        let s = GKRProverState::INIT;
        let mut params = GKRParams::<Fr> {
            mappings: GKRMappings {
                first_layer: None,
                layer: vec![],
                last_layer: None,
            },
            num_layers: 0,
        };
        let mut t = vec![s];
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::DONE);

        let mut rt = GKRProverState::DONE;
        for st in t.into_iter().rev().skip(1) {
            rt = rt.wtns_next(&params);
            assert_eq!(st, rt);
        }

        params = GKRParams::<Fr> {
            mappings: GKRMappings {
                first_layer: None,
                layer: vec![
                    PolynomialMapping {
                        exec: Arc::new(|v| vec![v[0] * v[2], v[1] * v[2]]),
                        degree: 2,
                        num_i: 3,
                        num_o: 2,
                    },
                    PolynomialMapping {
                        exec: Arc::new(|v| vec![v[0], v[1], v[0] * v[1]]),
                        degree: 2,
                        num_i: 2,
                        num_o: 3,
                    },
                ],
                last_layer: None,
            },
            num_layers: 1,
        };
        t = vec![s];
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(0, 2));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(0, 1));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(0, 0));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::DONE);

        rt = GKRProverState::DONE;
        for st in t.into_iter().rev().skip(1) {
            rt = rt.wtns_next(&params);
            assert_eq!(st, rt);
        }

        params = GKRParams::<Fr> {
            mappings: GKRMappings {
                first_layer: None,
                layer: vec![
                    PolynomialMapping {
                        exec: Arc::new(|v| vec![v[0] * v[2], v[1] * v[2]]),
                        degree: 2,
                        num_i: 3,
                        num_o: 2,
                    },
                    PolynomialMapping {
                        exec: Arc::new(|v| vec![v[0], v[1], v[0] * v[1]]),
                        degree: 2,
                        num_i: 2,
                        num_o: 3,
                    },
                ],
                last_layer: None,
            },
            num_layers: 2,
        };
        t = vec![s];
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(1, 5));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(1, 4));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(1, 3));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(0, 2));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(0, 1));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(0, 0));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::DONE);

        rt = GKRProverState::DONE;
        for st in t.iter().rev().skip(1) {
            rt = rt.wtns_next(&params);
            assert_eq!(st, &rt);
        }

        params = GKRParams::<Fr> {
            mappings: GKRMappings {
                first_layer: None,
                layer: vec![
                    PolynomialMapping {
                        exec: Arc::new(|v| vec![v[0] * v[2], v[1] * v[2]]),
                        degree: 2,
                        num_i: 3,
                        num_o: 2,
                    },
                    PolynomialMapping {
                        exec: Arc::new(|v| vec![v[0], v[1], v[0] * v[1]]),
                        degree: 2,
                        num_i: 2,
                        num_o: 3,
                    },
                ],
                last_layer: None,
            },
            num_layers: 7,
        };
        t = vec![s];
        for i in (0..7).rev() {
            t.push(t.last().unwrap().next(&params));
            assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(i, 3 * i + 2));
            t.push(t.last().unwrap().next(&params));
            assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(i, 3 * i + 1));
            t.push(t.last().unwrap().next(&params));
            assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(i, 3 * i));
        }
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::DONE);

        rt = GKRProverState::DONE;
        for st in t.iter().rev().skip(1) {
            rt = rt.wtns_next(&params);
            assert_eq!(st, &rt);
        }

        params = GKRParams::<Fr> {
            mappings: GKRMappings {
                first_layer: Some(vec![
                    PolynomialMapping {
                        exec: Arc::new(|v| vec![v[0] * v[2], v[1] * v[2]]),
                        degree: 2,
                        num_i: 3,
                        num_o: 2,
                    },
                    PolynomialMapping {
                        exec: Arc::new(|v| vec![v[0], v[1], v[0] * v[1]]),
                        degree: 2,
                        num_i: 2,
                        num_o: 3,
                    },
                    PolynomialMapping {
                        exec: Arc::new(|v| vec![v[0] * v[2], v[1] * v[2]]),
                        degree: 2,
                        num_i: 3,
                        num_o: 2,
                    },
                    PolynomialMapping {
                        exec: Arc::new(|v| vec![v[0], v[1], v[0] * v[1]]),
                        degree: 2,
                        num_i: 2,
                        num_o: 3,
                    },
                ]),
                layer: vec![
                    PolynomialMapping {
                        exec: Arc::new(|v| vec![v[0] * v[2], v[1] * v[2]]),
                        degree: 2,
                        num_i: 3,
                        num_o: 2,
                    },
                    PolynomialMapping {
                        exec: Arc::new(|v| vec![v[0], v[1], v[0] * v[1]]),
                        degree: 2,
                        num_i: 2,
                        num_o: 3,
                    },
                ],
                last_layer: Some(vec![
                    PolynomialMapping {
                        exec: Arc::new(|v| vec![v[0] * v[2], v[1] * v[2]]),
                        degree: 2,
                        num_i: 3,
                        num_o: 2,
                    },
                ]),
            },
            num_layers: 7,
        };
        t = vec![s];
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(6, 21));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(6, 20));
        for i in (0..5).rev() {
            t.push(t.last().unwrap().next(&params));
            assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(i + 1, 5 + i * 3 + 2));
            t.push(t.last().unwrap().next(&params));
            assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(i + 1, 5 + i * 3 + 1));
            t.push(t.last().unwrap().next(&params));
            assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(i + 1, 5 + i * 3));
        }
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(0, 4));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(0, 3));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(0, 2));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(0, 1));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(0, 0));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::DONE);

        rt = GKRProverState::DONE;
        for st in t.iter().rev().skip(1) {
            rt = rt.wtns_next(&params);
            assert_eq!(st, &rt);
        }
    }

    #[test]
    fn test_witness_generation() {
        let gen = &mut test_rng();
        fn f62(v: &[Fr]) -> Vec<Fr> {
            vec![v[0] * v[1] * v[2], v[3] * v[4] * v[5]]
        }
        let m62 = PolynomialMapping {
            exec: Arc::new(f62),
            degree: 3,
            num_i: 6,
            num_o: 2,
        };

        fn f23(v: &[Fr]) -> Vec<Fr> {
            vec![v[0], v[1], v[0] * v[1]]
        }
        let m23 = PolynomialMapping {
            exec: Arc::new(f23),
            degree: 2,
            num_i: 2,
            num_o: 3,
        };

        fn f61(v: &[Fr]) -> Vec<Fr> {
            vec![v[0] * v[1] * v[2] * v[3] * v[4] * v[5]]
        }
        let m61 = PolynomialMapping {
            exec: Arc::new(f61),
            degree: 6,
            num_i: 6,
            num_o: 1,
        };

        fn f34(v: &[Fr]) -> Vec<Fr> {
            vec![v[1] * v[2], v[2] * v[0], v[0] * v[1], v[0] * v[1] * v[2]]
        }
        let m34 = PolynomialMapping {
            exec: Arc::new(f34),
            degree: 3,
            num_i: 3,
            num_o: 4,
        };

        fn f45(v: &[Fr]) -> Vec<Fr> {
            vec![v[1] * v[2], v[2] * v[3], v[3] * v[0], v[0] * v[1], v[0] * v[1] * v[2] * v[3]]
        }
        let m45 = PolynomialMapping {
            exec: Arc::new(f45),
            degree: 4,
            num_i: 4,
            num_o: 5,
        };

        fn f53(v: &[Fr]) -> Vec<Fr> {
            vec![v[0] * v[1] * v[2], v[2] * v[3], v[3] * v[4]]
        }
        let m53 = PolynomialMapping {
            exec: Arc::new(f53),
            degree: 3,
            num_i: 5,
            num_o: 3,
        };

        fn f63(v: &[Fr]) -> Vec<Fr> {
            vec![v[0] * v[3], v[1] * v[4], v[2] * v[5]]
        }
        let m63 = PolynomialMapping {
            exec: Arc::new(f63),
            degree: 2,
            num_i: 6,
            num_o: 3,
        };

        let params = GKRParams::<Fr> {
            mappings: GKRMappings {
                first_layer: Some(vec![
                    m63,
                    m34,
                    m45,
                    m53,
                ]),
                layer: vec![
                    m62,
                    m23,
                ],
                last_layer: Some(vec![
                    m61,
                ]),
            },
            num_layers: 4,
        };

        let input = (0..3).map(|_|
            DensePolynomial::new((0..32).map(|_| Fr::rand(gen)).collect())
        ).collect_vec();
        let (trace, output) = GKR::witness(input.clone(), &params);
        let mut i = 0;
        trace[i].iter().zip_eq(input.iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last();
        trace[i + 1].iter().zip_eq(split_vecs(&trace[i]).iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&trace[i], f63).iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&trace[i], f34).iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&trace[i], f45).iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&trace[i], f53).iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last(); i += 1;
        trace[i + 1].iter().zip_eq(split_vecs(&trace[i]).iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&trace[i], f62).iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&trace[i], f23).iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last(); i += 1;
        trace[i + 1].iter().zip_eq(split_vecs(&trace[i]).iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&trace[i], f62).iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly(&trace[i], f23).iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last(); i += 1;
        trace[i + 1].iter().zip_eq(split_vecs(&trace[i]).iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last(); i += 1;
        output.iter().zip_eq(map_over_poly(&trace[i], f61).iter()).map(|(r, e)| assert_eq!(r.Z, e.Z)).last(); i += 1;
    }

    // #[test]
    // fn prover_vs_verifier() {
    //     let gen = &mut test_rng();
    // 
    //     let input = (0..3).map(|_|
    //         DensePolynomial::new((0..32).map(|_| Fr::rand(gen)).collect())
    //     ).collect_vec();
    //     let point = (0..1).map(|_| Fr::rand(gen)).collect_vec();
    // 
    //     let params = BintreeParams::new(
    //         vec![
    //             Layer::new_split(3),
    //             Layer::new_pmap(Box::new(crate::bintree::test::f63), 2, 6, 3),
    //             Layer::new_pmap(Box::new(crate::bintree::test::f34), 3, 3, 4),
    //             Layer::new_pmap(Box::new(crate::bintree::test::f45), 4, 4, 5),
    //             Layer::new_pmap(Box::new(crate::bintree::test::f53), 3, 5, 3),
    //             Layer::new_split(3),
    //             Layer::new_pmap(Box::new(crate::bintree::test::f62), 3, 6, 2),
    //             Layer::new_pmap(Box::new(crate::bintree::test::f23), 2, 2, 3),
    //             Layer::new_split(3),
    //             Layer::new_pmap(Box::new(crate::bintree::test::f62), 3, 6, 2),
    //             Layer::new_pmap(Box::new(crate::bintree::test::f23), 2, 2, 3),
    //             Layer::new_split(3),
    //             Layer::new_pmap(Box::new(crate::bintree::test::f61), 6, 6, 1),
    //         ],
    //         5,
    //     );
    // 
    //     let (trace, output) = Bintree::witness(input.clone(), &params);
    // 
    // 
    //     let evals = to_multieval(EvalClaim {
    //         evs: output.iter().map(|p| p.evaluate(&point)).collect(),
    //         point,
    //     });
    // 
    //     let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());
    // 
    //     let mut prover = BintreeProver::start(evals, trace, &params);
    //     let mut res = None;
    //     while res.is_none() {
    //         let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
    //         res = prover.round(challenge, &mut p_transcript);
    //     }
    //     let (EvalClaim{point: proof_point, evs}, proof) = res.unwrap();
    // 
    //     assert_eq!(evs, input.iter().map(|p| p.evaluate(&proof_point)).collect_vec());
    // 
    // }
}