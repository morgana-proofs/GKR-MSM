use std::marker::PhantomData;
use ark_ff::PrimeField;
use liblasso::poly::dense_mlpoly::DensePolynomial;
use liblasso::utils::math;
use log::trace;
use crate::gkr::GKRProverState::{SPLIT, SUMCHECK};
use crate::protocol::{IndexedProofTranscript, TranscriptReceiver, TranscriptSender, Challenge, Protocol, ProtocolProver, ProtocolVerifier, PolynomialMapping};
use crate::utils::{map_over_poly, split_vecs};

pub struct GKR<F: PrimeField> {
    _pd: PhantomData<F>,
}

pub struct GKRProver<F: PrimeField> {
    trace: <Self as ProtocolProver<F>>::Trace,
    current: GKRProverState,
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum GKRProverState {
    INIT,
    SUMCHECK(usize),
    SPLIT(usize),
    DONE,
}

impl GKRProverState {
    fn next<F: PrimeField>(self, params: &GKRParams<F>) -> Self {
        match self {
            GKRProverState::SUMCHECK(i) => match params.should_split(i) {
                true => GKRProverState::SPLIT(i),
                false => GKRProverState::SUMCHECK(i - 1),
            },
            GKRProverState::SPLIT(i) => match i {
                0 => GKRProverState::DONE,
                _ => GKRProverState::SUMCHECK(i - 1),
            }
            GKRProverState::INIT => match params.num_layers {
                0 => GKRProverState::DONE,
                _ => GKRProverState::SUMCHECK(params.get_total_length() - 1),
            }
            GKRProverState::DONE => unreachable!(),
        }
    }

    fn wtns_next<F: PrimeField>(self, params: &GKRParams<F>) -> Self {
        match self {
            GKRProverState::SUMCHECK(i) => {
                if i + 1 == params.get_total_length() {
                    GKRProverState::INIT
                } else {
                    match params.should_split(i + 1) {
                        true => GKRProverState::SPLIT(i + 1),
                        false => GKRProverState::SUMCHECK(i + 1),
                    }
                }
            },
            GKRProverState::SPLIT(i) => GKRProverState::SUMCHECK(i),
            GKRProverState::INIT => unreachable!(),
            GKRProverState::DONE => match params.num_layers {
                0 => GKRProverState::INIT,
                _ => GKRProverState::SPLIT(0),
            }
        }
    }
}

pub struct GKRVerifier<F: PrimeField> {
    _pd: PhantomData<F>,
}

pub struct GKRProof<F: PrimeField> {
    _pd: PhantomData<F>,
}

/// if mapping for first or last layer is None we assume it is the same as for the inner layer
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
pub struct GKRParams<F: PrimeField> {
    mappings: GKRMappings<F>,
    num_layers: usize,
}

impl<F: PrimeField> GKRParams<F> {
    fn get_mappings(&self, mut idx: usize) -> &PolynomialMapping<F> {
        if idx < self.mappings.first_layer_length() {
            if let Some(l) = &self.mappings.first_layer {
                return &l[idx];
            }
        } else {
            idx -= self.mappings.first_layer_length();
        }

        if idx >= (self.num_layers - 2) * self.mappings.inner_layer_length() {
            idx -= (self.num_layers - 2) * self.mappings.inner_layer_length();
            if let Some(l) = &self.mappings.last_layer {
                return &l[idx];
            } else {
                return self.mappings.layer.get(idx).unwrap()
            }
        }

        &self.mappings.layer.get(idx % self.mappings.inner_layer_length()).unwrap()
    }

    fn get_total_length(&self) -> usize {
        let mut total = 0;
        if self.num_layers == 0 {
            return total;
        }
        total += self.mappings.first_layer_length();
        if self.num_layers == 1 {
            return total;
        }
        total += self.mappings.last_layer_length();
        if self.num_layers == 2 {
            return total;
        }
        total + self.mappings.inner_layer_length() * (self.num_layers - 2)
    }

    fn should_split(&self, mut idx: usize) -> bool {
        if idx == 0 {
            return true;
        }
        if idx < self.mappings.first_layer_length() {
            return false;
        }
        idx -= self.mappings.first_layer_length();
        if idx % self.mappings.inner_layer_length() == 0 {
            return true
        }
        if idx < self.mappings.inner_layer_length() * (self.num_layers - 2) {
            return false;
        }
        idx -= self.mappings.inner_layer_length() * (self.num_layers - 2);
        idx == self.mappings.last_layer_length()
    }
}

impl<F: PrimeField> Protocol<F> for GKR<F> {
    type Prover = GKRProver<F>;
    type Verifier = GKRVerifier<F>;
    type ClaimsToReduce = Vec<DensePolynomial<F>>;
    type ClaimsNew = Vec<DensePolynomial<F>>;
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
            trace.push(next_layer);
            println!("{:?}", state);
            match state {
                SUMCHECK(idx) => {
                    next_layer = map_over_poly(trace.last().unwrap(), |v| (GKR::get_current_mapping(params, idx).exec)(v));
                },
                SPLIT(idx) => {
                    next_layer = split_vecs(trace.last().unwrap());
                },
                _ => unreachable!(),
            };
            state = state.wtns_next(params);
        }
        (trace, next_layer)
    }
}

impl<F: PrimeField> GKR<F> {
    fn get_current_input(trace: &<Self as Protocol<F>>::Trace, idx: usize) -> &Vec<DensePolynomial<F>> {
        trace.get(idx).unwrap()
    }

    fn get_current_mapping(params: &<Self as Protocol<F>>::Params, idx: usize) -> &PolynomialMapping<F> {
        params.get_mappings(idx)
    }
}

impl<F: PrimeField> ProtocolProver<F> for GKRProver<F> {
    type ClaimsToReduce = Vec<DensePolynomial<F>>;
    type ClaimsNew = Vec<DensePolynomial<F>>;
    type Proof = GKRProof<F>;
    type Params = GKRParams<F>;
    type Trace = Vec<Vec<DensePolynomial<F>>>;
    fn start(claims_to_reduce: Self::ClaimsToReduce, args: Self::Trace, params: &Self::Params) -> Self {

        Self {
            trace: vec![],
            current: GKRProverState::INIT,
        }
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T) -> Option<(Self::ClaimsNew, Self::Proof)> {
        todo!()
    }
}

impl<F: PrimeField> ProtocolVerifier<F> for GKRVerifier<F> {
    type Params = GKRParams<F>;
    type ClaimsToReduce = Vec<DensePolynomial<F>>;
    type ClaimsNew = Vec<DensePolynomial<F>>;
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
    use ark_bls12_381::Fr;
    use ark_std::{test_rng, UniformRand, Zero};
    use itertools::Itertools;
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
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(1));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(0));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(0));
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
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(3));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(2));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(2));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(1));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(0));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(0));
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
            assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(2 * i + 1));
            t.push(t.last().unwrap().next(&params));
            assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(2 * i));
            t.push(t.last().unwrap().next(&params));
            assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(2 * i));
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
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(14));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(14));
        for i in (0..5).rev() {
            t.push(t.last().unwrap().next(&params));
            assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(4 + i * 2 + 1));
            t.push(t.last().unwrap().next(&params));
            assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(4 + i * 2));
            t.push(t.last().unwrap().next(&params));
            assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(4 + i * 2));
        }
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(3));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(2));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(1));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SUMCHECK(0));
        t.push(t.last().unwrap().next(&params));
        assert_eq!(t.last().unwrap(), &GKRProverState::SPLIT(0));
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
            num_i: 3,
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

}