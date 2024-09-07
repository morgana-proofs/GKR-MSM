use std::{collections::VecDeque, marker::PhantomData, sync::Arc};
use std::fmt::{Debug, Formatter, Pointer};
use std::sync::OnceLock;

use ark_ff::PrimeField;
use ark_std::iterable::Iterable;
use itertools::{Either, Itertools};
#[cfg(feature = "prof")]
use profi::prof;

use crate::{protocol::{protocol::{EvalClaim, MultiEvalClaim, PolynomialMapping, Protocol, ProtocolProver, ProtocolVerifier}, sumcheck::{SumcheckPolyMap as SumcheckPolyMap, SumcheckPolyMapParams, SumcheckPolyMapProof, SumcheckPolyMapProver, SumcheckPolyMapVerifier, to_multieval}, split::{Split, SplitProver, SplitVerifier}}, transcript::{Challenge, TranscriptReceiver}};
use crate::polynomial::fragmented::{FragmentedPoly, InterOp};

#[derive(Clone)]
pub enum BintreeAddLayer<F: PrimeField> {
    Mapping(PolynomialMapping<F>),
    Split(usize),
}

impl<F: PrimeField> Debug for BintreeAddLayer<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self {
            BintreeAddLayer::Mapping(_) => f.write_str("Mapping"),
            BintreeAddLayer::Split(_) => f.write_str("Split"),
        }
    }
}

pub enum BintreeAddProver<F: PrimeField> {
    Split(SplitProver<F>),
    Mapping(SumcheckPolyMapProver<F>),
}

pub enum BintreeAddVerifier<F: PrimeField> {
    Split(SplitVerifier<F>),
    Mapping(SumcheckPolyMapVerifier<F>),
}

pub enum BintreeAddLayerProof<F: PrimeField> {
    Mapping(SumcheckPolyMapProof<F>),
    Split,
}

pub enum BintreeAddClaimsNew<F: PrimeField> {
    Multi(MultiEvalClaim<F>),
    Single(EvalClaim<F>),
}

pub struct BintreeAddComponent<F: PrimeField> {
    phantom_data: PhantomData<F>,
}

impl<F: PrimeField> BintreeAddLayer<F> {
    pub fn new_split(num_polys: usize) -> Self {
        BintreeAddLayer::Split(num_polys)
    }

    pub fn new_pmap(f: Box<dyn Fn(&[F]) -> Vec<F> + Send + Sync>, degree: usize, num_i: usize, num_o: usize) -> Self {
        BintreeAddLayer::Mapping(
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

    pub fn layer_wtns(&self, num_vars: usize, input: Vec<FragmentedPoly<F>>) -> (Vec<Vec<FragmentedPoly<F>>>, Vec<FragmentedPoly<F>>) {
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

impl<F: PrimeField> ComponentLayer<F> for BintreeAddLayer<F> {
    fn num_i(&self) -> usize {
        self.num_i()
    }

    fn num_o(&self) -> usize {
        self.num_o()
    }

    fn check_num_vars(&self, num_vars: &usize) {
        match self {
            BintreeAddLayer::Mapping(_) => {}
            BintreeAddLayer::Split(_) => {
                assert!(num_vars > &0usize, "Can not split 0-variable vector.");
            }
        }
    }

    fn alter_num_vars(&self, num_vars: &mut usize) {
        match self {
            BintreeAddLayer::Mapping(_) => {}
            BintreeAddLayer::Split(_) => {
                *num_vars -= 1;
            }
        }
    }

    fn trailing_check(&self) {
        match self {
            BintreeAddLayer::Mapping(_) => {}
            BintreeAddLayer::Split(_) => panic!("Technical condition: split can not be last operation."),
        };
    }
}

impl<F: PrimeField> ComponentProver<F> for BintreeAddProver<F> {

}

impl<F: PrimeField> ComponentVerifier<F> for BintreeAddVerifier<F> {

}

impl<F: PrimeField> ComponentProof<F> for BintreeAddLayerProof<F> {

}

impl<F: PrimeField> ComponentClaimsNew<F> for BintreeAddClaimsNew<F> {
    fn initial(claim: MultiEvalClaim<F>) -> Self {
        BintreeAddClaimsNew::Multi(claim)
    }

    fn finalize(self) -> EvalClaim<F> {
        match self {
            BintreeAddClaimsNew::Multi(_) => unreachable!(),
            BintreeAddClaimsNew::Single(claim) => claim
        }
    }
}

impl<F: PrimeField> GKRComponentRegistry<F> for BintreeAddComponent<F> {
    type Layer = BintreeAddLayer<F>;
    type Prover = BintreeAddProver<F>;
    type Verifier = BintreeAddVerifier<F>;
    type Proof = BintreeAddLayerProof<F>;
    type ClaimsNew = BintreeAddClaimsNew<F>;
    type TraceRow = Vec<FragmentedPoly<F>>;

    fn initialize_prover(l: &Self::Layer, current_claims: Self::ClaimsNew, current_trace: Self::TraceRow, current_num_vars: usize) -> Self::Prover {
        match l {
            BintreeAddLayer::Mapping(f) => {
                let _current_claims = match current_claims {
                    BintreeAddClaimsNew::Multi(claim) => claim,
                    BintreeAddClaimsNew::Single(claim) => to_multieval(claim)
                };

                Self::Prover::Mapping(SumcheckPolyMapProver::start(
                    _current_claims.clone(),
                    vec![current_trace],
                    &SumcheckPolyMapParams{f: f.clone(), num_vars: current_num_vars}
                ))
            }
            BintreeAddLayer::Split(split) => {
                let _current_claims = match current_claims {
                    BintreeAddClaimsNew::Single(c) => c,
                    BintreeAddClaimsNew::Multi(_) => panic!("Unexpected multi-evaluation claim."),
                };

                Self::Prover::Split(SplitProver::start(
                    _current_claims,
                    vec![current_trace],
                    &()
                ))
            }
        }
    }

    fn initialize_verifier(l: &Self::Layer, current_claims: Self::ClaimsNew, current_proof: Self::Proof, current_num_vars: usize) -> Self::Verifier {
        match l {
            BintreeAddLayer::Mapping(f) => {
                let _current_claims = match current_claims {
                    BintreeAddClaimsNew::Multi(c) => c,
                    BintreeAddClaimsNew::Single(c) => to_multieval(c),
                };

                let Self::Proof::Mapping(_current_proof) = current_proof else {panic!()};

                Self::Verifier::Mapping(SumcheckPolyMapVerifier::start(
                    _current_claims,
                    _current_proof,
                    &SumcheckPolyMapParams{f: f.clone(), num_vars: current_num_vars }
                ))
            }
            BintreeAddLayer::Split(split) => {
                let _current_claims = match current_claims {
                    BintreeAddClaimsNew::Single(c) => c,
                    BintreeAddClaimsNew::Multi(_) => panic!("Unexpected multi-evaluation claim."),
                };

                let Self::Proof::Split = current_proof else {panic!()};

                Self::Verifier::Split(SplitVerifier::start(
                    _current_claims,
                    (),
                    &(),
                ))
            }
        }
    }

    fn prover_round<T: TranscriptReceiver<F>>(prover: &mut Self::Prover, challenge: Challenge<F>, transcript: &mut T) -> Option<(Self::ClaimsNew, Self::Proof)> {
        match prover {
            BintreeAddProver::Split(split) => match split.round(challenge, transcript) {
                None => None,
                Some((claim, proof)) => Some((Self::ClaimsNew::Single(claim), Self::Proof::Split))
            },
            BintreeAddProver::Mapping(map) => match map.round(challenge, transcript) {
                None => None,
                Some((claim, proof)) => Some((Self::ClaimsNew::Single(claim), Self::Proof::Mapping(proof))),
            },
        }
    }

    fn verifier_round<T: TranscriptReceiver<F>>(verifier: &mut Self::Verifier, challenge: Challenge<F>, transcript: &mut T) -> Option<Self::ClaimsNew> {
        match verifier {
            BintreeAddVerifier::Split(split) => match split.round(challenge, transcript) {
                None => None,
                Some(claim) => Some(Self::ClaimsNew::Single(claim))
            },
            BintreeAddVerifier::Mapping(map) => match map.round(challenge, transcript) {
                None => None,
                Some(claim) => Some(Self::ClaimsNew::Single(claim)),
            },
        }    }

    fn layer_wtns(layer: &Self::Layer, num_vars: usize, input: Vec<FragmentedPoly<F>>) -> (Vec<Self::TraceRow>, Vec<FragmentedPoly<F>>) {
        layer.layer_wtns(num_vars, input)
    }
}

// ==============================================================

pub trait GKRComponentRegistry<F: PrimeField> {
    type Layer: ComponentLayer<F> + Debug;
    type Prover: ComponentProver<F>;
    type Verifier: ComponentVerifier<F>;
    type Proof: ComponentProof<F>;
    type ClaimsNew: ComponentClaimsNew<F>;
    type TraceRow;

    fn initialize_prover(l: &Self::Layer, current_claims: Self::ClaimsNew, current_trace: Self::TraceRow, current_num_vars: usize) -> Self::Prover;
    fn initialize_verifier(l: &Self::Layer, current_claims: Self::ClaimsNew, current_proof: Self::Proof, current_num_vars: usize) -> Self::Verifier;
    fn prover_round<T: TranscriptReceiver<F>>(prover: &mut Self::Prover, challenge: Challenge<F>, transcript: &mut T) -> Option<(Self::ClaimsNew, Self::Proof)>;
    fn verifier_round<T: TranscriptReceiver<F>>(verifier: &mut Self::Verifier, challenge: Challenge<F>, transcript: &mut T) -> Option<Self::ClaimsNew>;

    fn layer_wtns(layer: &Self::Layer, num_vars: usize, input: Vec<FragmentedPoly<F>>) -> (Vec<Self::TraceRow>, Vec<FragmentedPoly<F>>);

}

pub trait ComponentClaimsNew<F: PrimeField> {
    fn initial(claim: MultiEvalClaim<F>) -> Self;

    fn finalize(self) -> EvalClaim<F>;
}

pub trait ComponentProof<F: PrimeField> {}

pub trait ComponentProver<F: PrimeField> {}

pub trait ComponentVerifier<F: PrimeField> {}

pub trait ComponentLayer<F: PrimeField>: Clone {
    fn num_i(&self) -> usize;
    fn num_o(&self) -> usize;
    fn check_num_vars(&self, num_vars: &usize);
    fn alter_num_vars(&self, num_vars: &mut usize);

    fn trailing_check(&self);
}


// ===================================================
pub struct GenericGKRParams<F: PrimeField, R: GKRComponentRegistry<F>> {
    pub layers: Vec<R::Layer>,
    pub num_vars: usize,
    pub phantom_data: PhantomData<F>
}

impl <F: PrimeField, R: GKRComponentRegistry<F>> Debug for GenericGKRParams<F, R>{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("Params<num_vars: {:?}, layers: {:?}>", self.num_vars, self.layers))
    }
}

impl<F: PrimeField, R: GKRComponentRegistry<F>> GenericGKRParams<F, R> {
    pub fn new(layers: Vec<R::Layer>, num_vars: usize) -> Self {
        Self {layers, num_vars, phantom_data: PhantomData}
    }

    pub fn unroll(&self) -> Vec<(R::Layer, usize)> {
        let mut num_vars = self.num_vars;
        let mut last_num_o = None;

        let ret : Vec<_> = self.layers.iter().map(|layer| {

            let layer = layer.clone();

            let (num_i, num_o) = (layer.num_i(), layer.num_o());

            let old_num_vars = num_vars;

            layer.check_num_vars(&num_vars);
            layer.alter_num_vars(&mut num_vars);

            let tmp = (layer, old_num_vars);

            match last_num_o {
                None => (),
                Some(o) => {
                    assert_eq!(o, num_i, "Amount of inputs differs from amount of outputs");
                    last_num_o = Some(num_o);
                }
            }

            tmp
        }).collect();


        ret.last().unwrap().0.trailing_check();
        ret
    }

}

pub struct GenericGKRProtocol<F: PrimeField, R: GKRComponentRegistry<F>> {
    _marker: PhantomData<(F, R)>,
}

pub struct GenericGKRProver<F: PrimeField, R: GKRComponentRegistry<F>> {
    proofs: Option<VecDeque<R::Proof>>,
    trace: Vec<R::TraceRow>,
    params: Vec<(R::Layer, usize)>,
    current_claims: Option<R::ClaimsNew>,
    current_prover: Option<R::Prover>,
    phantom_data: PhantomData<R>,
}

pub struct GenericGKRVerifier<F: PrimeField, R: GKRComponentRegistry<F>> {
    proofs: VecDeque<R::Proof>,
    params: Vec<(R::Layer, usize)>,
    current_claims: Option<R::ClaimsNew>,
    current_verifier: Option<R::Verifier>,
    phantom_data: PhantomData<R>
}

impl<F: PrimeField, R: GKRComponentRegistry<F>> Protocol<F> for GenericGKRProtocol<F, R> {
    type Prover = GenericGKRProver<F, R>;

    type Verifier = GenericGKRVerifier<F, R>;

    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type WitnessInput = Vec<FragmentedPoly<F>>;

    type Trace = Vec<R::TraceRow>;

    type WitnessOutput = Vec<FragmentedPoly<F>>;

    type Proof = VecDeque<R::Proof>;

    type Params = GenericGKRParams<F, R>;

    fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
        let mut trace = vec![];
        let num_vars = params.num_vars;
        assert_eq!(args[0].num_vars(), num_vars);
        let layers = params.unroll();
        assert_eq!(layers[0].0.num_i(), args.len());

        let mut layer_trace;
        let mut output = args;

        for (layer, curr_num_vars) in layers {
            (layer_trace, output) = R::layer_wtns(&layer, curr_num_vars, output);
            trace.extend(layer_trace)
        }

        (trace, output)
    }
}

impl<F: PrimeField, R: GKRComponentRegistry<F>> ProtocolProver<F> for GenericGKRProver<F, R> {
    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type Proof = VecDeque<R::Proof>;

    type Params = GenericGKRParams<F, R>;

    type Trace = Vec<R::TraceRow>;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        args: Self::Trace,
        params: &Self::Params,
    ) -> Self {

        Self {
            proofs: Some(VecDeque::new()),
            trace: args,
            params: params.unroll(),
            current_claims: Some(R::ClaimsNew::initial(claims_to_reduce)),
            current_prover: None,
            phantom_data: Default::default(),
        }
    }

    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
                                       ->
                                       Option<(Self::ClaimsNew, Self::Proof)> {
        #[cfg(feature = "prof")]
        prof!("BintreeProver::round");

        let Self{
            proofs,
            trace,
            params,
            current_claims,
            current_prover,
            ..
        } = self;

        match current_prover {
            None => {
                let current_trace = trace.pop().unwrap();
                let (current_params, current_num_vars) = params.pop().unwrap();
                *current_prover = Some(
                    R::initialize_prover(&current_params, current_claims.take().unwrap(), current_trace, current_num_vars)
                )
            },
            Some(_) => (),
        };

        match R::prover_round(current_prover.as_mut().unwrap(), challenge, transcript) {
            None => {}
            Some((claim, proof)) => {
                *current_claims = Some(claim);
                proofs.as_mut().unwrap().push_back(proof);
                *current_prover = None;

            }
        }

        if let None = current_prover.as_ref() {
            if params.len() > 0 {return None};
            Some((current_claims.take().unwrap().finalize(), proofs.take().unwrap()))
        } else {
            None
        }
    }
}

impl<F: PrimeField, R: GKRComponentRegistry<F>> ProtocolVerifier<F> for GenericGKRVerifier<F, R> {
    type Params = GenericGKRParams<F, R>;

    type ClaimsToReduce = MultiEvalClaim<F>;

    type ClaimsNew = EvalClaim<F>;

    type Proof = VecDeque<R::Proof>;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        proof: Self::Proof,
        params: &Self::Params,
    ) -> Self {
        Self {
            proofs: proof,
            params: params.unroll(),
            current_claims: Some(R::ClaimsNew::initial(claims_to_reduce)),
            current_verifier: None,
            phantom_data: Default::default(),
        }
    }

    fn round<T: TranscriptReceiver<F>>(
        &mut self,
        challenge: Challenge<F>,
        transcript: &mut T)
        ->
        Option<Self::ClaimsNew> {
        let Self {
            proofs,
            params,
            current_claims,
            current_verifier,
            ..
        } = self;


        match current_verifier {
            None => {
                let current_proof = proofs.pop_front().unwrap();
                let (current_params, current_num_vars) = params.pop().unwrap();
                *current_verifier = Some(
                    R::initialize_verifier(&current_params, current_claims.take().unwrap(), current_proof, current_num_vars)
                )
            },
            Some(_) => (),
        }

        match R::verifier_round(current_verifier.as_mut().unwrap(), challenge, transcript) {
            None => {}
            Some(claim) => {
                *current_claims = Some(claim);
                *current_verifier = None;

            }
        }
        if let None = current_verifier.as_ref() {
            if params.len() > 0 {return None};
            Some(current_claims.take().unwrap().finalize())
        } else {
            None
        }
    }
}


pub type BintreeParams<F: PrimeField> = GenericGKRParams<F, BintreeAddComponent<F>>;

pub type BintreeProtocol<F: PrimeField> = GenericGKRProtocol<F, BintreeAddComponent<F>>;
pub type BintreeProver<F: PrimeField> = GenericGKRProver<F, BintreeAddComponent<F>>;
pub type BintreeVerifier<F: PrimeField> = GenericGKRVerifier<F, BintreeAddComponent<F>>;

#[cfg(test)]
mod test {
    use ark_bls12_381::{Fr, G1Projective};
    use ark_std::{test_rng, UniformRand};
    use itertools::Itertools;
    use liblasso::utils::test_lib::TestTranscript;
    use crate::polynomial::fragmented::Shape;

    use crate::transcript::{IndexedProofTranscript, TranscriptSender};
    use crate::utils::{map_over_poly_legacy};

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
        let shape = Arc::new(OnceLock::new());
        shape.get_or_init(||Shape::rand(gen, num_vars));
        let input = (0..3).map(|_|
        FragmentedPoly::rand_with_shape(gen, shape.clone())
        ).collect_vec();

        let params = BintreeParams::new(
            vec![
                BintreeAddLayer::new_split(3),
                BintreeAddLayer::new_pmap(Box::new(f63), 10, 6, 3),
                BintreeAddLayer::new_pmap(Box::new(f34), 10, 3, 4),
                BintreeAddLayer::new_pmap(Box::new(f45), 10, 4, 5),
                BintreeAddLayer::new_pmap(Box::new(f53), 10, 5, 3),
                BintreeAddLayer::new_split(3),
                BintreeAddLayer::new_pmap(Box::new(f62), 10, 6, 2),
                BintreeAddLayer::new_pmap(Box::new(f23), 10, 2, 3),
                BintreeAddLayer::new_split(3),
                BintreeAddLayer::new_pmap(Box::new(f62), 10, 6, 2),
                BintreeAddLayer::new_pmap(Box::new(f23), 10, 2, 3),
                BintreeAddLayer::new_split(3),
                BintreeAddLayer::new_pmap(Box::new(f61), 10, 6, 1),
            ],
            5,
        );

        let (trace, output) = BintreeProtocol::witness(input.clone(), &params);
        let mut i = 0;
        trace[i].iter().zip_eq(input.iter()).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last();
        i += 1;// trace[i + 1].iter().zip_eq(split_vecs(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone())).iter()).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f63).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f34).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f45).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f53).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        i += 1;// trace[i + 1].iter().zip_eq(split_vecs(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone())).iter()).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f62).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f23).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        i += 1;// trace[i + 1].iter().zip_eq(split_vecs(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone())).iter()).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f62).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f23).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        i += 1;// trace[i + 1].iter().zip_eq(split_vecs(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone())).iter()).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        output.iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f61).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
        assert_eq!(i, trace.len());
    }

    #[test]
    fn prover_vs_verifier() {
        let gen = &mut test_rng();

        let num_vars = 5;
        let shape = Arc::new(OnceLock::new());
        shape.get_or_init(||Shape::rand(gen, num_vars));
        let input = (0..3).map(|_|
        FragmentedPoly::rand_with_shape(gen, shape.clone())
        ).collect_vec();
        let point = (0..1).map(|_| Fr::rand(gen)).collect_vec();

        let params = BintreeParams::new(
            vec![
                BintreeAddLayer::new_split(3),
                BintreeAddLayer::new_pmap(Box::new(f63), 2, 6, 3),
                BintreeAddLayer::new_pmap(Box::new(f34), 3, 3, 4),
                BintreeAddLayer::new_pmap(Box::new(f45), 4, 4, 5),
                BintreeAddLayer::new_pmap(Box::new(f53), 3, 5, 3),
                BintreeAddLayer::new_split(3),
                BintreeAddLayer::new_pmap(Box::new(f62), 3, 6, 2),
                BintreeAddLayer::new_pmap(Box::new(f23), 2, 2, 3),
                BintreeAddLayer::new_split(3),
                BintreeAddLayer::new_pmap(Box::new(f62), 3, 6, 2),
                BintreeAddLayer::new_pmap(Box::new(f23), 2, 2, 3),
                BintreeAddLayer::new_split(3),
                BintreeAddLayer::new_pmap(Box::new(f61), 6, 6, 1),
            ],
            5,
        );

        let (trace, output) = BintreeProtocol::witness(input.clone(), &params);


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
