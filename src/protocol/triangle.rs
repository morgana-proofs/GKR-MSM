use std::{marker::PhantomData, sync::Arc};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::sync::OnceLock;
use ark_ed_on_bls12_381_bandersnatch::{EdwardsProjective};
use ark_ff::{Field, PrimeField};
use ark_std::iterable::Iterable;
use itertools::Itertools;
#[cfg(feature = "prof")]
use profi::prof;

use crate::{protocol::{protocol::{EvalClaim, MultiEvalClaim, PolynomialMapping, Protocol, ProtocolProver, ProtocolVerifier}, sumcheck::{SumcheckPolyMap as SumcheckPolyMap, SumcheckPolyMapParams, SumcheckPolyMapProof, SumcheckPolyMapProver, SumcheckPolyMapVerifier, to_multieval}, split::{Split, SplitProver, SplitVerifier}}, transcript::{Challenge, TranscriptReceiver}};
use crate::grand_add::{twisted_edwards_add_l1, twisted_edwards_add_l2, twisted_edwards_add_l3};
use crate::polynomial::fragmented::{FragmentedPoly, InterOp};
use crate::protocol::generic_gkr::{ComponentClaimsNew, ComponentLayer, ComponentProof, ComponentProver, ComponentVerifier, GenericGKRParams, GenericGKRProtocol, GenericGKRProver, GenericGKRVerifier, GKRComponentRegistry};
use crate::protocol::split_at::{SplitAt, SplitAtParams, SplitAtProver, SplitAtVerifier};
use crate::utils::TwistedEdwardsConfig;

#[derive(Clone)]
pub enum TriangleAddLayer<F: PrimeField> {
    Mapping(PolynomialMapping<F>),
    SplitAt(usize, usize),
}

impl<F: PrimeField> Debug for TriangleAddLayer<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self {
            TriangleAddLayer::Mapping(m) => f.write_str(&format!("Mapping<in: {}, out: {}, deg: {}>", m.num_i, m.num_o, m.degree)),
            TriangleAddLayer::SplitAt(a, b) => f.write_str(&format!("Split<polys: {}, idx: {}>", a, b)),
        }
    }
}

pub enum TriangleAddLayerProver<F: PrimeField> {
    SplitAt(SplitAtProver<F>),
    Mapping(SumcheckPolyMapProver<F>),
}

pub enum TriangleAddLayerVerifier<F: PrimeField> {
    SplitAt(SplitAtVerifier<F>),
    Mapping(SumcheckPolyMapVerifier<F>),
}

pub enum TriangleAddLayerProof<F: PrimeField> {
    Mapping(SumcheckPolyMapProof<F>),
    SplitAt,
}

pub enum TriangleAddClaimsNew<F: PrimeField> {
    Multi(MultiEvalClaim<F>),
    Single(EvalClaim<F>),
}

pub struct TriangleAddComponent<F: PrimeField> {
    phantom_data: PhantomData<F>,
}

impl<F: PrimeField> TriangleAddLayer<F> {
    pub fn new_split(num_polys: usize, var_idx: usize) -> Self {
        TriangleAddLayer::SplitAt(num_polys, var_idx)
    }

    pub fn new_pmap(f: Box<dyn Fn(&[F]) -> Vec<F> + Send + Sync>, degree: usize, num_i: usize, num_o: usize) -> Self {
        TriangleAddLayer::Mapping(
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
            Self::SplitAt(n, _) => *n,
        }
    }

    pub fn num_o(&self) -> usize {
        match self {
            Self::Mapping(PolynomialMapping{num_o, ..}) => *num_o,
            Self::SplitAt(n, _) => 2 * n,
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
            Self::SplitAt(_, var_idx) => {
                SplitAt::witness(input, &SplitAtParams{var: *var_idx, poly_grp_size: 3})
            }
        }
    }

}

impl<F: PrimeField> ComponentLayer<F> for TriangleAddLayer<F> {
    fn num_i(&self) -> usize {
        self.num_i()
    }

    fn num_o(&self) -> usize {
        self.num_o()
    }

    fn check_num_vars(&self, num_vars: &usize) {
        match self {
            TriangleAddLayer::Mapping(_) => {}
            TriangleAddLayer::SplitAt(_, _) => {
                assert!(num_vars > &0usize, "Can not split 0-variable vector.");
            }
        }
    }

    fn alter_num_vars(&self, num_vars: &mut usize) {
        match self {
            TriangleAddLayer::Mapping(_) => {}
            TriangleAddLayer::SplitAt(_, _) => {
                *num_vars -= 1;
            }
        }
    }

    fn trailing_check(&self) {
        match self {
            TriangleAddLayer::Mapping(_) => {}
            TriangleAddLayer::SplitAt(_, _) => panic!("Technical condition: split can not be last operation."),
        };
    }
}

impl<F: PrimeField> ComponentProver<F> for TriangleAddLayerProver<F> {

}

impl<F: PrimeField> ComponentVerifier<F> for TriangleAddLayerVerifier<F> {

}

impl<F: PrimeField> ComponentProof<F> for TriangleAddLayerProof<F> {

}

impl<F: PrimeField> ComponentClaimsNew<F> for TriangleAddClaimsNew<F> {
    fn initial(claim: MultiEvalClaim<F>) -> Self {
        TriangleAddClaimsNew::Multi(claim)
    }

    fn finalize(self) -> EvalClaim<F> {
        match self {
            TriangleAddClaimsNew::Multi(_) => unreachable!(),
            TriangleAddClaimsNew::Single(claim) => claim
        }
    }
}

impl<F: PrimeField> GKRComponentRegistry<F> for TriangleAddComponent<F> {
    type Layer = TriangleAddLayer<F>;
    type Prover = TriangleAddLayerProver<F>;
    type Verifier = TriangleAddLayerVerifier<F>;
    type Proof = TriangleAddLayerProof<F>;
    type ClaimsNew = TriangleAddClaimsNew<F>;
    type TraceRow = Vec<FragmentedPoly<F>>;

    fn initialize_prover(l: &Self::Layer, current_claims: Self::ClaimsNew, current_trace: Self::TraceRow, current_num_vars: usize) -> Self::Prover {
        match l {
            TriangleAddLayer::Mapping(f) => {
                let _current_claims = match current_claims {
                    TriangleAddClaimsNew::Multi(claim) => claim,
                    TriangleAddClaimsNew::Single(claim) => to_multieval(claim)
                };

                Self::Prover::Mapping(SumcheckPolyMapProver::start(
                    _current_claims.clone(),
                    vec![current_trace],
                    &SumcheckPolyMapParams{f: f.clone(), num_vars: current_num_vars}
                ))
            }
            TriangleAddLayer::SplitAt(split, var_idx) => {
                let _current_claims = match current_claims {
                    TriangleAddClaimsNew::Single(c) => c,
                    TriangleAddClaimsNew::Multi(_) => panic!("Unexpected multi-evaluation claim."),
                };

                Self::Prover::SplitAt(SplitAtProver::start(
                    _current_claims,
                    vec![current_trace],
                    &SplitAtParams{var: *var_idx, poly_grp_size: 3}
                ))
            }
        }
    }

    fn initialize_verifier(l: &Self::Layer, current_claims: Self::ClaimsNew, current_proof: Self::Proof, current_num_vars: usize) -> Self::Verifier {
        match l {
            TriangleAddLayer::Mapping(f) => {
                let _current_claims = match current_claims {
                    TriangleAddClaimsNew::Multi(c) => c,
                    TriangleAddClaimsNew::Single(c) => to_multieval(c),
                };

                let Self::Proof::Mapping(_current_proof) = current_proof else {panic!()};

                Self::Verifier::Mapping(SumcheckPolyMapVerifier::start(
                    _current_claims,
                    _current_proof,
                    &SumcheckPolyMapParams{f: f.clone(), num_vars: current_num_vars }
                ))
            }
            TriangleAddLayer::SplitAt(split, var_idx) => {
                let _current_claims = match current_claims {
                    TriangleAddClaimsNew::Single(c) => c,
                    TriangleAddClaimsNew::Multi(_) => panic!("Unexpected multi-evaluation claim."),
                };

                let Self::Proof::SplitAt = current_proof else {panic!()};

                Self::Verifier::SplitAt(SplitAtVerifier::start(
                    _current_claims,
                    (),
                    &SplitAtParams{var: *var_idx, poly_grp_size: 3},
                ))
            }
        }
    }

    fn prover_round<T: TranscriptReceiver<F>>(prover: &mut Self::Prover, challenge: Challenge<F>, transcript: &mut T) -> Option<(Self::ClaimsNew, Self::Proof)> {
        match prover {
            TriangleAddLayerProver::SplitAt(split) => {
                match split.round(challenge, transcript) {
                    None => None,
                    Some((claim, proof)) => Some((Self::ClaimsNew::Single(claim), Self::Proof::SplitAt))
                }
            },
            TriangleAddLayerProver::Mapping(map) => {
                match map.round(challenge, transcript) {
                    None => None,
                    Some((claim, proof)) => Some((Self::ClaimsNew::Single(claim), Self::Proof::Mapping(proof))),
                }
            },
        }
    }

    fn verifier_round<T: TranscriptReceiver<F>>(verifier: &mut Self::Verifier, challenge: Challenge<F>, transcript: &mut T) -> Option<Self::ClaimsNew> {
        match verifier {
            TriangleAddLayerVerifier::SplitAt(split) => match split.round(challenge, transcript) {
                None => None,
                Some(claim) => Some(Self::ClaimsNew::Single(claim))
            },
            TriangleAddLayerVerifier::Mapping(map) => match map.round(challenge, transcript) {
                None => None,
                Some(claim) => Some(Self::ClaimsNew::Single(claim)),
            },
        }    }

    fn layer_wtns(layer: &Self::Layer, num_vars: usize, input: Vec<FragmentedPoly<F>>) -> (Vec<Self::TraceRow>, Vec<FragmentedPoly<F>>) {
        layer.layer_wtns(num_vars, input)
    }
}

pub type TriangleAddParams<F: PrimeField> = GenericGKRParams<F, TriangleAddComponent<F>>;
pub type TriangleAddProtocol<F: PrimeField> = GenericGKRProtocol<F, TriangleAddComponent<F>>;
pub type TriangleAddProver<F: PrimeField> = GenericGKRProver<F, TriangleAddComponent<F>>;
pub type TriangleAddVerifier<F: PrimeField> = GenericGKRVerifier<F, TriangleAddComponent<F>>;

pub fn t1_l1<F: Field + TwistedEdwardsConfig>(pts: &[F]) -> Vec<F> {
    assert_eq!(pts.len(), 3 * 4);
    let first = pts.first_chunk::<6>().unwrap();
    let last = pts.last_chunk::<6>().unwrap();
    let a = first.first_chunk::<3>().unwrap();
    let b = first.last_chunk::<3>().unwrap();
    let c = last.first_chunk::<3>().unwrap();
    let d = last.last_chunk::<3>().unwrap();

    let mut ret = twisted_edwards_add_l1(&a.iter().chain(c.iter()).collect_vec());
    ret.extend(twisted_edwards_add_l1(&b.iter().chain(d.iter()).collect_vec()));
    ret.extend(twisted_edwards_add_l1(last));
    ret
}

pub fn l1_at<F: Field + TwistedEdwardsConfig>(depth: usize, pts: &[F]) -> Vec<F> {
    assert_eq!(pts.len(), 3 * 4 + 3 * 2 * depth);
    let first = pts.first_chunk::<12>().unwrap();
    let mut ret = t1_l1(first);
    for chunk in pts.chunks(6).skip(2) {
        ret.extend(twisted_edwards_add_l1(chunk));
    }
    assert_eq!(ret.len(), l2_i_at(depth));
    ret
}

pub fn l2_at<F: Field + TwistedEdwardsConfig>(depth: usize, pts: &[F]) -> Vec<F> {
    assert_eq!(pts.len(), 4 * 2 + 4 * (depth + 1));
    let mut ret = vec![];
    for chunk in pts.chunks(4) {
        ret.extend(twisted_edwards_add_l2(chunk));
    }
    assert_eq!(ret.len(), l3_i_at(depth));
    ret
}

pub fn l3_at<F: Field + TwistedEdwardsConfig>(depth: usize, pts: &[F]) -> Vec<F> {
    assert_eq!(pts.len(), 4 * 2 + 4 * (depth + 1));
    let mut ret = vec![];
    for chunk in pts.chunks(4) {
        ret.extend(twisted_edwards_add_l3(chunk));
    }
    assert_eq!(ret.len() * 2, l1_i_at(depth + 1));
    ret
}

pub fn l1_i_at(depth: usize) -> usize {
    3 * 4 + 3 * 2 * depth
}

pub fn l2_i_at(depth: usize) -> usize {
    4 * 2 + 4 * (depth + 1)
}

pub fn l3_i_at(depth: usize) -> usize {
    4 * 2 + 4 * (depth + 1)
}


pub fn make_triangle_add_params<F: PrimeField + TwistedEdwardsConfig>(mut num_vars: usize, split_var_idx: usize) -> TriangleAddParams<F> {
    let mut layers = vec![
        TriangleAddLayer::new_split(3, split_var_idx),
    ];

    for d in 0..(num_vars - split_var_idx - 1) {
        layers.extend([
            TriangleAddLayer::new_split(l1_i_at(d) / 2, split_var_idx),
            TriangleAddLayer::new_pmap(Box::new(move |pts| l1_at(d, pts)), 2, l1_i_at(d), l2_i_at(d)),
            TriangleAddLayer::new_pmap(Box::new(move |pts| l2_at(d, pts)), 2, l2_i_at(d), l3_i_at(d)),
            TriangleAddLayer::new_pmap(Box::new(move |pts| l3_at(d, pts)), 2, l3_i_at(d), l1_i_at(d + 1) / 2),
        ])
    }

    TriangleAddParams::new(
        layers,
        num_vars,
    )
}

#[cfg(test)]
mod test {
    use ark_bls12_381::{Fr, G1Projective};
    use ark_std::{test_rng, UniformRand};
    use ark_std::rand::{Rng, RngCore};
    use itertools::Itertools;
    use liblasso::utils::test_lib::TestTranscript;
    use crate::polynomial::fragmented::{Fragment, Shape};
    use crate::polynomial::fragmented::FragmentContent::{Consts, Data};
    use crate::transcript::{IndexedProofTranscript, TranscriptSender};
    use crate::utils::{map_over_poly_legacy};

    use super::*;

    mod generic {
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

            let rng = &mut test_rng();
            let num_vars = 8;
            let num_polys = 3;
            let num_splits = 4;

            fn no_const_gen<RNG: Rng>(rng: &mut RNG, num_vars: usize, num_splits: usize) -> (FragmentedPoly<Fr>, usize, usize) {
                let split_var = rng.next_u64() as usize % (num_vars - num_splits);
                let sector_size: usize = 1 << (num_vars - 1 - split_var);
                let data_len = 1 << num_vars;

                let s = Shape::new(
                    vec![
                        Fragment {
                            mem_idx: 0,
                            len: data_len,
                            content: Data,
                            start: 0,
                        }
                    ],
                    1,
                );

                let shape = Arc::new(OnceLock::new());
                shape.get_or_init(|| s);
                let d = FragmentedPoly::<Fr>::rand_with_shape(rng, shape);
                (d, split_var, sector_size)
            }
            fn rng_gen<RNG: Rng>(rng: &mut RNG, num_vars: usize, num_splits: usize) -> (FragmentedPoly<Fr>, usize, usize) {
                let split_var = rng.next_u64() as usize % (num_vars - num_splits);
                let sector_size = 1 << (num_vars - 1 - split_var);
                let max_data_sectors_pairs = 1 << (split_var);
                let data_sectors = 2 * (rng.next_u64() as usize % max_data_sectors_pairs + 1);
                let data_len = data_sectors * sector_size;
                let consts_len = (1 << num_vars) - data_len;

                let s = Shape::new(
                    vec![
                        Fragment {
                            mem_idx: 0,
                            len: data_len,
                            content: Data,
                            start: 0,
                        },
                        Fragment {
                            mem_idx: 0,
                            len: consts_len,
                            content: Consts,
                            start: data_len,
                        }
                    ],
                    1,
                );

                let shape = Arc::new(OnceLock::new());
                shape.get_or_init(|| s);
                let d = FragmentedPoly::<Fr>::rand_with_shape(rng, shape);
                (d, split_var, sector_size)
            }

            for gen in [no_const_gen, rng_gen] {
                for _ in 0..100 {
                    let (d, split_var, sector_size) = gen(rng, num_vars, num_splits);
                    let shape = d.shape.clone();
                    let mut input = vec![d];
                    for _ in 1..num_polys {
                        input.push(FragmentedPoly::rand_with_shape(rng, shape.clone()))
                    }

                    assert!(num_vars > 4 + split_var);

                    let params = TriangleAddParams::new(
                        vec![
                            TriangleAddLayer::new_split(3, split_var),
                            TriangleAddLayer::new_pmap(Box::new(f63), 10, 6, 3),
                            TriangleAddLayer::new_pmap(Box::new(f34), 10, 3, 4),
                            TriangleAddLayer::new_pmap(Box::new(f45), 10, 4, 5),
                            TriangleAddLayer::new_pmap(Box::new(f53), 10, 5, 3),
                            TriangleAddLayer::new_split(3, split_var),
                            TriangleAddLayer::new_pmap(Box::new(f62), 10, 6, 2),
                            TriangleAddLayer::new_pmap(Box::new(f23), 10, 2, 3),
                            TriangleAddLayer::new_split(3, split_var),
                            TriangleAddLayer::new_pmap(Box::new(f62), 10, 6, 2),
                            TriangleAddLayer::new_pmap(Box::new(f23), 10, 2, 3),
                            TriangleAddLayer::new_split(3, split_var),
                            TriangleAddLayer::new_pmap(Box::new(f61), 10, 6, 1),
                        ],
                        num_vars,
                    );

                    let (trace, output) = TriangleAddProtocol::witness(input.clone(), &params);
                    let mut i = 0;
                    trace[i].iter().zip_eq(input.iter()).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last();
                    i += 1; // trace[i + 1].iter().zip_eq(split_vecs(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone())).iter()).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
                    trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f63).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last();
                    i += 1;
                    trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f34).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last();
                    i += 1;
                    trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f45).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last();
                    i += 1;
                    trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f53).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last();
                    i += 1;
                    i += 1; // trace[i + 1].iter().zip_eq(split_vecs(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone())).iter()).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
                    trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f62).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last();
                    i += 1;
                    trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f23).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last();
                    i += 1;
                    i += 1; // trace[i + 1].iter().zip_eq(split_vecs(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone())).iter()).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
                    trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f62).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last();
                    i += 1;
                    trace[i + 1].iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f23).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last();
                    i += 1;
                    i += 1; // trace[i + 1].iter().zip_eq(split_vecs(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone())).iter()).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last(); i += 1;
                    output.iter().zip_eq(map_over_poly_legacy(&Vec::<FragmentedPoly<Fr>>::interop_into(trace[i].clone()), f61).iter().map(|p| FragmentedPoly::<Fr>::interop_from(p.clone()))).map(|(r, e)| assert_eq!(r.vec(), e.vec())).last();
                    i += 1;
                    assert_eq!(i, trace.len());
                }
            }
        }

        #[test]
        fn prover_vs_verifier() {
            let gen = &mut test_rng();
            let rng = &mut test_rng();
            let num_vars = 8;
            let num_polys = 3;
            let num_splits = 8;

            fn no_const_gen<RNG: Rng>(rng: &mut RNG, num_vars: usize, num_splits: usize) -> (FragmentedPoly<Fr>, usize, usize) {
                let split_var = if num_vars - num_splits == 0 {0} else { rng.next_u64() as usize % (num_vars - num_splits) };
                let sector_size: usize = 1 << (num_vars - 1 - split_var);
                let data_len = 1 << num_vars;

                let s = Shape::new(
                    vec![
                        Fragment {
                            mem_idx: 0,
                            len: data_len,
                            content: Data,
                            start: 0,
                        }
                    ],
                    1,
                );

                let shape = Arc::new(OnceLock::new());
                shape.get_or_init(|| s);
                let d = FragmentedPoly::<Fr>::rand_with_shape(rng, shape);
                (d, split_var, sector_size)
            }
            fn rng_gen<RNG: Rng>(rng: &mut RNG, num_vars: usize, num_splits: usize) -> (FragmentedPoly<Fr>, usize, usize) {
                let split_var = if num_vars - num_splits == 0 {0} else { rng.next_u64() as usize % (num_vars - num_splits) };
                let sector_size = 1 << (num_vars - 1 - split_var);
                let max_data_sectors_pairs = 1 << (split_var);
                let data_sectors = 2 * (rng.next_u64() as usize % max_data_sectors_pairs + 1);
                let data_len = data_sectors * sector_size;
                let consts_len = (1 << num_vars) - data_len;
                let mut num_consts = 0;

                let mut fragments = vec![
                    Fragment {
                        mem_idx: 0,
                        len: data_len,
                        content: Data,
                        start: 0,
                    }
                ];
                if consts_len != 0 {
                    fragments.push(
                        Fragment {
                            mem_idx: 0,
                            len: consts_len,
                            content: Consts,
                            start: data_len,
                        }
                    );
                    num_consts += 1;
                }

                let s = Shape::new(
                    fragments,
                    num_consts,
                );

                let shape = Arc::new(OnceLock::new());
                shape.get_or_init(|| s);
                let d = FragmentedPoly::<Fr>::rand_with_shape(rng, shape);
                (d, split_var, sector_size)
            }

            for gen in [no_const_gen, rng_gen] {
                for _ in 0..2 {
                    let (d, split_var, sector_size) = gen(rng, num_vars, num_splits);
                    let shape = d.shape.clone();
                    let mut input = vec![d];
                    for _ in 1..num_polys {
                        input.push(FragmentedPoly::rand_with_shape(rng, shape.clone()))
                    }
                    let point = (0..(num_vars - num_splits)).map(|_| Fr::rand(rng)).collect_vec();


                    assert!(num_vars > 4 + split_var);

                    let params = TriangleAddParams::new(
                        vec![
                            TriangleAddLayer::new_split(3, split_var),
                            TriangleAddLayer::new_pmap(Box::new(f63), 2, 6, 3),
                            TriangleAddLayer::new_pmap(Box::new(f34), 3, 3, 4),
                            TriangleAddLayer::new_pmap(Box::new(f45), 4, 4, 5),
                            TriangleAddLayer::new_pmap(Box::new(f53), 3, 5, 3),
                            TriangleAddLayer::new_split(3, split_var),
                            TriangleAddLayer::new_pmap(Box::new(f62), 3, 6, 2),
                            TriangleAddLayer::new_pmap(Box::new(f23), 2, 2, 3),
                            TriangleAddLayer::new_split(3, split_var),
                            TriangleAddLayer::new_pmap(Box::new(f62), 3, 6, 2),
                            TriangleAddLayer::new_pmap(Box::new(f23), 2, 2, 3),
                            TriangleAddLayer::new_split(3, split_var),
                            TriangleAddLayer::new_pmap(Box::new(f62), 3, 6, 2),
                            TriangleAddLayer::new_pmap(Box::new(f23), 2, 2, 3),
                            TriangleAddLayer::new_split(3, split_var),
                            TriangleAddLayer::new_pmap(Box::new(f62), 3, 6, 2),
                            TriangleAddLayer::new_pmap(Box::new(f23), 2, 2, 3),
                            TriangleAddLayer::new_split(3, split_var),
                            TriangleAddLayer::new_pmap(Box::new(f62), 3, 6, 2),
                            TriangleAddLayer::new_pmap(Box::new(f23), 2, 2, 3),
                            TriangleAddLayer::new_split(3, split_var),
                            TriangleAddLayer::new_pmap(Box::new(f62), 3, 6, 2),
                            TriangleAddLayer::new_pmap(Box::new(f23), 2, 2, 3),
                            TriangleAddLayer::new_split(3, split_var),
                            TriangleAddLayer::new_pmap(Box::new(f61), 6, 6, 1),
                        ],
                        num_vars,
                    );

                    let (trace, output) = TriangleAddProtocol::witness(input.clone(), &params);


                    let claims_to_reduce = to_multieval(EvalClaim {
                        evs: output.iter().map(|p| p.evaluate(&point)).collect(),
                        point,
                    });

                    let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());

                    let mut prover = TriangleAddProver::start(claims_to_reduce.clone(), trace, &params);
                    let mut res = None;
                    while res.is_none() {
                        let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
                        res = prover.round(challenge, &mut p_transcript);
                    }
                    let (EvalClaim { point: proof_point, evs: proof_evs }, proof) = res.unwrap();

                    assert_eq!(proof_evs, input.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

                    let mut v_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));

                    let mut verifier = TriangleAddVerifier::start(
                        claims_to_reduce,
                        proof,
                        &params,
                    );

                    let mut res = None;
                    while res.is_none() {
                        let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
                        res = verifier.round(challenge, &mut v_transcript);
                    }
                    let EvalClaim { point: verify_point, evs: verify_evs } = res.unwrap();

                    assert_eq!(proof_point, verify_point);
                    assert_eq!(proof_evs, verify_evs);
                }
            }
        }
    }

    mod add {
        use ark_ec::{CurveGroup, Group};
        use ark_ed_on_bls12_381_bandersnatch::EdwardsProjective;
        use ark_ff::BigInt;
        use itertools::multizip;
        use liblasso::utils::math::Math;
        use super::*;

        #[test]
        fn witness_generation() {
            fn no_const_gen<RNG: Rng>(rng: &mut RNG, num_vars: usize) -> (FragmentedPoly<ark_ed_on_bls12_381_bandersnatch::EdwardsProjective>, [FragmentedPoly<Fr>; 3], usize, usize) {
                // let split_var = rng.next_u64() as usize % (num_vars - 3);
                let split_var = 1;
                let sector_size: usize = 1 << (num_vars - 1 - split_var);
                let data_len = 1 << num_vars;

                let s = Shape::new(
                    vec![
                        Fragment {
                            mem_idx: 0,
                            len: data_len,
                            content: Data,
                            start: 0,
                        }
                    ],
                    1,
                );

                let shape = Arc::new(OnceLock::new());
                shape.get_or_init(|| s);

                let (points, data) = FragmentedPoly::rand_points_with_shape(rng, shape);
                (points, data, split_var, sector_size)
            }
            fn rng_gen<RNG: Rng>(rng: &mut RNG, num_vars: usize) -> (FragmentedPoly<ark_ed_on_bls12_381_bandersnatch::EdwardsProjective>, [FragmentedPoly<Fr>; 3], usize, usize) {
                let split_var = rng.next_u64() as usize % (num_vars - 3);
                let sector_size = 1 << (num_vars - 1 - split_var);
                let max_data_sectors_pairs = 1 << (split_var);
                let data_sectors = 2 * (rng.next_u64() as usize % max_data_sectors_pairs + 1);
                let data_len = data_sectors * sector_size;
                let consts_len = (1 << num_vars) - data_len;
                let mut num_consts = 0;

                let mut fragments = vec![
                    Fragment {
                        mem_idx: 0,
                        len: data_len,
                        content: Data,
                        start: 0,
                    }
                ];
                if consts_len != 0 {
                    fragments.push(
                        Fragment {
                            mem_idx: 0,
                            len: consts_len,
                            content: Consts,
                            start: data_len,
                        }
                    );
                    num_consts += 1;
                }

                let s = Shape::new(
                    fragments,
                    num_consts,
                );

                let shape = Arc::new(OnceLock::new());
                shape.get_or_init(|| s);

                let (points, data) = FragmentedPoly::rand_points_with_shape(rng, shape);
                (points, data, split_var, sector_size)
            }

            let rng = &mut test_rng();
            let num_vars = 8;


            for gen in [no_const_gen, rng_gen] {
                for _ in 0..10 {
                    let (points, data, split_var, sector_size) = gen(rng, num_vars);

                    let input = data.to_vec();
                    let points_vec = points.vec();

                    let params = make_triangle_add_params(num_vars, split_var);

                    // dbg!(&params);

                    let (trace, output) = TriangleAddProtocol::witness(input.clone(), &params);
                    let out_vecs = output.iter().map(|p| p.vec()).collect_vec();

                    let mut chunk_results = vec![];
                    for mut chunk in points_vec.chunks(1 << (points_vec.len().log_2() - split_var)) {
                        let mut chunk = chunk.to_vec();
                        let mut res: Vec<EdwardsProjective> = vec![];
                        while chunk.len() > 1 {
                            let (l, r) = chunk.split_at(chunk.len() / 2);
                            let tmp: EdwardsProjective = r.iter().sum();
                            if l.len() == 1 {
                                chunk = l.to_vec();
                            } else {
                                chunk = l.iter().zip_eq(r.iter()).map(|(a, b)| *a + *b).collect_vec();
                            }
                            res.push(tmp.into_affine().into());
                        }
                        res.push(chunk[0].into_affine().into());
                        chunk_results.push(res);
                    }

                    let mut chunk_results = (0..chunk_results[0].len()).map(|i| {
                        chunk_results.iter().rev().map(|v| v[i].clone()).collect_vec()
                    }).flatten().collect_vec();

                    chunk_results.reverse();

                    let tmp = output.iter().map(|p| p.vec()).collect_vec();
                    let mut output_vecs = tmp.as_slice();
                    let mut out_points = vec![];
                    while let Some(([out_x, out_y, out_z], _leftover)) = output_vecs.split_first_chunk::<3>() {
                        for (x, y, z) in multizip((out_x, out_y, out_z)) {
                            out_points.push(EdwardsProjective::new(*x, *y, x * y, *z));
                        }
                        output_vecs = _leftover;
                    }
                    //
                    // let mut map = HashMap::new();
                    //
                    // for i in 0..2048 {
                    //     map.insert(
                    //         EdwardsProjective::from(EdwardsProjective::generator().mul_bigint(BigInt::<4>::from(i as u64)).into_affine()),
                    //         i
                    //     );
                    // }
                    //
                    // let trs = trace.iter().zip(trace.iter().skip(1).chain(&[output])).zip(params.layers).filter(|(_, l)| {
                    //     match l {
                    //         TriangleAddLayer::Mapping(_) => false,
                    //         TriangleAddLayer::SplitAt(_, _) => true,
                    //     }
                    // }).map(|((i, o), _)| {
                    //     let tmp = i.iter().map(|p| p.clone().into_vec()).collect_vec();
                    //     let mut res_i = vec![];
                    //     for c in tmp.chunks(3) {
                    //         let part = multizip((&c[0], &c[1], &c[2])).map(|(x, y, z)| {
                    //             map.get(&EdwardsProjective::new(*x, *y, x * y, *z)).map_or("OTHER".to_string(), |i| format!("{}", i))
                    //         }).collect_vec();
                    //         res_i.push(part);
                    //     }
                    //     let tmp = o.iter().map(|p| p.clone().into_vec()).collect_vec();
                    //     let mut res_o = vec![];
                    //     for c in tmp.chunks(3) {
                    //         let part = multizip((&c[0], &c[1], &c[2])).map(|(x, y, z)| {
                    //             map.get(&EdwardsProjective::new(*x, *y, x * y, *z)).map_or("OTHER".to_string(), |i| format!("{}", i))
                    //         }).collect_vec();
                    //         res_o.push(part);
                    //     }
                    //     vec![res_i, res_o]
                    // }).collect_vec();
                    //
                    // dbg!(trs);
                    //
                    // let out = out_points.iter().map(|p| map.get(p).map_or("OTHER".to_string(), |i| format!("{}", i))).collect_vec();
                    // dbg!(out);
                    //
                    // let res = chunk_results.iter().map(|p| map.get(p).map_or("OTHER".to_string(), |i| format!("{}", i))).collect_vec();
                    // dbg!(res);

                    assert_eq!(out_points, chunk_results);

                }
            }
        }

        #[test]
        fn prover_vs_verifier() {
            let rng = &mut test_rng();
            let num_vars = 6;

            fn no_const_gen<RNG: Rng>(rng: &mut RNG, num_vars: usize) -> (FragmentedPoly<ark_ed_on_bls12_381_bandersnatch::EdwardsProjective>, [FragmentedPoly<Fr>; 3], usize, usize) {
                let split_var = rng.next_u64() as usize % (num_vars - 3);
                let sector_size: usize = 1 << (num_vars - 1 - split_var);
                let data_len = 1 << num_vars;

                let s = Shape::new(
                    vec![
                        Fragment {
                            mem_idx: 0,
                            len: data_len,
                            content: Data,
                            start: 0,
                        }
                    ],
                    1,
                );

                let shape = Arc::new(OnceLock::new());
                shape.get_or_init(|| s);

                let (points, data) = FragmentedPoly::rand_points_with_shape(rng, shape);
                (points, data, split_var, sector_size)
            }
            fn rng_gen<RNG: Rng>(rng: &mut RNG, num_vars: usize) -> (FragmentedPoly<ark_ed_on_bls12_381_bandersnatch::EdwardsProjective>, [FragmentedPoly<Fr>; 3], usize, usize) {
                let split_var = rng.next_u64() as usize % (num_vars - 3);
                let sector_size = 1 << (num_vars - 1 - split_var);
                let max_data_sectors_pairs = 1 << (split_var);
                let data_sectors = 2 * (rng.next_u64() as usize % max_data_sectors_pairs + 1);
                let data_len = data_sectors * sector_size;
                let consts_len = (1 << num_vars) - data_len;
                let mut num_consts = 0;

                let mut fragments = vec![
                    Fragment {
                        mem_idx: 0,
                        len: data_len,
                        content: Data,
                        start: 0,
                    }
                ];
                if consts_len != 0 {
                    fragments.push(
                        Fragment {
                            mem_idx: 0,
                            len: consts_len,
                            content: Consts,
                            start: data_len,
                        }
                    );
                    num_consts += 1;
                }

                let s = Shape::new(
                    fragments,
                    num_consts,
                );

                let shape = Arc::new(OnceLock::new());
                shape.get_or_init(|| s);

                let (points, data) = FragmentedPoly::rand_points_with_shape(rng, shape);
                (points, data, split_var, sector_size)
            }

            for gen in [no_const_gen, rng_gen] {
                for _ in 0..10 {

                    let (points, data, split_var, sector_size) = gen(rng, num_vars);

                    let input = data.to_vec();
                    let points_vec = points.vec();

                    let params = make_triangle_add_params(num_vars, split_var);
                    // dbg!(&params);
                    let num_splits = params.layers.iter().filter(|l|match l {
                        TriangleAddLayer::Mapping(_) => false,
                        TriangleAddLayer::SplitAt(_, _) => true,
                    }).count();
                    let point = (0..(num_vars - num_splits)).map(|_| Fr::rand(rng)).collect_vec();

                    let (trace, output) = TriangleAddProtocol::witness(input.clone(), &params);
                    let claims_to_reduce = to_multieval(EvalClaim {
                        evs: output.iter().map(|p| p.evaluate(&point)).collect(),
                        point,
                    });

                    let mut p_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::new());

                    let mut prover = TriangleAddProver::start(claims_to_reduce.clone(), trace, &params);
                    let mut res = None;
                    while res.is_none() {
                        let challenge = p_transcript.challenge_scalar(b"challenge_nextround");
                        res = prover.round(challenge, &mut p_transcript);
                    }
                    let (EvalClaim { point: proof_point, evs: proof_evs }, proof) = res.unwrap();

                    assert_eq!(proof_evs, input.iter().map(|p| p.evaluate(&proof_point)).collect_vec());

                    let mut v_transcript: IndexedProofTranscript<G1Projective, _> = IndexedProofTranscript::new(TestTranscript::as_this(&p_transcript.transcript));

                    let mut verifier = TriangleAddVerifier::start(
                        claims_to_reduce,
                        proof,
                        &params,
                    );

                    let mut res = None;
                    while res.is_none() {
                        let challenge = v_transcript.challenge_scalar(b"challenge_nextround");
                        res = verifier.round(challenge, &mut v_transcript);
                    }
                    let EvalClaim { point: verify_point, evs: verify_evs } = res.unwrap();

                    assert_eq!(proof_point, verify_point);
                    assert_eq!(proof_evs, verify_evs);
                }
            }
        }
    }
}
