// use std::marker::PhantomData;
// use ark_ff::PrimeField;
// use liblasso::poly::dense_mlpoly::DensePolynomial;
// use crate::protocol::{Challenge, Protocol, ProtocolProver, ProtocolVerifier, TranscriptReceiver};
// use crate::sumcheck_trait::{EvalClaim, MultiEvalClaim};
// 
// pub struct Split<F: PrimeField> {
//     _marker: PhantomData<F>,
// }
// 
// pub struct SplitProver<F: PrimeField> {
//     claims_to_reduce: <Self as ProtocolProver<F>>::ClaimsToReduce,
//     done: bool,
// }
// 
// pub struct SplitVerifier<F: PrimeField> {
//     claims_to_reduce: <Self as ProtocolVerifier<F>>::ClaimsToReduce,
//     done: bool,
// }
// 
// impl<F: PrimeField> Protocol<F> for Split<F> {
//     type Prover = SplitProver<F>;
//     type Verifier = SplitVerifier<F>;
//     type ClaimsToReduce = MultiEvalClaim<F>;
//     type ClaimsNew = EvalClaim<F>;
//     type Proof = ();
//     type Params = ();
//     type WitnessInput = Vec<DensePolynomial<F>>;
//     type Trace = Self::WitnessInput;
//     type WitnessOutput = Vec<(DensePolynomial<F>, DensePolynomial<F>)>;
// 
//     fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput) {
//         let num_vars = args[0].num_vars;
//         assert!(num_vars > 0);
//         for arg in &args {
//             assert!(arg.num_vars == num_vars);
//         }
// 
//         let mut ret = vec![];
// 
//         for arg in &args {
//             ret.push(arg.split(1 << (num_vars - 1)));
//         }
// 
//         (args, ret)
//     }
// }
// 
// impl<F: PrimeField> ProtocolProver<F> for SplitProver<F> {
//     type ClaimsToReduce = MultiEvalClaim<F>;
//     type ClaimsNew = EvalClaim<F>;
//     type Proof = ();
//     type Params = ();
//     type Trace = Vec<DensePolynomial<F>>;
// 
//     fn start(
//         claims_to_reduce: Self::ClaimsToReduce,
//         args: Self::Trace,
//         params: &Self::Params,
//     ) -> Self {
//         let num_vars = args[0].num_vars;
//         assert!(num_vars > 0);
//         for arg in args {
//             assert!(arg.num_vars == num_vars);
//         }
// 
//         Self { claims_to_reduce, done: false}
//     }
// 
//     fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
//                                        ->
//                                        Option<(Self::ClaimsNew, Self::Proof)> {
//         let Self{ claims_to_reduce, done } = self;
//         assert!(!*done);
//         *done = true;
//         let r = challenge.value;
//         let MultiEvalClaim { points, evs } = claims_to_reduce;
//         
//         let evs_new = evs.iter().map(|(x, y)| *x + r * (*y - x)).collect();
//         let mut r = vec![r];
//         r.extend(pt.iter());
//         Some(((r, evs_new), ()))
//     }
// }
// 
// impl<F: PrimeField> ProtocolVerifier<F> for SplitVerifier<F> {
//     type ClaimsToReduce = MultiEvalClaim<F>;
//     type ClaimsNew = EvalClaim<F>;
//     type Proof = ();
//     type Params = ();
// 
//     fn start(
//         claims_to_reduce: Self::ClaimsToReduce,
//         proof: Self::Proof,
//         params: &Self::Params,
//     ) -> Self {
//         Self { claims_to_reduce, done: false }
//     }
// 
//     fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
//                                        ->
//                                        Option<Self::ClaimsNew> {
//         let Self{ claims_to_reduce, done } = self;
//         assert!(!*done);
//         *done = true;
//         let r = challenge.value;
//         let (pt, evs) = claims_to_reduce;
//         let evs_new = evs.iter().map(|(x, y)| *x + r * (*y - x)).collect();
//         let mut r = vec![r];
//         r.extend(pt.iter());
//         Some((r, evs_new))
//     }
// }
