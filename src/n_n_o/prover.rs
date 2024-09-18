// use super::*;

// pub struct NNSumcheckPolyMapProver<F: PrimeField> {
//     pub sumcheckable: Option<Box<dyn Sumcheckable<F>>>,
//     pub polys: Option<Vec<FragmentedPoly<F>>>,
//     pub mapping: PolynomialMapping<F>,
//     pub ev_folded: Option<F>,
//     pub num_vars: usize,
//     pub claims: MultiEvalClaim<F>,
//     pub rs: Vec<F>,
//     pub round_polys: Option<Vec<CompressedUniPoly<F>>>,
// }


// impl<F: PrimeField> Sumcheckable<F> for NNFragmentedLincomb<F> {
//     fn split(&mut self) {
//         if self.splits.is_some() {
//             return;
//         }
//         let (lpolys, rpolys): (Vec<FragmentedPoly<F>>, Vec<FragmentedPoly<F>>) = self.polys.par_iter().map(|p| p.split()).unzip();
//         self.splits = Some(NNSplits {
//             lpolys,
//             rpolys,
//         })
//     }

//     fn bind(&mut self, f: &F) {
//         self.split();
//         let NNSplits { mut lpolys, rpolys, .. } = self.splits.take().unwrap();

//         lpolys.par_iter_mut().zip(rpolys.par_iter()).map(|(l, r)| {
//             l.bind_from(r, f);
//         }).count();
//         self.polys = lpolys;

//     }

//     fn unipoly(&mut self) -> UniPoly<F> {
//         self.split();
//         let NNSplits { lpolys, rpolys, } = self.splits.take().unwrap();

//         let poly_diffs = lpolys
//             .par_iter()
//             .zip(rpolys.par_iter())
//             .map(|(l, r)| r -l )
//             .collect::<Vec<_>>();


//         let mut poly_extensions = Vec::with_capacity(self.degree);


//         let mut last_poly = &rpolys;

//         for i in 0..self.degree {
//             poly_extensions.push(last_poly.clone());
//             poly_extensions[i].par_iter_mut().zip(poly_diffs.par_iter()).map(|(p, d)| p.add_assign(d)).count();
//             last_poly = poly_extensions.last().unwrap();

//         }

//         let folded = self.folded_f.as_ref().unwrap().clone();
//         let poly_ext_iter = once(&lpolys).chain(once(&rpolys)).chain(poly_extensions.par_iter());
//         let results = poly_ext_iter.map(|polys| {
//             let tmp = (0..polys[0].items_len()).into_par_iter().map(|i| {
//                 folded(&polys.iter().map(|p| p[i]).collect_vec())
//             }).collect::<Vec<_>>();
//             tmp.par_iter().sum()
//         }).collect::<Vec<F>>();

//         self.splits = Some(NNSplits {
//             lpolys,
//             rpolys,
//         });
//         UniPoly::from_evals(&results)
//     }

//     fn final_evals(&self) -> Vec<F> {
//         self.polys.par_iter().map(|poly| poly[0]).collect()
//     }
// }



// impl<F: PrimeField> ProtocolProver<F> for NNSumcheckPolyMapProver<F> {
//     type ClaimsToReduce = MultiEvalClaim<F>;
//     type ClaimsNew = EvalClaim<F>;
//     type Proof = NNSumcheckPolyMapProof<F>;
//     type Params = NNSumcheckPolyMapParams<F>;
//     type Trace = Vec<Vec<FragmentedPoly<F>>>;

//     fn start(claims_to_reduce: Self::ClaimsToReduce, args: Self::Trace, params: &Self::Params) -> Self {
//         assert_eq!(args[0].len(), params.f.num_i);

//         Self {
//             sumcheckable: None,
//             polys: Some(args[0].clone()),
//             mapping: params.f.clone(),
//             claims: claims_to_reduce,
//             ev_folded: None,
//             num_vars: params.num_vars,
//             rs: vec![],
//             round_polys: Some(vec![]),
//         }
//     }

//     fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T) -> Option<(Self::ClaimsNew, Self::Proof)> {
//         match &mut self.sumcheckable {
//             None => {
//                 let gamma = challenge.value;
//                 let gamma_pows = make_gamma_pows(&self.claims, gamma);


//                 let polys = self.polys.take().unwrap();
//                 let shape = polys[0].shape.clone();
//                 self.sumcheckable = Some(Box::new(NNFragmentedLincomb {
//                     polys,
//                     splits: None,
//                     folded_f: Some(make_folded_f(&self.claims, &gamma_pows, &self.mapping)),
//                     degree: self.mapping.degree,
//                 }));
//             }
//             Some(s) => {
//                 let r_j = challenge.value;
//                 fix_var_bot(&mut self.rs, r_j);
//                 s.bind(&r_j);

//                 if self.rs.len() == self.num_vars {
//                     let final_evaluations: Vec<F> = s.final_evals();

//                     transcript.append_scalars(b"sumcheck_final_evals", &final_evaluations[0..self.mapping.num_i]);

//                     return Some((
//                         EvalClaim{
//                             point: self.rs.clone(),
//                             evs: final_evaluations[0..self.mapping.num_i].to_vec(),
//                         },
//                         NNSumcheckPolyMapProof{
//                             round_polys : self.round_polys.take().unwrap(),
//                             final_evaluations : final_evaluations[0..self.mapping.num_i].to_vec(),
//                         }
//                     ))
//                 }
//             }
//         }

//         let round_uni_poly = self.sumcheckable.as_mut().unwrap().unipoly();
//         // let round_uni_poly = UniPoly::from_evals(&vec![F::zero(); self.mapping.degree + 2]);

//         // append the prover's message to the transcript
//         transcript.append_scalars(b"poly", &round_uni_poly.as_vec());
//         // and to proof
//         self.round_polys.as_mut().unwrap().push(round_uni_poly.compress());

//         None

//     }
// }

