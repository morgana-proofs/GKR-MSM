pub mod fns {
	use ark_std::One;
	use ark_bls12_381::Fq;
	use ark_ff::{Field, MontFp};

	const B3: Fq = MontFp!("12");

	pub fn projective_bls12_381_double(pts: &[Fq]) -> Vec<Fq> {
		// https://eprint.iacr.org/2015/1060 -- Algorithm 9

		assert_eq!(pts.len(), 3);
		let &[x, y, z] = pts.try_into().unwrap();

		let t0 = y.double();
		let z3 = t0.double();
		let z3 = z3.double();

		let z3 = z3.double();
		let t1 = y * z;
		let t2 = z.double();

		let t2 = B3 * t2;
		let x3 = t2 * z3;
		let y3 = t0 + t2;

		let z3 = t1 * z3;
		let t1 = t2.double();
		let t2 = t1 + t2;

		let t0 = t0 - t2;
		let y3 = t0 * y3;
		let y3 = x3 + y3;

		let t1 = x * y;
		let x3 = t0 * t1;
		let x3 = x3.double();

		vec![x3, y3, z3]
	}

	pub fn projective_bls12_381_add(pts: &[Fq]) -> Vec<Fq> {
		// https://eprint.iacr.org/2015/1060 -- Algorithm 7

		assert_eq!(pts.len(), 6);
		let &[x1, y1, z1, x2, y2, z2] = pts.try_into().unwrap();

		let t0 = x1 * x2;
		let t1 = y1 * y2;
		let t2 = z1 * z2;

		let t3 = x1 + y1;
		let t4 = x2 + y2;
		let t3 = t3 * t4;

		let t4 = t0 + t1;
		let t3 = t3 - t4;
		let t4 = y1 + z1;

		let x3 = y2 + z2;
		let t4 = t4 * x3;
		let x3 = t1 + t2;

		let t4 = t4 - x3;
		let x3 = x1 + z1;
		let y3 = x2 + z2;

		let x3 = x3 * y3;
		let y3 = t0 + t2;
		let y3 = x3 - y3;

		let x3 = t0.double();
		let t0 = x3 + t0;
		let t2 = B3 * t2;

		let z3 = t1 + t2;
		let t1 = t1 - t2;
		let y3 = B3 * y3;

		let x3 = t4 * y3;
		let t2 = t3 * t1;
		let x3 = t2 - x3;

		let y3 = y3 * t0;
		let t1 = t1 * z3;
		let y3 = t1 + y3;

		let t0 = t0 * t3;
		let z3 = z3 * t4;
		let z3 = z3 + t0;

		vec![x3, y3, z3]
	}

	// TODO: there are several things to optimize here.
	//       1. some layers may use affine functions
	//       2. degrees vastly differ across input and output variables
	
	/// Double-and-add over the BLS12-381 curve.
	///
	/// In: 7; Out: 6.
	/// dna(x_p, y_p, z_p, x, y, z, b) = (add(double(x_p, y_p, z_p), choice(b, x, y, z)), x, y, z), where
	///
	/// add      := projective_bls12_381_add
	/// double   := projective_bls12_381_double
	/// choice   := b * (x : y : z) + (1 - b) * (0 : 1 : 0) = (choice_1, choice_2, choice_3)
	/// choice_1 := b * x
	/// choice_2 := b * y + 1 - b
	/// choice_3 := b * z
	///
	/// deg add = deg double = (2, 2)
	/// deg choice = 2
	/// => deg dna = 12
	pub fn projective_bls12_381_double_and_add(pts: &[Fq]) -> Vec<Fq> {
		assert_eq!(pts.len(), 7);
		let &[x_prev, y_prev, z_prev, x, y, z, bit] = pts.try_into().unwrap();

		let mut next = projective_bls12_381_double(&[x_prev, y_prev, z_prev]);

		if bit.is_one() {
			next = projective_bls12_381_add(&[next[0], next[1], next[2], x, y, z])
		}

		next.reserve(3);
		next.push(x);
		next.push(y);
		next.push(z);

		next
	}
}

pub mod algfns {
	// TODO: make_algfn should respect generic bounds for fns.
	/// This macro assumes there exists a super::fns mod with respectively named functions in it.
	macro_rules! make_algfn {
		($struct_name:ident($deg:expr, $n_ins:expr, $n_outs:expr)) => {
			#[derive(Copy, Clone)]
			#[allow(non_camel_case_types)]
			pub struct $struct_name(std::marker::PhantomData<ark_bls12_381::Fq>);

			impl $struct_name {
				pub const fn new() -> Self {
					Self(std::marker::PhantomData)
				}
			}

			impl $crate::cleanup::utils::algfn::AlgFn<ark_bls12_381::Fq> for $struct_name {
				fn deg(&self) -> usize {
					$deg
				}

				fn n_ins(&self) -> usize {
					$n_ins
				}

				fn n_outs(&self) -> usize {
					$n_outs
				}

				fn exec(&self, args: &impl std::ops::Index<usize, Output=ark_bls12_381::Fq>) -> impl std::iter::Iterator<Item=ark_bls12_381::Fq> {
					let args: std::vec::Vec<_> = std::iter::Iterator::collect(std::iter::Iterator::map(0..(self.n_ins()), |i| args[i]));

					super::fns::$struct_name(&args).into_iter()
				}
			}
		}
	}

	make_algfn!(projective_bls12_381_double_and_add(12, 7, 6));
}

pub mod gkr {
    use std::marker::PhantomData;

    use crate::cleanup::{polys::common::MapSplit, proof_transcript::ProofTranscript2, protocols::sumcheck::{BareSumcheck, DenseEqSumcheck, DenseEqSumcheckObject, DenseSumcheckObject, SumClaim}, utils::algfn::{IdAlgFn, StackedAlgFn}};

	use ark_bls12_381::Fq;
	use ark_ff::PrimeField;

	use crate::cleanup::{proof_transcript::TProofTranscript2, protocols::{gkrs::{gkr::GKRLayer, scmul::algfns::projective_bls12_381_double_and_add}, sumcheck::{GenericSumcheckProtocol, SinglePointClaims}}, utils::algfn::{AlgFn, AlgFnUtils}};
	use crate::cleanup::protocol2::Protocol2;

	static DNA: projective_bls12_381_double_and_add = projective_bls12_381_double_and_add::new();

	type LayerAlgFn = StackedAlgFn<Fq, projective_bls12_381_double_and_add, IdAlgFn<Fq>>;
	
	pub struct ScalarMulGKRParallelPart {
		num_towered_dnas: usize, // num_layers = num_towered_dnas + 1
		log_num_towers: usize, // parallelization degree, number of subcircuits
	}

	impl ScalarMulGKRParallelPart {
		pub fn new(num_towered_dnas: usize, log_num_towers: usize) -> Self {
			Self { num_towered_dnas, log_num_towers }
		}

		/// Returns an algfn used when transitioning from layer `i` to layer `i + 1`.
		/// Layers are numbered from bottom to top, starting from the input layer at 0.
		pub fn algfn_for_layer(&self, i: usize) -> LayerAlgFn {
			debug_assert!(i < self.num_towered_dnas);
			// transitioning to layer i, we need to copy num_towered_dnas - i - 1 bits:
			// at layer i we've eaten i bits from the input (as each layer transition uses one dna),
			// there were num_towered_dnas bits at the beginning, and one bit will go into current dna.
			StackedAlgFn::new(DNA, IdAlgFn::new(self.num_towered_dnas - i - 1))
		}
		
		/// Returns a vector of polynomials at each layer.
		/// Layers are numbered from bottom to top, starting from the input layer at 0.
		/// Polys are first indexed by the subcircuit dimension,
		/// then by transition function's input index (as expected by `Vec::algfn_map`).
		pub fn generate_witness(&self, polys: Vec<Vec<Fq>>) -> Vec<Vec<Vec<Fq>>> {
			let mut witness = Vec::with_capacity(self.num_towered_dnas + 1);
			witness.push(polys);
			for i in 1..self.num_towered_dnas + 1 {
				let fun = self.algfn_for_layer(i - 1);
				let next = Vec::algfn_map(&witness[i - 1], fun);
				witness.push(next);
			}

			witness
		}
	}

	impl<Tr: TProofTranscript2> Protocol2<Tr> for ScalarMulGKRParallelPart {
		type ProverInput = Vec<Vec<Fq>>;

		type ProverOutput = ();

		type ClaimsBefore = SinglePointClaims<Fq>;

		type ClaimsAfter = SinglePointClaims<Fq>;

		fn prove(&self, transcript: &mut Tr, mut claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
			let witness = self.generate_witness(advice);

			for i in (0..self.num_towered_dnas).rev() {
				let fun = self.algfn_for_layer(i);
				let layer_advice = witness[i].clone();
				
				let proto = DenseEqSumcheck::new(fun, self.log_num_towers);
				claims = proto.prove(transcript, claims, layer_advice).0;
			}
			
			(claims, ())
		}

		fn verify(&self, transcript: &mut Tr, mut claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
			for i in (0..self.num_towered_dnas).rev() {
				let fun = self.algfn_for_layer(i);
				
				let proto = DenseEqSumcheck::new(fun, self.log_num_towers);
				claims = proto.verify(transcript, claims);
			}

			claims
		}
    }

	struct ScalarMulGKR {
		num_towered_dnas: usize,
		num_towers: usize,
	}

	impl ScalarMulGKR {
		pub fn new(num_towered_dnas: usize, num_towers: usize) -> Self {
			Self { num_towered_dnas, num_towers }
		}
	}

	impl<Tr: TProofTranscript2> Protocol2<Tr> for ScalarMulGKR {
		type ProverInput = Vec<Vec<Fq>>;

		type ProverOutput = ();

		type ClaimsBefore = SinglePointClaims<Fq>;

		type ClaimsAfter = SinglePointClaims<Fq>;

		fn prove(&self, transcript: &mut Tr, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
			todo!()
		}

		fn verify(&self, transcript: &mut Tr, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
			todo!()
		}
	}
}

#[cfg(test)]
mod test {
	use std::{iter::repeat_with, ops::Mul};

	use ark_ec::Group;
	use ark_bls12_381::{Fq, G1Projective as G, Fr as F};
	use ark_std::{test_rng, UniformRand, One};
	use itertools::Itertools;
	
	use crate::cleanup::{proof_transcript::{ProofTranscript2, TProofTranscript2}, protocol2::Protocol2, protocols::sumcheck::SinglePointClaims, utils::arith::evaluate_poly};

use super::gkr::ScalarMulGKRParallelPart;

	#[test]
	fn test_prove_and_verify_claims_parallel_part() {
		let mut rng = test_rng();

		let pt = G::rand(&mut rng);
		let scalar = F::from(1337); // hi 010 100 111 001 lo
		let result_pt = pt * scalar;
		let result = vec![result_pt.x, result_pt.y, result_pt.z];

		let bits = [0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1];
		let bits: Vec<Vec<_>> = bits.chunks(3).map(|chunk| chunk.into_iter().map(|&bit| Fq::from(bit)).collect()).collect();

		let input = {
			let mut input = Vec::new();
			let mut running_pt = pt;
			for (i, chunk) in bits.iter().enumerate() {
				input.push(Vec::new());
				// input point
				input[i].push(running_pt.x);
				input[i].push(running_pt.y);
				input[i].push(running_pt.z);

				// initial point
				input[i].push(pt.x);
				input[i].push(pt.y);
				input[i].push(pt.z);
				
				for &bit in chunk {
					input[i].push(bit);
					
					running_pt.double();
					if bit.is_one() {
						running_pt += pt;
					}
				}
			}

			let rows = input.len();
			let cols = input[0].len();

			let transposed: Vec<Vec<_>> = (0..cols).map(|col| {
				(0..rows)
					.map(|row| input[row][col])
					.collect()
			}).collect();

			transposed
		};
		
		let proto = ScalarMulGKRParallelPart::new(3, 2);
		
		let witness = proto.generate_witness(input.clone());
		let claims = {
			let point: Vec<_> = repeat_with(|| Fq::rand(&mut rng)).take(2).collect();
			let evs: Vec<_> = witness.last().unwrap().iter().map(|poly| evaluate_poly(poly, &point)).collect();
			SinglePointClaims { evs, point }
		};
		
		let (prover_output_claims, proof) = {
			let mut transcript_p = ProofTranscript2::start_prover(b"rulonoboev");
			let advice = witness.first().unwrap().clone();
			
			(proto.prove(&mut transcript_p, claims.clone(), advice).0, transcript_p.end())
		};
		let mut transcript_v = ProofTranscript2::start_verifier(b"rulonoboev", proof);
		let verifier_output_claims = proto.verify(&mut transcript_v, claims);

		assert_eq!(prover_output_claims, verifier_output_claims);
	}
}
