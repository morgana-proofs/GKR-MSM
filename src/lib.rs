#![feature(generic_const_exprs)]

use ark_bls12_381::Fr;
use ark_ec::{bls12::Bls12, pairing::Pairing, CurveGroup};
use ark_ff::{BigInt, Field, PrimeField};
use ark_std::iterable::Iterable;
use liblasso::{poly::{eq_poly::EqPolynomial, dense_mlpoly::DensePolynomial}, subprotocols::sumcheck::SumcheckInstanceProof, utils::transcript::ProofTranscript};
use merlin::Transcript;
use core::num;
use std::marker::PhantomData;
use liblasso::utils::math::Math;
use rayon::{current_num_threads, join, prelude::*, scope, spawn};

type C = <Bls12<ark_bls12_381::Config> as Pairing>::G1;


pub trait TwistedEdwardsConfig {

    const COEFF_D: Self;

    fn mul_by_a(&self) -> Self;

    fn mul_by_d(&self) -> Self;
}

pub struct BandersnatchConfig {}



impl TwistedEdwardsConfig for Fr {

    const COEFF_D: Self = Self {
        0: BigInt([12167860994669987632, 4043113551995129031, 6052647550941614584, 3904213385886034240]), 
        1: PhantomData
    };
    
    #[inline(always)]
    fn mul_by_a(&self) -> Self {
        let t = (*self).double().double();
        -(t + *self)
    }

    #[inline(always)]
    fn mul_by_d(&self) -> Self {
        *self * Self::COEFF_D
    }
}


pub fn affine_twisted_edwards_add_l1<F: Field + TwistedEdwardsConfig>(pts: &[F; 4]) -> [F; 3]  {
    let [x1, y1, x2, y2] = pts;
    [*x1 * y2, *x2 * y1, *y1 * y2 - (*x1 * x2).mul_by_a()]
}

pub fn affine_twisted_edwards_add_l2<F: Field + TwistedEdwardsConfig>(pts: &[F; 3]) -> [F; 3]  {
    let [x1y2, x2y1, y1y2_ax1x2] = pts;
    [(*x1y2 + x2y1), *y1y2_ax1x2, *x1y2 * x2y1]
}

pub fn affine_twisted_edwards_add_l3<F: Field + TwistedEdwardsConfig>(pts: &[F; 3]) -> [F; 3]  {
    let [X, Y, XY] = pts;
    let dXY = XY.mul_by_d();
    let Z2_dXY = F::one() - dXY;
    let Z2__dXY = F::one() + dXY;
    [Z2_dXY * X, Z2__dXY * Y, Z2_dXY * Z2__dXY]
}

pub fn affine_twisted_edwards_add<F: Field + TwistedEdwardsConfig>(pts: &[F; 4]) -> [F; 3] {
    affine_twisted_edwards_add_l3(&affine_twisted_edwards_add_l2(&affine_twisted_edwards_add_l1(pts)))
}


pub fn twisted_edwards_add_l1<F: Field + TwistedEdwardsConfig>(pts: &[F; 6]) -> [F; 4]  {
    let [x1, y1, z1, x2, y2, z2] = pts;
    [*x1 * y2, *x2 * y1, *y1 * y2 - (*x1 * x2).mul_by_a(), *z1 * z2]
}

pub fn twisted_edwards_add_l2<F: Field + TwistedEdwardsConfig>(pts: &[F; 4]) -> [F; 4]  {
    let [x1y2, x2y1, y1y2_ax1x2, z1z2] = pts;
    [(*x1y2 + x2y1) * z1z2, *y1y2_ax1x2 * z1z2, z1z2.square(), *x1y2 * x2y1]
}

pub fn twisted_edwards_add_l3<F: Field + TwistedEdwardsConfig>(pts: &[F; 4]) -> [F; 3]  {
    let [X, Y, Z2, XY] = pts;
    let dXY = XY.mul_by_d();
    let Z2_dXY = *Z2 - dXY;
    let Z2__dXY = *Z2 + dXY;
    [Z2_dXY * X, Z2__dXY * Y, Z2_dXY * Z2__dXY]
}

pub fn twisted_edwards_add<F: Field + TwistedEdwardsConfig>(pts: &[F; 6]) -> [F; 3] {
    twisted_edwards_add_l3(&twisted_edwards_add_l2(&twisted_edwards_add_l1(pts)))
}


pub fn scale<F: Field + TwistedEdwardsConfig, const ALPHA: usize, const BETA: usize>(f: fn (&[F; ALPHA - 1]) -> [F; BETA]) -> impl Fn (&[F; ALPHA]) -> [F; BETA] {
    move |data: &[F; ALPHA]| -> [F; BETA] {
        let (pts, factor) = data.split_at(ALPHA);
        f(pts.try_into().unwrap()).map(|p| p * factor[0])
    }
}

// GKR

struct FirstLayer<F: Field + TwistedEdwardsConfig> {
    pub deg2: [DensePolynomial<F>; 3],
    pub deg4: [DensePolynomial<F>; 3],
    pub deg8: [DensePolynomial<F>; 3],
}

struct InnerLayer<F: Field + TwistedEdwardsConfig> {
    pub deg2: [DensePolynomial<F>; 4],
    pub deg4: [DensePolynomial<F>; 4],
    pub deg8: [DensePolynomial<F>; 3],
}

struct GrandAddCircuit<F: Field + TwistedEdwardsConfig> {
    pub input: [DensePolynomial<F>; 2],
    pub first: FirstLayer<F>,
    pub inner: Vec<InnerLayer<F>>,
}

pub fn split_vecs<F: PrimeField, const ALPHA: usize>(ins: &[DensePolynomial<F>; ALPHA]) -> [DensePolynomial<F>; ALPHA * 2] {
    let mut res = Vec::<DensePolynomial::<F>>::with_capacity(ALPHA * 2);
    for _i in 0..(ALPHA * 2) {
        res.push(DensePolynomial::new(vec![]))
    }

    ins.iter().enumerate().map(|(idx, poly)| (res[idx], res[ALPHA + idx]) = poly.split(poly.len() / 2)).count();
    res.try_into().unwrap()
}


/// This utility function will parallelize an operation that is to be
/// performed over a mutable slice. Stolen from halo2 backend.
pub fn parallelize<T: Send + Sync + ark_std::fmt::Debug, F: Fn( &[&[T]], &mut[&mut[T]], usize) + Send + Sync + Clone, const ALPHA: usize, const BETA: usize>(
    v: & [& [T]; ALPHA],
    t: &mut [&mut[T]; BETA],
    f: F
) {
    let f = &f;
    let total_iters = v[0].len();
    let num_threads = current_num_threads();
    let base_chunk_size = total_iters / num_threads;
    let cutoff_chunk_id = total_iters % num_threads;
    let split_pos = cutoff_chunk_id * (base_chunk_size + 1);
    
    let mut v : Vec<_> = v.into_iter().collect();
    let mut t : Vec<_> = t.into_iter().collect();

    println!("Source {:?}", v);
    println!("Target {:?}", t);

    let (mut v_hi, mut v_lo) : (Vec<_>, Vec<_>) = v.into_iter().map(|v|v.split_at(split_pos)).unzip();
    let (mut t_hi, mut t_lo) : (Vec<_>, Vec<_>) = t.into_iter().map(|t|t.split_at_mut(split_pos)).unzip();

    println!("Source_hi {:?}", v_hi);
    println!("Target_hi {:?}", t_hi);

    println!("Source_lo {:?}", v_lo);
    println!("Target_lo {:?}", t_lo);


    scope(|scope| {
        // Skip special-case: number of iterations is cleanly divided by number of threads.
        if cutoff_chunk_id != 0 {

            for chunk_id in 0 .. total_iters % num_threads {
                let mut v_hi_chunked : Vec<_> = v_hi.iter()
                    .map(|v_hi_coord| v_hi_coord.chunks_exact(base_chunk_size + 1)).collect();

            }

            for (chunk_id, chunk) in 
                v_hi
                    .chunks_exact(base_chunk_size + 1)
                    .zip(t_hi.chunks_exact_mut(base_chunk_size + 1))
                    .enumerate()
                {
                    let offset = chunk_id * (base_chunk_size + 1);
                    scope.spawn(move |_| f(chunk.0, chunk.1, offset));
                }
        }
       // Skip special-case: less iterations than number of threads.
        if base_chunk_size != 0 {
            for (chunk_id, chunk) in 
                v_lo.chunks_exact(base_chunk_size)
                    .zip(t_lo.chunks_exact_mut(base_chunk_size))
                    .enumerate()
                {
                    let offset = chunk_id * base_chunk_size;
                    scope.spawn(move |_| f(chunk.0, chunk.1, offset));
                }
    }
    });
}



pub fn map_over_arrays<F: PrimeField, const ALPHA: usize, const BETA: usize>(
    ins: & [&[F]; ALPHA],
    outs: &mut [&mut [F]; BETA],
    f: impl Fn(&[F; ALPHA]) -> [F; BETA] + Send + Sync + Clone
) -> () {
    parallelize(
        ins,
        outs,
        |ins, outs, _| {
            let n = ins[0].len();
            println!("n={}", n);
            println!("ins={:?}", ins);
            let mut args = [F::zero(); ALPHA];
            for i in 0..n {
                for j in 0..ALPHA {
                    args[j] = ins[j][i];
                }
                let res = f(&args);
                for j in 0..BETA {
                    outs[j][i] = res[j]
                }
            }
        }
    );
}
// pub fn map_over_poly<F: PrimeField, const ALPHA: usize, const BETA: usize>(
//     ins: &[DensePolynomi

// pub fn map_over_poly<F: PrimeField, const ALPHA: usize, const BETA: usize>(
//     ins: &[DensePolynomial<F>; ALPHA],
//     f: impl Fn(&[F; ALPHA]) -> [F; BETA] + Send + Sync + Clone
// ) -> [DensePolynomial<F>; BETA] {
//     let array_ins: [&[F]; ALPHA] = ins.each_ref().map(|p| p.vec().as_slice());
//     let mut vec_outs = Vec::with_capacity(BETA);
//     for i in 0..BETA {
//         vec_outs.push(Vec::with_capacity(ins[0].len()));
//         vec_outs[i].resize(ins[0].len(), F::zero());
//     }
//     let mut array_outs: [&mut [F]; BETA] = vec_outs.iter_mut().map(|v| v.as_mut_slice()).collect::<Vec<&mut [F]>>().try_into().unwrap();
//     map_over_arrays(&array_ins, &mut array_outs, f);
//     vec_outs.into_iter().map(|v| DensePolynomial::new(v)).collect::<Vec<DensePolynomial<F>>>().try_into().unwrap()
// }

pub fn map_over_poly<F: PrimeField, const ALPHA: usize, const BETA: usize>(
    ins: &[DensePolynomial<F>; ALPHA],
    f: impl Fn(&[F; ALPHA]) -> [F; BETA] + Send + Sync + Clone
) -> [DensePolynomial<F>; BETA] {
    let ins_refs = ins.each_ref();
    let applications: Vec<[F; BETA]> = (0..ins[0].len()).into_par_iter()
        .map(|idx| {
            f(&ins_refs.map(|p| p[idx]))
        }).collect();
    (0..BETA).into_iter()
        .map(|idx| {
            DensePolynomial::new(applications.iter().map(|v| v[idx]).collect())
    }).collect::<Vec<DensePolynomial::<F>>>().try_into().unwrap()
}



impl<F: PrimeField + TwistedEdwardsConfig> GrandAddCircuit<F> {
    pub fn new(x: &DensePolynomial<F>, y: &DensePolynomial<F>) -> Self {
        assert_eq!(x.len(), y.len());
        
        let num_layers = x.len().log_2() as usize;
        assert_eq!(x.len(), 1 << num_layers);

        let input = [x.clone(), y.clone()];
        let deg1 = split_vecs(&input);
        let deg2 = map_over_poly(&deg1, affine_twisted_edwards_add_l1);
        let deg4 = map_over_poly(&deg2, affine_twisted_edwards_add_l2);
        let deg8 = map_over_poly(&deg4, affine_twisted_edwards_add_l3);
        let mut inner_deg1 = split_vecs(&deg8);
        let first_layer = FirstLayer {deg2, deg4, deg8};

        let mut inner_layers = Vec::with_capacity(num_layers - 1);

        for _ in 1..num_layers {
            let inner_deg2 = map_over_poly(&inner_deg1, twisted_edwards_add_l1);
            let inner_deg4 = map_over_poly(&inner_deg2, twisted_edwards_add_l2);
            let inner_deg8 = map_over_poly(&inner_deg4, twisted_edwards_add_l3);
            inner_deg1 = split_vecs(&inner_deg8);
            inner_layers.push(InnerLayer {
                deg2: inner_deg2,
                deg4: inner_deg4,
                deg8: inner_deg8,
            });
        }
    
        GrandAddCircuit {
            input,
            first: first_layer,
            inner: inner_layers,
        }
    }
}

struct FirstLayerProof<F: PrimeField + TwistedEdwardsConfig> {
    deg8_claim: [F; 3],
    deg8_proof: SumcheckInstanceProof<F>,
    deg4_claim: [F; 3],
    deg4_proof: SumcheckInstanceProof<F>,
    deg2_claim: [F; 3],
    deg2_proof: SumcheckInstanceProof<F>,
}

struct InnerLayerProof<F: PrimeField + TwistedEdwardsConfig> {
    deg8_claim: [F; 3],
    deg8_proof: SumcheckInstanceProof<F>,
    deg4_claim: [F; 4],
    deg4_proof: SumcheckInstanceProof<F>,
    deg2_claim: [F; 4],
    deg2_proof: SumcheckInstanceProof<F>,
}

struct GrandAddArgument<F: PrimeField + TwistedEdwardsConfig> {
    final_claim: [F; 2],
    first: FirstLayerProof<F>,
    inner: Vec<InnerLayerProof<F>>,
}

impl<F: PrimeField + TwistedEdwardsConfig> GrandAddArgument<F> {
  pub fn prove<G>(
    grand_add_circuit: &mut GrandAddCircuit<F>,
    transcript: &mut Transcript,
    mut rand: Vec<F>,
  ) -> Self
  where
    G: CurveGroup<ScalarField = F>,
  {
        let GrandAddCircuit{input, first, inner} = grand_add_circuit;
        let FirstLayer{deg2: first_deg2, deg4: first_deg4, deg8: first_deg8} = first;
        let first_layer_proof: FirstLayerProof<F>;
        let mut inner_layers_proofs: Vec<InnerLayerProof<F>> = Vec::new();
        let final_claim;
        let num_inner_layers = inner.len();

        let mut deg8_claim = if num_inner_layers > 0{
            inner.last().unwrap().deg8.each_ref().map(|p| p.evaluate(&rand))
        } else {
            first_deg8.each_ref().map(|p| p.evaluate(&rand))
        };

        for inner_layer_id in (0..num_inner_layers).rev() {
            let mut polys: Vec<DensePolynomial<F>> = inner[inner_layer_id].deg4.to_vec();
            polys.push(DensePolynomial::new(EqPolynomial::<F>::new(rand.clone()).evals()));

            let (deg8_proof, _rand, evals, gamma) = SumcheckInstanceProof::prove_arbitrary_vec::<_, G, _, 5, 3>(
                &deg8_claim,
                0,
                &mut polys.try_into().unwrap(),
                scale(twisted_edwards_add_l3),
                3,
                transcript,
            );
            rand = _rand;

            let deg4_claim = evals.try_into().unwrap();

            polys = inner[inner_layer_id].deg2.to_vec();
            polys.push(DensePolynomial::new(EqPolynomial::<F>::new(rand.clone()).evals()));

            let (deg4_proof, _rand, evals, gamma) = SumcheckInstanceProof::prove_arbitrary_vec::<_, G, _, 5, 4>(
                &deg4_claim,
                0,
                &mut polys.try_into().unwrap(),
                scale(twisted_edwards_add_l2),
                3,
                transcript,
            );
            rand = _rand;

            let deg2_claim = evals.try_into().unwrap();

            if inner_layer_id == 0 {
                polys = split_vecs(&first_deg8).to_vec();
            } else {
                polys = split_vecs(&inner[inner_layer_id - 1].deg8).to_vec();
            }

            polys.push(DensePolynomial::new(EqPolynomial::<F>::new(rand.clone()).evals()));

            let (deg2_proof, _rand, evals, gamma) = SumcheckInstanceProof::prove_arbitrary_vec::<_, G, _, 7, 4>(
                &deg2_claim,
                0,
                &mut polys.try_into().unwrap(),
                scale(twisted_edwards_add_l1),
                3,
                transcript,
            );
            rand = _rand;

            inner_layers_proofs.push(InnerLayerProof {
                deg8_proof,
                deg8_claim,
                deg4_proof,
                deg4_claim,
                deg2_proof,
                deg2_claim,
            });
            let layer_coef = <Transcript as ProofTranscript<G>>::challenge_scalar(transcript, b"challenge_layer_coef");
    
            deg8_claim = (0..3)
                .map(|i| evals[i] + layer_coef * (evals[i] - evals[3 + i]))
                .collect::<Vec<F>>().try_into().unwrap();

            let mut ext = vec![layer_coef];
            ext.extend(rand);
            rand = ext
        }

        { // First layer
            let mut polys: Vec<DensePolynomial<F>> = first_deg4.to_vec();
            polys.push(DensePolynomial::new(EqPolynomial::<F>::new(rand.clone()).evals()));

            let (deg8_proof, _rand, evals, gamma) = SumcheckInstanceProof::prove_arbitrary_vec::<_, G, _, 4, 3>(
                &deg8_claim,
                0,
                &mut polys.try_into().unwrap(),
                scale(affine_twisted_edwards_add_l3),
                3,
                transcript,
            );
            rand = _rand;

            let deg4_claim = evals.try_into().unwrap();

            polys = first_deg2.to_vec();
            polys.push(DensePolynomial::new(EqPolynomial::<F>::new(rand.clone()).evals()));

            let (deg4_proof, _rand, evals, gamma) = SumcheckInstanceProof::prove_arbitrary_vec::<_, G, _, 4, 3>(
                &deg4_claim,
                0,
                &mut polys.try_into().unwrap(),
                scale(affine_twisted_edwards_add_l2),
                3,
                transcript,
            );
            rand = _rand;

            let deg2_claim = evals.try_into().unwrap();

            polys = split_vecs(&input).to_vec();
            polys.push(DensePolynomial::new(EqPolynomial::<F>::new(rand.clone()).evals()));

            let (deg2_proof, _rand, evals, gamma) = SumcheckInstanceProof::prove_arbitrary_vec::<_, G, _, 5, 3>(
                &deg2_claim,
                0,
                &mut polys.try_into().unwrap(),
                scale(affine_twisted_edwards_add_l1),
                3,
                transcript,
            );
            rand = _rand;

            first_layer_proof = FirstLayerProof {
                deg8_proof,
                deg8_claim,
                deg4_proof,
                deg4_claim,
                deg2_proof,
                deg2_claim,
            };

            let layer_coef = <Transcript as ProofTranscript<G>>::challenge_scalar(transcript, b"challenge_layer_coef");

            final_claim = (0..2)
                .map(|i| evals[i] + layer_coef * (evals[i] - evals[2 + i]))
                .collect::<Vec<F>>().try_into().unwrap();
        }

        GrandAddArgument {
            first: first_layer_proof,
            inner: inner_layers_proofs,
            final_claim,
        }
  }

//   pub fn verify<G, T: ProofTranscript<G>>(
//     &self,
//     claims_prod_vec: &Vec<F>,
//     len: usize,
//     transcript: &mut T,
//   ) -> (Vec<F>, Vec<F>)
//   where
//     G: CurveGroup<ScalarField = F>,
//   {
//     let num_layers = len.log_2() as usize;
//     let mut rand: Vec<F> = Vec::new();
//     assert_eq!(self.proof.len(), num_layers);

//     let mut claims_to_verify = claims_prod_vec.to_owned();
//     for (num_rounds, i) in (0..num_layers).enumerate() {
//       // produce random coefficients, one for each instance
//       let coeff_vec =
//         transcript.challenge_vector(b"rand_coeffs_next_layer", claims_to_verify.len());

//       // produce a joint claim
//       let claim = (0..claims_to_verify.len())
//         .map(|i| claims_to_verify[i] * coeff_vec[i])
//         .sum();

//       let (claim_last, rand_prod) = self.proof[i].verify::<G, T>(claim, num_rounds, 3, transcript);

//       let claims_prod_left = &self.proof[i].claims_prod_left;
//       let claims_prod_right = &self.proof[i].claims_prod_right;
//       assert_eq!(claims_prod_left.len(), claims_prod_vec.len());
//       assert_eq!(claims_prod_right.len(), claims_prod_vec.len());

//       for i in 0..claims_prod_vec.len() {
//         transcript.append_scalar(b"claim_prod_left", &claims_prod_left[i]);
//         transcript.append_scalar(b"claim_prod_right", &claims_prod_right[i]);
//       }

//       assert_eq!(rand.len(), rand_prod.len());
//       let eq: F = (0..rand.len())
//         .map(|i| rand[i] * rand_prod[i] + (F::one() - rand[i]) * (F::one() - rand_prod[i]))
//         .product();
//       let claim_expected: F = (0..claims_prod_vec.len())
//         .map(|i| coeff_vec[i] * (claims_prod_left[i] * claims_prod_right[i] * eq))
//         .sum();

//       assert_eq!(claim_expected, claim_last);

//       // produce a random challenge
//       let r_layer = transcript.challenge_scalar(b"challenge_r_layer");

//       claims_to_verify = (0..claims_prod_left.len())
//         .map(|i| claims_prod_left[i] + r_layer * (claims_prod_right[i] - claims_prod_left[i]))
//         .collect::<Vec<F>>();

//       let mut ext = vec![r_layer];
//       ext.extend(rand_prod);
//       rand = ext;
//     }
//     (claims_to_verify, rand)
//   }
}





#[cfg(test)]
mod tests {
    use ark_ff::UniformRand;
    use std::{assert_eq, str::FromStr};
    use itertools::zip_eq;

    use super::*;

    #[test]
    fn check_that_constants_are_same_as_other_constants_that_we_can_not_access_due_to_version_conflicts() {
        assert_eq!(Fr::from_str("45022363124591815672509500913686876175488063829319466900776701791074614335719").unwrap(), Fr::COEFF_D);
        assert_eq!(8.log_2(), 3);
    }

    #[test]
    fn bandersnatch_addition() {
        use ark_ed_on_bls12_381_bandersnatch::{EdwardsProjective, EdwardsAffine};

        let mut rng = ark_std::test_rng();
        
        let pt1 = EdwardsProjective::rand(&mut rng);
        let pt2 = EdwardsProjective::rand(&mut rng);
        let bandersnatch_sum =  pt1 + pt2;
        let [x, y, z] = twisted_edwards_add(&[pt1.x, pt1.y, pt1.z, pt2.x, pt2.y, pt2.z]);
        assert_eq!(bandersnatch_sum, EdwardsAffine::new(x / z, y / z));
    }

    #[test]
    fn bandersnatch_affine_addition() {
        use ark_ed_on_bls12_381_bandersnatch::{EdwardsProjective, EdwardsAffine};

        let mut rng = ark_std::test_rng();
        
        let pt1 = EdwardsAffine::rand(&mut rng);
        let pt2 = EdwardsAffine::rand(&mut rng);
        let bandersnatch_sum =  pt1 + pt2;
        let [x, y, z] = affine_twisted_edwards_add(&[pt1.x, pt1.y, pt2.x, pt2.y]);
        assert_eq!(bandersnatch_sum, EdwardsAffine::new(x / z, y / z));
    }

    #[test]
    fn map_over_poly_check() {
        let ins = [
            DensePolynomial::new(vec![Fr::from(5)]),
            DensePolynomial::new(vec![Fr::from(3)]),
            DensePolynomial::new(vec![Fr::from(2)]),
            DensePolynomial::new(vec![Fr::from(4)]),
        ];
        let outs = map_over_poly(&ins, affine_twisted_edwards_add);
        let ans = affine_twisted_edwards_add(&[Fr::from(5), Fr::from(3), Fr::from(2), Fr::from(4)]).map(|x| DensePolynomial::new(vec![x]));
        zip_eq(outs.iter(), ans.iter()).enumerate().map(|(idx, (o, a))| assert_eq!(o.Z, a.Z, "Mismatch in position {:?}: {:?} != {:?}", idx, o, a)).count();
    }
}
