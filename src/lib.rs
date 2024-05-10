#![feature(generic_const_exprs)]

pub mod pullback;
pub mod msm_nonaffine;
pub mod gkr_msm_simple;

use ark_bls12_381::Fr;
use ark_ec::{bls12::Bls12, pairing::Pairing, CurveGroup};
use ark_ff::{BigInt, Field, PrimeField};
use ark_std::iterable::Iterable;
use itertools::Itertools;
use liblasso::{poly::{dense_mlpoly::DensePolynomial, eq_poly::EqPolynomial}, subprotocols::sumcheck::VecSumcheckInstanceProof, utils::{errors::ProofVerifyError, transcript::ProofTranscript}};
use merlin::Transcript;
use std::marker::PhantomData;
use liblasso::utils::math::Math;
use rayon::{current_num_threads, join, prelude::*, scope, spawn};

type C = <Bls12<ark_bls12_381::Config> as Pairing>::G1;


pub trait TwistedEdwardsConfig {

    const COEFF_D: Self;

    fn mul_by_a(&self) -> Self;

    fn mul_by_d(&self) -> Self;
}


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


pub fn affine_twisted_edwards_add_l1<F: Field + TwistedEdwardsConfig>(pts: &Vec<F>) -> Vec<F>  {
    assert_eq!(pts.len(), 4);
    let [x1, y1, x2, y2] = pts.as_slice().first_chunk().unwrap();
    vec![*x1 * y2, *x2 * y1, *y1 * y2 - (*x1 * x2).mul_by_a()]
}

pub fn affine_twisted_edwards_add_l2<F: Field + TwistedEdwardsConfig>(pts: &Vec<F>) -> Vec<F>  {
    assert_eq!(pts.len(), 3);
    let [x1y2, x2y1, y1y2_ax1x2] = pts.as_slice().first_chunk().unwrap();
    vec![(*x1y2 + x2y1), *y1y2_ax1x2, *x1y2 * x2y1]
}

pub fn affine_twisted_edwards_add_l3<F: Field + TwistedEdwardsConfig>(pts: &Vec<F>) -> Vec<F>  {
    assert_eq!(pts.len(), 3);
    let [X, Y, XY] = pts.as_slice().first_chunk().unwrap();
    let dXY = XY.mul_by_d();
    let Z2_dXY = F::one() - dXY;
    let Z2__dXY = F::one() + dXY;
    vec![Z2_dXY * X, Z2__dXY * Y, Z2_dXY * Z2__dXY]
}

pub fn affine_twisted_edwards_add<F: Field + TwistedEdwardsConfig>(pts: &Vec<F>) -> Vec<F> {
    assert_eq!(pts.len(), 4);
    affine_twisted_edwards_add_l3(&affine_twisted_edwards_add_l2(&affine_twisted_edwards_add_l1(pts)))
}


pub fn twisted_edwards_add_l1<F: Field + TwistedEdwardsConfig>(pts: &Vec<F>) -> Vec<F>  {
    assert_eq!(pts.len(), 6);
    let [x1, y1, z1, x2, y2, z2] = pts.as_slice().first_chunk().unwrap();
    vec![*x1 * y2, *x2 * y1, *y1 * y2 - (*x1 * x2).mul_by_a(), *z1 * z2]
}

pub fn twisted_edwards_add_l2<F: Field + TwistedEdwardsConfig>(pts: &Vec<F>) -> Vec<F>  {
    assert_eq!(pts.len(), 4);
    let [x1y2, x2y1, y1y2_ax1x2, z1z2] = pts.as_slice().first_chunk().unwrap();
    vec![(*x1y2 + x2y1) * z1z2, *y1y2_ax1x2 * z1z2, z1z2.square(), *x1y2 * x2y1]
}

pub fn twisted_edwards_add_l3<F: Field + TwistedEdwardsConfig>(pts: &Vec<F>) -> Vec<F>  {
    assert_eq!(pts.len(), 4);
    let [X, Y, Z2, XY] = pts.as_slice().first_chunk().unwrap();
    let dXY = XY.mul_by_d();
    let Z2_dXY = *Z2 - dXY;
    let Z2__dXY = *Z2 + dXY;
    vec![Z2_dXY * X, Z2__dXY * Y, Z2_dXY * Z2__dXY]
}

pub fn twisted_edwards_add<F: Field + TwistedEdwardsConfig>(pts: &Vec<F>) -> Vec<F> {
    twisted_edwards_add_l3(&twisted_edwards_add_l2(&twisted_edwards_add_l1(pts)))
}


pub fn scale<F: Field + TwistedEdwardsConfig, T: Fn (&Vec<F>) -> Vec<F>>(f: T) -> impl Fn (&Vec<F>) -> Vec<F> {
    move |data: &Vec<F>| -> Vec<F> {
        let (pts, factor) = data.split_at(data.len() - 1);
        f(&pts.to_vec()).iter().map(|p| *p * factor[0]).collect()
    }
}

// GKR

struct FirstLayer<F: Field + TwistedEdwardsConfig> {
    pub deg2: Vec<DensePolynomial<F>>,  // len = 3
    pub deg4: Vec<DensePolynomial<F>>,  // len = 3
    pub deg8: Vec<DensePolynomial<F>>,  // len = 3
}

struct InnerLayer<F: Field + TwistedEdwardsConfig> {
    pub deg2: Vec<DensePolynomial<F>>,  // len = 4
    pub deg4: Vec<DensePolynomial<F>>,  // len = 4
    pub deg8: Vec<DensePolynomial<F>>,  // len = 3
}

struct GrandAddCircuit<F: Field + TwistedEdwardsConfig> {
    pub input: Vec<DensePolynomial<F>>,  // len = 2
    pub first: FirstLayer<F>,
    pub inner: Vec<InnerLayer<F>>,
}

pub fn fold_with_coef<F: Field>(evals: &Vec<F>, layer_coef: F) -> Vec<F> {
    assert_eq!(evals.len() % 2, 0);
    (0..(evals.len() / 2))
        .map(|i| evals[i] + layer_coef * (evals[i] - evals[2 + i]))
        .collect()
}

pub fn split_vecs<F: PrimeField>(ins: &Vec<DensePolynomial<F>>) -> Vec<DensePolynomial<F>> {
    let mut res = Vec::<DensePolynomial::<F>>::with_capacity(ins.len() * 2);
    for _i in 0..(ins.len() * 2) {
        res.push(DensePolynomial::new(vec![F::zero()]))
    }

    ins.iter().enumerate().map(|(idx, poly)| (res[idx], res[ins.len() + idx]) = poly.split(poly.len() / 2)).count();
    res.try_into().unwrap()
}

pub fn map_over_poly<F: PrimeField>(
    ins: &Vec<DensePolynomial<F>>,
    f: impl Fn(&Vec<F>) -> Vec<F> + Send + Sync + Clone
) -> Vec<DensePolynomial<F>> {
    let applications: Vec<Vec<F>> = (0..ins[0].len()).into_par_iter()
        .map(|idx| {
            f(&ins.iter().map(|p| p[idx]).collect_vec())
        }).collect();
    
    (0..applications.first().unwrap().len()).into_iter()
        .map(|idx| {
            DensePolynomial::new(applications.iter().map(|v| v[idx]).collect())
    }).collect::<Vec<DensePolynomial::<F>>>().try_into().unwrap()
}



impl<F: PrimeField + TwistedEdwardsConfig> GrandAddCircuit<F> {
    pub fn new(x: &DensePolynomial<F>, y: &DensePolynomial<F>, num_layers: usize) -> Self {
        assert_eq!(x.len(), y.len());
        assert!(num_layers <= x.num_vars);

        let input = vec![x.clone(), y.clone()];
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

    fn num_layers(&self) -> usize {
         self.inner.len() + 1
    }
}

struct FirstLayerProof<F: PrimeField + TwistedEdwardsConfig> {
    deg8_proof: VecSumcheckInstanceProof<F>,
    deg4_proof: VecSumcheckInstanceProof<F>,
    deg2_proof: VecSumcheckInstanceProof<F>,
}

struct InnerLayerProof<F: PrimeField + TwistedEdwardsConfig> {
    deg8_proof: VecSumcheckInstanceProof<F>,
    deg4_proof: VecSumcheckInstanceProof<F>,
    deg2_proof: VecSumcheckInstanceProof<F>,
}

struct GrandAddArgument<F: PrimeField + TwistedEdwardsConfig> {
    input_log_size: usize,
    final_claim: Vec<F>, // len = 2
    first: FirstLayerProof<F>,
    inner: Vec<InnerLayerProof<F>>,
}
 
impl<F: PrimeField + TwistedEdwardsConfig> GrandAddArgument<F> {
    pub fn prove<G, T>(
        grand_add_circuit: &mut GrandAddCircuit<F>,
        _rand: &Vec<F>,
        transcript: &mut T,
    ) -> Self
    where
        T: ProofTranscript<G>,
        G: CurveGroup<ScalarField = F>,
    {
        let mut rand = _rand.clone(); 
        let GrandAddCircuit{input, first, inner} = grand_add_circuit;
        let FirstLayer{deg2: first_deg2, deg4: first_deg4, deg8: first_deg8} = first;
        let first_layer_proof: FirstLayerProof<F>;
        let mut inner_layers_proofs: Vec<InnerLayerProof<F>> = Vec::new();
        let final_claim;
        let num_inner_layers = inner.len();
        let input_log_size = input[0].num_vars;
        let output_log_size = input_log_size - num_inner_layers - 1;

        let mut deg8_claim = if num_inner_layers > 0{
            inner.last().unwrap().deg8.iter().map(|p| p.evaluate(&rand)).collect()
        } else {
            first_deg8.iter().map(|p| p.evaluate(&rand)).collect()
        };

        for inner_layer_id in (0..num_inner_layers).rev() {
            let (deg8_proof, _rand) = VecSumcheckInstanceProof::prove::<_, G, _>(
                &deg8_claim,
                input_log_size - inner_layer_id - 2,
                &mut inner[inner_layer_id].deg4.to_vec(),
                &mut vec![DensePolynomial::new(EqPolynomial::<F>::new(rand.clone()).evals())],
                scale(twisted_edwards_add_l3),
                3,
                transcript,
            );
            rand = _rand;

            let mut deg4_claim = deg8_proof.inner_proof.final_evals.clone();
            deg4_claim.pop();

            let (deg4_proof, _rand) = VecSumcheckInstanceProof::prove::<_, G, _>(
                &deg4_claim,
                input_log_size - inner_layer_id - 2,
                &mut inner[inner_layer_id].deg2.to_vec(),
                &mut vec![DensePolynomial::new(EqPolynomial::<F>::new(rand.clone()).evals())],
                scale(twisted_edwards_add_l2),
                3,
                transcript,
            );
            rand = _rand;

            let mut deg2_claim = deg4_proof.inner_proof.final_evals.clone();
            deg2_claim.pop();

            let mut polys = if inner_layer_id == 0 {
                split_vecs(&first_deg8).to_vec()
            } else {
                split_vecs(&inner[inner_layer_id - 1].deg8).to_vec()
            };

            let (deg2_proof, _rand) = VecSumcheckInstanceProof::prove::<_, G, _>(
                &deg2_claim,
                input_log_size - inner_layer_id - 2,
                &mut polys,
                &mut vec![DensePolynomial::new(EqPolynomial::<F>::new(rand.clone()).evals())],
                scale(twisted_edwards_add_l1),
                3,
                transcript,
            );
            rand = _rand; 
            
            let layer_coef = transcript.challenge_scalar(b"challenge_layer_coef");
    
            deg8_claim = deg2_proof.inner_proof.final_evals.clone();
            deg8_claim.pop();

            deg8_claim = fold_with_coef(&deg8_claim, layer_coef);

            let mut ext = vec![layer_coef];
            ext.extend(rand);
            rand = ext;

            inner_layers_proofs.push(InnerLayerProof {
                deg8_proof,
                deg4_proof,
                deg2_proof,
            });
        }

        { // First layer
            let (deg8_proof, _rand) = VecSumcheckInstanceProof::prove::<_, G, _>(
                &deg8_claim,
                input_log_size - 1,
                &mut vec![DensePolynomial::new(EqPolynomial::<F>::new(rand.clone()).evals())],
                &mut first_deg4.to_vec(),
                scale(affine_twisted_edwards_add_l3),
                3,
                transcript,
            );
            rand = _rand;

            let mut deg4_claim = deg8_proof.inner_proof.final_evals.clone();
            deg4_claim.pop();

            let (deg4_proof, _rand) = VecSumcheckInstanceProof::prove::<_, G, _>(
                &deg4_claim,
                input_log_size - 1,
                &mut first_deg2.to_vec(),
                &mut vec![DensePolynomial::new(EqPolynomial::<F>::new(rand.clone()).evals())],
                scale(affine_twisted_edwards_add_l2),
                3,
                transcript,
            );
            rand = _rand;

            let mut deg2_claim = deg4_proof.inner_proof.final_evals.clone();
            deg2_claim.pop();

            let (deg2_proof, _rand) = VecSumcheckInstanceProof::prove::<_, G, _>(
                &deg2_claim,
                input_log_size - 1,
                &mut split_vecs(&input).to_vec().try_into().unwrap(),
                &mut vec![DensePolynomial::new(EqPolynomial::<F>::new(rand.clone()).evals())],
                scale(affine_twisted_edwards_add_l1),
                3,
                transcript,
            );
            rand = _rand;


            let layer_coef = transcript.challenge_scalar(b"challenge_layer_coef");

            let mut full_final_claim = deg2_proof.inner_proof.final_evals.clone();
            full_final_claim.pop();
            final_claim = fold_with_coef(&full_final_claim, layer_coef);

            first_layer_proof = FirstLayerProof {
                deg8_proof, 
                deg4_proof,
                deg2_proof,
            };
        }

        GrandAddArgument {
            input_log_size,
            first: first_layer_proof,
            inner: inner_layers_proofs,
            final_claim,
        }
  }

  pub fn verify<G, T: ProofTranscript<G>>(
    &self,
    claim: &Vec<F>,
    _rand: &Vec<F>,
    transcript: &mut T,
  ) -> Result<Vec<F>, ProofVerifyError>
  where
    G: CurveGroup<ScalarField = F>,
  {
    let mut rand = _rand.clone();
    let mut running_claim = claim.clone();
    let input_log_size = self.input_log_size;
    let output_log_size = input_log_size - self.inner.len() - 1;

    for layer_idx in 0..self.inner.len() {
        rand = self.inner[layer_idx].deg8_proof.verify(&running_claim, output_log_size + layer_idx, 3, &[&|r| EqPolynomial::new(rand.clone()).evaluate(r)], scale(twisted_edwards_add_l3), transcript)?;
        println!("{} 8", layer_idx);
        
        let mut deg4_claim = self.inner[layer_idx].deg8_proof.inner_proof.final_evals.clone();
        deg4_claim.pop();
        rand = self.inner[layer_idx].deg4_proof.verify(&deg4_claim, output_log_size + layer_idx, 3, &[&|r| EqPolynomial::new(rand.clone()).evaluate(r)], scale(twisted_edwards_add_l2), transcript)?;
        println!("{} 4", layer_idx);

        let mut deg2_claim = self.inner[layer_idx].deg4_proof.inner_proof.final_evals.clone();
        deg2_claim.pop();
        rand = self.inner[layer_idx].deg2_proof.verify(&deg2_claim, output_log_size + layer_idx, 3, &[&|r| EqPolynomial::new(rand.clone()).evaluate(r)], scale(twisted_edwards_add_l1), transcript)?;
        println!("{} 2", layer_idx);

        let layer_coef = transcript.challenge_scalar(b"challenge_layer_coef");

        running_claim = self.inner[layer_idx].deg2_proof.inner_proof.final_evals.clone();
        running_claim.pop();
        running_claim = fold_with_coef(&running_claim, layer_coef);

        let mut ext = vec![layer_coef];
        ext.extend(rand);
        rand = ext;
    }

    {  // First layer
        rand = self.first.deg2_proof.verify(&running_claim, input_log_size - 1, 3, &[&|r| EqPolynomial::new(rand.clone()).evaluate(r)], scale(affine_twisted_edwards_add_l1), transcript)?;
        
        let mut deg4_claim = self.first.deg8_proof.inner_proof.final_evals.clone();
        deg4_claim.pop();
        rand = self.first.deg4_proof.verify(&deg4_claim, input_log_size - 1, 3, &[&|r| EqPolynomial::new(rand.clone()).evaluate(r)], scale(affine_twisted_edwards_add_l2), transcript)?;
        
        let mut deg2_claim = self.first.deg4_proof.inner_proof.final_evals.clone();
        deg2_claim.pop();
        rand = self.first.deg8_proof.verify(&deg2_claim, input_log_size - 1, 3, &[&|r| EqPolynomial::new(rand.clone()).evaluate(r)], scale(affine_twisted_edwards_add_l3), transcript)?;
        
        let layer_coef = transcript.challenge_scalar(b"challenge_layer_coef");  

        running_claim = self.first.deg2_proof.inner_proof.final_evals.clone();
        running_claim.pop();

        running_claim = fold_with_coef(&running_claim, layer_coef);
        assert_eq!(&self.final_claim, &running_claim);
    }

    Ok(rand)
  }
}





#[cfg(test)]
mod tests {
    use ark_bls12_381::G1Projective;
    use ark_ff::UniformRand;
    use std::{assert_eq, str::FromStr};
    use itertools::zip_eq;
    use ark_ed_on_bls12_381_bandersnatch::{EdwardsAffine, EdwardsProjective, BandersnatchConfig};
    use liblasso::utils::test_lib::TestTranscript;
    use ark_ec::twisted_edwards::Projective;

    use super::*;

    #[test]
    fn check_that_constants_are_same_as_other_constants_that_we_can_not_access_due_to_version_conflicts() {
        assert_eq!(Fr::from_str("45022363124591815672509500913686876175488063829319466900776701791074614335719").unwrap(), Fr::COEFF_D);
        assert_eq!(8.log_2(), 3);
    }

    #[test]
    fn bandersnatch_addition() {
        let mut rng = ark_std::test_rng();
        
        let pt1 = EdwardsProjective::rand(&mut rng);
        let pt2 = EdwardsProjective::rand(&mut rng);
        let bandersnatch_sum =  pt1 + pt2;
        let a = twisted_edwards_add(&vec![pt1.x, pt1.y, pt1.z, pt2.x, pt2.y, pt2.z]);
        assert_eq!(a.len(), 3);
        let [x, y, z] = a.as_slice().first_chunk().unwrap();
        assert_eq!(bandersnatch_sum, EdwardsAffine::new(x / z, y / z));
    }

    #[test]
    fn bandersnatch_affine_addition() {

        let mut rng = ark_std::test_rng();
        
        let pt1 = EdwardsAffine::rand(&mut rng);
        let pt2 = EdwardsAffine::rand(&mut rng);
        let bandersnatch_sum =  pt1 + pt2;
        let a = affine_twisted_edwards_add(&vec![pt1.x, pt1.y, pt2.x, pt2.y]);  
        assert_eq!(a.len(), 3);
        let [x, y, z] = a.as_slice().first_chunk().unwrap();
        assert_eq!(bandersnatch_sum, EdwardsAffine::new(x / z, y / z));
    }

    #[test]
    fn map_over_poly_check() {
        let ins = vec![
            DensePolynomial::new(vec![Fr::from(5)]),
            DensePolynomial::new(vec![Fr::from(3)]),
            DensePolynomial::new(vec![Fr::from(2)]),
            DensePolynomial::new(vec![Fr::from(4)]),
        ];
        let outs = map_over_poly(&ins, affine_twisted_edwards_add);
        let ans: Vec<DensePolynomial<Fr>> = affine_twisted_edwards_add(&vec![Fr::from(5), Fr::from(3), Fr::from(2), Fr::from(4)]).iter().map(|&x| DensePolynomial::new(vec![x])).collect();
        zip_eq(outs.iter(), ans.iter()).enumerate().map(|(idx, (o, a))| assert_eq!(o.Z, a.Z, "Mismatch in position {:?}: {:?} != {:?}", idx, o, a)).count();
    }

    #[test]
    fn grand_addition() {
        let mut rng = ark_std::test_rng();
        let coords: Vec<(Fr, Fr)> = (0..16).map(|i| EdwardsAffine::rand(&mut rng)).map(|p| (p.x, p.y)).collect();
        let (mut xs, mut ys) = (Vec::with_capacity(coords.len()), Vec::with_capacity(coords.len()));
        for i in 0..coords.len() {
            xs.push(coords[i].0);
            ys.push(coords[i].1);
        }

        let r: Vec<Fr> = (0..100).map(|i| Fr::from(i)).collect();
        let mut transcript: TestTranscript<Fr> = TestTranscript::new(r.clone(), vec![]);

        let mut grand_add_circuit = GrandAddCircuit::new(&DensePolynomial::new(xs), &DensePolynomial::new(ys), 3);

        let mut point = vec![Fr::from(228)];

        let output_claim = if grand_add_circuit.inner.len() > 0{
            grand_add_circuit.inner.last().unwrap().deg8.iter().map(|p| p.evaluate(&point)).collect()
        } else {
            grand_add_circuit.first.deg8.iter().map(|p| p.evaluate(&point)).collect()
        };
        
        let argument = GrandAddArgument::prove::<G1Projective, _>(&mut grand_add_circuit, &mut point, &mut transcript);
        
        let mut transcript: TestTranscript<Fr> = TestTranscript::as_this(&transcript);
        let _ = argument.verify::<G1Projective, _>(&output_claim, &point, &mut transcript);
        transcript.assert_end()
    }
}
