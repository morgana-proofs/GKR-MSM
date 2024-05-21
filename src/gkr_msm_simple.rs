use ark_ec::{CurveGroup, ScalarMul};
use ark_ff::PrimeField;
use liblasso::poly::dense_mlpoly::DensePolynomial;
use rayon::iter::{repeatn, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};
use std::{fs::File, sync::Arc};
use ark_serialize::*;

use crate::{
    binary_msm::{binary_msm, prepare_coefs},
    grand_add::{
        affine_twisted_edwards_add_l1,
        affine_twisted_edwards_add_l2,
        affine_twisted_edwards_add_l3,
        twisted_edwards_add_l1,
        twisted_edwards_add_l2,
        twisted_edwards_add_l3
    }, protocol::{PolynomialMapping, Protocol, TranscriptReceiver, TranscriptSender}, sumcheck_trait::{Split, SumcheckPolyMap, SumcheckPolyMapParams}, utils::TwistedEdwardsConfig};

pub trait MSMCircuitConfig {
    type F : PrimeField;
    type Comm : CurveGroup<ScalarField = Self::F>;
    type G : CurveGroup<Config : TwistedEdwardsConfig>;
}

pub struct ExtendedBases<G: CurveGroup>{
    packing_factor: usize,
    values: Vec<Vec<G::Affine>>,
}

pub struct CommitmentKey<G: CurveGroup> {
    bases: Option<Vec<G::Affine>>,
    binary_extended_bases: Option<Vec<Vec<G::Affine>>>,
}

impl<G: CurveGroup> CommitmentKey<G> {
    pub fn new() -> Self {
        Self {bases: None, binary_extended_bases: None}
    }
    
    pub fn load(&mut self, file: &mut File) {
        todo!()
    }

    pub fn commit_vec(&self, v: &[G::ScalarField]) -> G {
        G::msm(self.bases.as_ref().unwrap(), v).unwrap()
    }

    pub fn commit_bitvec(&self, v: impl Iterator<Item = bool>) -> G {
        binary_msm(& prepare_coefs(v), self.binary_extended_bases.as_ref().unwrap())
    }

}

pub struct MSMCircuit {}



// This function takes a bit and a point, parsed as b, p.x, p.y, and returns b ? p : zero_point

fn pt_bit_choice<F: PrimeField>(args: &[F]) -> Vec<F> {
    vec![args[0]*args[1],  args[0]*(args[2] - F::one()) + F::one()]
}

fn param_from_f<F: PrimeField>(f: PolynomialMapping<F>, num_vars: usize) -> SumcheckPolyMapParams<F> {
    SumcheckPolyMapParams{f, num_vars}
}

pub fn gkr_msm_prove<
    F: PrimeField + TwistedEdwardsConfig,
    T: TranscriptReceiver<F> + TranscriptSender<F>,
    G: CurveGroup<ScalarField = F>,
> (    
    scalars: Vec<Vec<bool>>,
    points: Vec<(F, F)>,
    log_num_points: usize,
    log_num_scalar_bits: usize,
    log_num_bit_columns: usize, // Logamount of columns that host the bitvector. Normally ~5-6 should be reasonable.
    ck: &CommitmentKey<G>,
    transcript: &mut T,
) -> () {

    let num_points = 1 << log_num_points;
    let num_scalar_bits = 1 << log_num_scalar_bits;
    let num_vars = log_num_points + log_num_scalar_bits;
    let size = 1 << num_vars;
    let num_bit_columns = 1 << log_num_bit_columns;

    assert!(points.len() == num_points);
    assert!(scalars.len() == num_points); 

    scalars.iter().map(|s| assert!(s.len() == num_scalar_bits)).count();

    // COMMIT TO OUR STUFF AND ADD IT TO TRANSCRIPT
    let bits_flatten : Vec<_> = scalars.into_par_iter().flatten().collect();

    let col_size = size >> log_num_bit_columns;
    
    let bit_comms : Vec<G> = (0..num_bit_columns).map(|i| {
        let point = ck.commit_bitvec(bits_flatten[col_size * i .. col_size * (i + 1)].iter().map(|x|*x));
        transcript.append_point(b"bit column", point);
        point
    }).collect();

    assert!(
        col_size >= 2*points.len(),
        "Points should fit in a single column. Please reduce the amount of columns."
    );

    let (mut pts_prep, tmp) : (Vec<_>, Vec<_>) = points.iter().map(|x|*x).unzip();
    pts_prep.extend(tmp.into_iter().chain(std::iter::repeat(F::zero())).take(col_size - points.len()*2));

    let pts_comm : G = ck.commit_vec(&pts_prep);
    transcript.append_point(b"point column", pts_comm);


    let bits_poly = DensePolynomial::new(
        bits_flatten
        .par_iter()
        .map(|x| F::from(*x as u64))
        .collect());

    let _points_table_poly : (Vec<_>, Vec<_>) = 
        points
            .par_iter()
            .map(|p| repeatn(*p, num_scalar_bits))
            .flatten()
            .unzip();

    let points_table_poly = (DensePolynomial::new(_points_table_poly.0), DensePolynomial::new(_points_table_poly.1));

    // layer0
    // bits_poly
    // points_table_poly
    
    let base_layer = vec![bits_poly, points_table_poly.0, points_table_poly.1];

    // layer1
    // filtered pts

    let f_base = PolynomialMapping{
        exec: Arc::new(pt_bit_choice),
        degree: 2,
        num_i: 3,
        num_o: 2
    };

    let (base_layer, gkr_input_layer) = SumcheckPolyMap::witness(base_layer, &param_from_f(f_base, num_vars));


    // Now, we will compute GKR witness.

    let f_deg2 = PolynomialMapping{
        exec: Arc::new(twisted_edwards_add_l1::<F>),
        degree: 2, num_i: 6, num_o: 4,
    };
    let f_deg4 = PolynomialMapping{
        exec: Arc::new(twisted_edwards_add_l2::<F>),
        degree: 2, num_i: 4, num_o: 4,
    };
    let f_deg8 = PolynomialMapping{
        exec: Arc::new(twisted_edwards_add_l3::<F>),
        degree: 2, num_i: 4, num_o: 3,
    };
    let f_deg2_init = PolynomialMapping{
        exec: Arc::new(affine_twisted_edwards_add_l1::<F>),
        degree: 2, num_i: 4, num_o: 3,
    };
    let f_deg4_init = PolynomialMapping{
        exec: Arc::new(affine_twisted_edwards_add_l2::<F>),
        degree: 2, num_i: 3, num_o: 3,
    };
    let f_deg8_init = PolynomialMapping{
        exec: Arc::new(affine_twisted_edwards_add_l3::<F>),
        degree: 2, num_i: 3, num_o: 3,
    };

    assert!(num_points > 1);
    let num_inner_layers = log_num_points - 1;

    let mut gkr_trace = vec![];
    let (gkr_input_layer, l2) = SumcheckPolyMap::witness(
        gkr_input_layer,
        &param_from_f(f_deg2_init, num_vars));    
    gkr_trace.push(gkr_input_layer);

    let (l2, l4) = SumcheckPolyMap::witness(
        l2,
        &param_from_f(f_deg4_init, num_vars));    
    gkr_trace.push(l2);

    let (l4, l8) = SumcheckPolyMap::witness(
        l4,
        &param_from_f(f_deg8_init, num_vars));    
    gkr_trace.push(l4);

    let mut last_l8 = l8;

    for i in 0..num_inner_layers {
        let curr_num_vars = num_vars >> (i+1);
        let l8 = last_l8;
        let (l8, _l1) = Split::witness(l8, &());
        gkr_trace.push(l8);
        let (mut l1, tmp) : (Vec<_>, Vec<_>) = _l1.into_iter().unzip();
        l1.extend(tmp);

        let par2 = param_from_f(f_deg2.clone(), curr_num_vars);
        let (_, l2) = SumcheckPolyMap::witness(l1, &par2);
        // gkr_trace.push(_); - maybe we don't need to keep it.
        let par4 = param_from_f(f_deg4.clone(), curr_num_vars);
        let (l2, l4) = SumcheckPolyMap::witness(l2, &par4);
        gkr_trace.push(l2);
        
        let par8 = param_from_f(f_deg8.clone(), curr_num_vars);
        let (l4, l8) = SumcheckPolyMap::witness(l4, &par8);
        gkr_trace.push(l4);

        last_l8 = l8;
    }

 
}