use crate::poly;
use crate::protocol::protocol::MultiEvalClaim;

use super::*;
use super::bit_utils::*;
use ark_ff::PrimeField;
use itertools::Itertools;
use crate::transcript::{TranscriptReceiver, TranscriptSender, Challenge,};


pub const MY_FAVORITE_LIMB_SIZE: usize = 64;

pub struct MSMProof<G: CurveGroup> {
    bit_columns: Vec<G>,
    point_column: G,
    gkr_proof: BintreeProof<G::ScalarField>,
    output: Vec<G::ScalarField>,
}


fn powers_of_t<F: PrimeField>(
    t: F, 
    log_len: usize
) -> Vec<F> {
    let mut ans = vec![F::one()];
    let mut curr_pow = t;
    for _ in 0..log_len{
        let clone_ans = ans.clone();
        let mut clone_ans: Vec<_> = clone_ans.iter()
                                    .map(|&x| x*curr_pow)
                                    .collect();
        ans.append(&mut clone_ans);
        curr_pow = curr_pow * curr_pow;
    }
    ans
}

// in: [a, b, c, d], [x, y]
// out [ax, bx, cx, dx, ay, by, cy, dy]
pub fn tensor_product_of_vecs<F: PrimeField>(
    vec1: Vec<F>,
    vec2: Vec<F>,
) -> Vec<F> {
    let car_product: Vec<_> = vec2.iter()
                        .cartesian_product(vec1)
                        .collect();
    let ans = car_product.iter()
                        .map(|(&x, y)| x*y)
                        .collect();
    ans
}


pub fn tensor_product<F: PrimeField>(
    poly1: DensePolynomial<F>,
    poly2: DensePolynomial<F>,
) -> DensePolynomial<F> {
    let (num_vars1, len1, Z1) = (poly1.num_vars, poly1.len, poly1.Z);
    let (num_vars2, len2, Z2) = (poly2.num_vars, poly2.len, poly2.Z);

    let num_vars = num_vars1*num_vars2;
    let len = len1*len2;

    assert!(len.is_power_of_two());

    let Z = tensor_product_of_vecs(Z1, Z2);

    DensePolynomial{
        num_vars,
        len,
        Z
    }
}


//computes the factor in the equalizer polynomial (x_position * value) + (1 - x_position)(1 - value)
// only returns evals, not the polynoial
pub fn elemenary_equalizer_poly<F: PrimeField>(
    value: F,
    position: usize,
    num_vars: usize
) -> Vec<F> {
    let len = 1 << num_vars;
    let Z: Vec<_> = (0..len)
                                .map(|i| 
                                    {
                                        let x_position = (i / (1 << position) ) % 2;
                                        let x_position = F::from(x_position as u64);
                                        (x_position * value) + (F::one() - x_position)*(F::one() - value)
                                    })
                                .collect();
    
    Z
}


//computes the equalizer sum_{position} (x_position * value) + (1 - x_position)(1 - value)
// only returns evals, not the polynoial
pub fn equalizer_poly<F: PrimeField>(
    point: Vec<F>,
    num_vars: usize
) -> Vec<F> {
    assert_eq!(point.len(), num_vars);
    let len = 1 << num_vars;

    let mut Z = vec![F::one(); len];

    for i in 0..num_vars{
        let other_Z = elemenary_equalizer_poly(point[i], i, num_vars);
        Z = Z.iter()
            .zip(other_Z)
            .map(|(&x, y)| x*y)
            .collect();
    }
    Z
    
}


// This function takes a bit and a point, parsed as b, p.x, p.y, and returns b ? p : zero_point

fn pt_bit_choice<F: PrimeField>(args: &[F]) -> Vec<F> {
    vec![args[0] * args[1], args[0] * (args[2] - F::one()) + F::one()]
}


pub fn layer_op <F: PrimeField>(arr: &[F]) -> Vec<F>  {
    assert_eq!(arr.len(), 4);
    let [x1, y1, x2, y2] = arr.first_chunk().unwrap();
    vec![*x1 * y2, *x2 * y1, *y1 * y2 - (*x1 * x2), F::one()]
}


pub fn mini_msm<
    F: PrimeField,
    T: TranscriptReceiver::<F> + TranscriptSender::<F>,
>(
    scalars: Vec<Vec<bool>>,
    //points: Vec<(F, F)>,
    transcript: &mut T,
){
    let num_vars = 10;


    let bits_flatten: Vec<_> = scalars.iter().flatten().collect();

    let bits_poly = NestedPolynomial::from_values(
        bits_flatten
            .par_iter()
            .map(|x| F::from(**x as u64))
            .collect(),
        bits_flatten.len().log_2(),
        F::zero(),
    );


    let base_layer = vec![bits_poly.clone(), bits_poly.clone(), bits_poly.clone()];//, points_table_poly.0, points_table_poly.1];

    let f_base = PolynomialMapping {
        exec: Arc::new(pt_bit_choice),
        degree: 2,
        num_i: 3,
        num_o: 2,
    };


    let f_deg2 = PolynomialMapping {
        exec: Arc::new(layer_op::<F>),
        degree: 2,
        num_i: 4,
        num_o: 4,
    };

    let layers = vec![
        Layer::Mapping(f_base),
        // Layer::new_split(2),
        // Layer::Mapping(f_deg2.clone()),
        // Layer::Mapping(f_deg2.clone()),];
    ];

    let params = BintreeParams::new(layers, num_vars);

    let (trace, output) = Bintree::witness(base_layer, &params);


    let claim_point = (0..num_vars - 1)
        .map(|_| F::one())
        .collect_vec();

    let claim_evals = output
        .iter()
        .map(|p| p.evaluate(&claim_point))
        .collect_vec();

    let claim = to_multieval(EvalClaim {
        point: claim_point,
        evs: claim_evals,
    });


    let mut prover = BintreeProver::start(claim, trace, &params);

    let mut res = None;
    while res.is_none() {
        //let challenge = transcript.challenge_scalar(b"challenge_nextround");
        let challenge = Challenge{value:  F::one()};
        res = prover.round(challenge, transcript);
    }

    let (gkr_evals, _) = res.unwrap();

    println!("{:?}", gkr_evals);
}



// given a table of bits T[i, j] of evaluations of the polynomial P,
// and a claim of evaluation of P at a point r
// produces an opening proof and a bunch more claims
pub fn opening<
    F: PrimeField, // + TwistedEdwardsConfig,
    //T: TranscriptReceiver<F> + TranscriptSender<F>,
    //G: CurveGroup<ScalarField = F>,
>(
    eval_bits: Vec<Vec<bool>>,
    point: Vec<Vec<bool>>,
    eval_claim: MultiEvalClaim<F>,
    log_len: usize,
    
    limb_size: usize, // just put 64

    challenge_t: F,
    //log_num_scalar_bits: usize,
    //log_num_bit_columns: usize, // Logamount of columns that host the bitvector. Normally ~5-6 should be reasonable.
    //transcript: &mut T,
) //-> (EvalClaim<F>, MSMProof<G>)
{
    
    let Z_len = 1 << limb_size; 
    assert_eq!(eval_bits.len(), Z_len);
    
    let size_of_fe = (F::MODULUS_BIT_SIZE as usize).max(eval_bits[0].len());
    //println!("{}, {}, {}", eval_bits.len(), eval_bits[0].len(), size_of_fe);

    let powers_of_two = powers_of_t(F::from(2u64), limb_size);
    //let powers_of_two = powers_of_t(F::from(2), limb_size);
    let l_two = DensePolynomial{
        num_vars: limb_size,
        len : Z_len,
        Z: powers_of_two
    };

    todo!();
    
}

