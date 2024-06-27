// Commit
// 1. Prepare multilinear polynomial $P\in\mathbb{F}_p[\mathbf{x}]$ of $n$ variables. Denote $P(\mathbf{x}) = \sum_{a\in\mathbb{B}^n}c_a[\mathbf{x}==a]$
// 2. Represent $c_a = c_{a,>}2^{128}+c_{a,<}$ for each $a$.
// 3. Commit to two multilinear polynomials over $\mathbb{F}_q$, defined as  $P_<(\mathbf{x}) = \sum_{a\in\mathbb{B}^n}c_{a,<}[\mathbf{x}==a]$ and $P_>(\mathbf{x}) = \sum_{a\in\mathbb{B}^n}c_{a,>}[\mathbf{x}==a]$.
// 4. Prepare a proof $\mathcal{R}$ that the coefficients of $P_<,P_>$ are range-checked.

use super::*;
use super::bit_utils::*;

// pub struct NonNativeCommitProof<G: CurveGroup> {
//     bit_columns: Vec<G>,
//     point_column: G,
//     gkr_proof: BintreeProof<G::ScalarField>,
//     output: Vec<G::ScalarField>,
// }

pub fn commit_bits<
    F: PrimeField + TwistedEdwardsConfig,
    B: BigInteger,
    T: TranscriptReceiver<F> + TranscriptSender<F>,
    G: CurveGroup<ScalarField = F>,
>(
    evals: Vec<B>,
    log_len: usize,
    log_num_bit_columns: usize, // Logamount of columns that host the bitvector. Normally ~5-6 should be reasonable.
    ck: &CommitmentKey<G>,
    transcript: &mut T,
) //-> (EvalClaim<F>, NonNativeCommitProof<G>)    
{   
    let Z_len = 1 << log_len; 
    assert_eq!(evals.len(), Z_len);
                            
    let num_bit_columns = 1 << log_num_bit_columns;
    let size_of_fe = F::MODULUS_BIT_SIZE as usize;
    let col_size = size_of_fe >> log_num_bit_columns;

    let bit_vec = evals_to_long_bit_vec_sorted_by_bits_be(evals);

    let bit_comms: Vec<G> = (0..num_bit_columns)
        .map(|i| {
            let point = ck.commit_bitvec(
                bit_vec[col_size * i..col_size * (i + 1)]
                    .iter()
                    .map(|x| *x),
            );
            transcript.append_point::<G>(b"bit column", point);
            point
        })
        .collect();
    
    todo!();
    
    
    // TODO: 
    // 



    // let num_points = 1 << log_num_points;
    // let num_scalar_bits = 1 << log_num_scalar_bits;
    // let num_vars = log_num_points + log_num_scalar_bits;
    // let size = 1 << num_vars;
    // let num_bit_columns = 1 << log_num_bit_columns;

    // assert_eq!(scalars.len(), num_points);

    // // COMMIT TO OUR STUFF AND ADD IT TO TRANSCRIPT
    // let bits_flatten: Vec<_> = scalars.into_par_iter().flatten().collect();

    // let col_size = size >> log_num_bit_columns;

    // let bit_comms: Vec<G> = (0..num_bit_columns)
    //     .map(|i| {
    //         let point = ck.commit_bitvec(
    //             bits_flatten[col_size * i..col_size * (i + 1)]
    //                 .iter()
    //                 .map(|x| *x),
    //         );
    //         transcript.append_point::<G>(b"bit column", point);
    //         point
    //     })
    //     .collect();

    // assert!(
    //     col_size >= 2 * points.len(),
    //     "Points should fit in a single column. Please reduce the amount of columns."
    // );

    // let (mut pts_prep, tmp): (Vec<_>, Vec<_>) = points.iter().map(|x| *x).unzip();
    // pts_prep.extend(
    //     tmp.into_iter()
    //         .chain(repeat(F::zero()).take(col_size - num_points * 2)),
    // );

    // let pts_comm: G = ck.commit_vec(&pts_prep);
    // transcript.append_point::<G>(b"point column", pts_comm);

    // let bits_poly = NestedPolynomial::from_values(
    //     bits_flatten
    //         .par_iter()
    //         .map(|x| F::from(*x as u64))
    //         .collect(),
    //     bits_flatten.len().log_2(),
    //     F::zero(),
    // );

    // let _points_table_poly: (Vec<_>, Vec<_>) = points
    //     .par_iter()
    //     .map(|p| repeatn(*p, num_scalar_bits))
    //     .flatten()
    //     .unzip();


    // let tmp = _points_table_poly.0.len().log_2();
    // let points_table_poly = (
    //     NestedPolynomial::from_values(
    //         _points_table_poly.0,
    //         tmp,
    //         F::zero(),
    //     ),
    //     NestedPolynomial::from_values(
    //         _points_table_poly.1,
    //         tmp,
    //         F::zero(),
    //     ),
    // );

    // // layer0
    // // bits_poly
    // // points_table_poly

    // let base_layer = vec![bits_poly, points_table_poly.0, points_table_poly.1];

    // // layer1
    // // filtered pts

    // let f_base = PolynomialMapping {
    //     exec: Arc::new(pt_bit_choice),
    //     degree: 2,
    //     num_i: 3,
    //     num_o: 2,
    // };

    // // Now, we will compute GKR witness.

    // let f_deg2 = PolynomialMapping {
    //     exec: Arc::new(twisted_edwards_add_l1::<F>),
    //     degree: 2,
    //     num_i: 6,
    //     num_o: 4,
    // };
    // let f_deg4 = PolynomialMapping {
    //     exec: Arc::new(twisted_edwards_add_l2::<F>),
    //     degree: 2,
    //     num_i: 4,
    //     num_o: 4,
    // };
    // let f_deg8 = PolynomialMapping {
    //     exec: Arc::new(twisted_edwards_add_l3::<F>),
    //     degree: 2,
    //     num_i: 4,
    //     num_o: 3,
    // };
    // let f_deg2_init = PolynomialMapping {
    //     exec: Arc::new(affine_twisted_edwards_add_l1::<F>),
    //     degree: 2,
    //     num_i: 4,
    //     num_o: 3,
    // };
    // let f_deg4_init = PolynomialMapping {
    //     exec: Arc::new(affine_twisted_edwards_add_l2::<F>),
    //     degree: 2,
    //     num_i: 3,
    //     num_o: 3,
    // };
    // let f_deg8_init = PolynomialMapping {
    //     exec: Arc::new(affine_twisted_edwards_add_l3::<F>),
    //     degree: 2,
    //     num_i: 3,
    //     num_o: 3,
    // };

    // let num_inner_layers = log_num_points - 1;

    // let layers = vec![
    //     Layer::Mapping(f_base),
    //     Layer::new_split(2),
    //     Layer::Mapping(f_deg2_init),
    //     Layer::Mapping(f_deg4_init),
    //     Layer::Mapping(f_deg8_init),
    // ]
    // .into_iter()
    // .chain(
    //     repeat(
    //         vec![
    //             Layer::new_split(3),
    //             Layer::Mapping(f_deg2.clone()),
    //             Layer::Mapping(f_deg4.clone()),
    //             Layer::Mapping(f_deg8.clone()),
    //         ]
    //         .into_iter(),
    //     )
    //     .take(num_inner_layers)
    //     .flatten(),
    // )
    // .collect_vec();

    // let params = BintreeParams::new(layers, num_vars);

    // let (trace, output) = Bintree::witness(base_layer, &params);

    // output
    //     .iter()
    //     .map(|p| transcript.append_scalars(b"output", &p.vec()))
    //     .count();
    // output
    //     .iter()
    //     .map(|p| assert_eq!(p.num_vars(), log_num_scalar_bits))
    //     .count();

    // let claim_point = (0..log_num_scalar_bits)
    //     .map(|_| transcript.challenge_scalar(b"output_claim_point").value)
    //     .collect_vec();

    // let claim_evals = output
    //     .iter()
    //     .map(|p| p.evaluate(&claim_point))
    //     .collect_vec();

    // let claim = to_multieval(EvalClaim {
    //     point: claim_point,
    //     evs: claim_evals,
    // });

    // let mut prover = BintreeProver::start(claim, trace, &params);

    // let mut res = None;
    // while res.is_none() {
    //     let challenge = transcript.challenge_scalar(b"challenge_nextround");
    //     res = prover.round(challenge, transcript);
    // }

    // let (gkr_evals, gkr_proof) = res.unwrap();


    // (
    //     gkr_evals,
    //     NonNativeCommitProof {
    //         bit_columns: bit_comms,
    //         point_column: pts_comm,
    //         gkr_proof,
    //         output: output
    //             .into_iter()
    //             .map(|p| p.vec().iter().map(|x| *x).collect_vec())
    //             .flatten()
    //             .collect_vec(),
    //     }
    // );
}


mod tests{
    use ark_bls12_381::Fq as Fq;
    use ark_ff::MontBackend;
    use ark_std::{test_rng, UniformRand};
    use ark_std::rand::Rng;
    use super::*;


    #[test]
    fn test_smolnum() {
        prime_field_element_to_bits(Fq::from(3));
        prime_field_element_to_bits(Fq::from(4));
        prime_field_element_to_bits(Fq::from(5));
        prime_field_element_to_bits(Fq::from(6));
    }

    #[test]
    fn test_bignum() {
        let mut rng = test_rng();
        println!("{:?}\n", (prime_field_element_to_bits((Fq::rand(&mut rng)))));
        println!("{:?}\n", (prime_field_element_to_bits(Fq::from(521))));
    }
    #[test]
    fn test_dense_poly_to_bits_1() {
        let mut rng = test_rng();
        let three = Fq::from(3);
        let four = Fq::from(4);
        let fiveee = Fq::from(5);
        let sixxx = Fq::from(6);
        let Z = vec![three, four, fiveee, sixxx];
        let inp = DensePolynomial{
            num_vars : 2,
            len : 4,
            Z
        };
        let p = polynomial_to_many_bit_polynomials(inp);

        println!("{:?}\n\n", p[p.len()-4 ..].to_vec());
    }

    #[test]
    fn test_dense_poly_to_bits_2() {
        let mut rng = test_rng();
        let three = Fq::from(3);
        let four = Fq::from(4);
        let fiveee = Fq::from(5);
        let sixxx = Fq::from(6);
        let Z = vec![three, four, fiveee, sixxx];
        let inp = DensePolynomial{
            num_vars : 2,
            len : 4,
            Z
        };
        let p = polynomial_to_one_polynomial_of_bits_sorted_by_bits(inp);
        println!("{:?}\n\n", p);
        let Z = p.Z.clone();
        println!("length: {:?}\n", Z.len());
        for (i, &x) in Z.iter().enumerate(){
            if x == Fq::from(1){
                println!("non-zero bits: {:?}", i);
            }
        }
    }

    #[test]
    fn test_dense_poly_to_bits_3() {
        let mut rng = test_rng();
        let three = Fq::from(3);
        let four = Fq::from(4);
        let fiveee = Fq::from(5);
        let sixxx = Fq::from(6);
        let Z = vec![three, four, fiveee, sixxx];
        let inp = DensePolynomial{
            num_vars : 2,
            len : 4,
            Z
        };
        let p = polynomial_to_one_polynomial_of_bits_sorted_by_values(inp);
        
        println!("{:?}\n\n", p);
        let Z = p.Z.clone();
        println!("length: {:?}\n", Z.len());
        for (i, &x) in Z.iter().enumerate(){
            if x == Fq::from(1){
                println!("non-zero bits: {:?}", i);
            }
        }
    }

    
    #[test]
    fn test_dense_poly_to_bits_4() {
        let mut rng = test_rng();
        let three = Fq::from(3);
        let Z = vec![three];
        let inp = DensePolynomial{
            num_vars : 0,
            len : 1,
            Z
        };
        let p = polynomial_to_one_polynomial_of_bits_sorted_by_values(inp);
        
        println!("{:?}\n\n", p);
        let Z = p.Z.clone();
        println!("length: {:?}\n", Z.len());
        for (i, &x) in Z.iter().enumerate(){
            if x == Fq::from(1){
                println!("non-zero bits: {:?}", i);
            }
        }
    }

    
    #[test]
    fn test_dense_poly_to_bits_5() {
        let mut rng = test_rng();
        let three = Fq::from(3);
        let four = Fq::from(4);
        let Z = vec![three, four];
        let inp = DensePolynomial{
            num_vars : 1,
            len : 2,
            Z
        };
        let p = polynomial_to_one_polynomial_of_bits_sorted_by_values(inp);
        
        println!("{:?}\n\n", p);
        let Z = p.Z.clone();
        println!("length: {:?}\n", Z.len());
        for (i, &x) in Z.iter().enumerate(){
            if x == Fq::from(1){
                println!("non-zero bits: {:?}", i);
            }
        }
    }
}