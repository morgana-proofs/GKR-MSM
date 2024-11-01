
fn make_prover_response<F: PrimeField>(Pxy: &[u64], Px: &[u64], Py: &[u64], num_limbs: usize) -> Vec<F> 
// num_limbs should be 6...
{
    let deg = num_limbs - 1;

    let (Pxy, Px, Py) = (Pxy.iter().map(|x| *x as i128).collect_vec(), Px.iter().map(|x| *x as i128).collect_vec(), Py.iter().map(|x| *x as i128).collect_vec());

    let degree_of_first_product = 2*deg;
    let degree_of_second_product = 3*deg;

    // multiplying Pxy by Px and summing by x
    let evalsxy = Pxy.chunks(Px.len())
        .map(|chunk|
            chunk.chunks(num_limbs)
                .zip(Px.chunks(num_limbs))
                .map(|(a, b)|{
                    let evals_a = coeffs_to_evals_with_precompute(a, degree_of_first_product + 1);
                    let evals_b = coeffs_to_evals_with_precompute(b, degree_of_first_product + 1);
                    println!("{:?}, {:?}", evals_a, evals_b);
                    let m = evals_a.iter().zip(evals_b).map(|(&s, t)| mul_i128(s, t)).collect_vec();
                    println!("{:?}", m);
                    m
                })
                .fold(vec![zero_256(); degree_of_first_product+1], |acc, x|{
                    acc.iter().zip(x).map(|(&s, t)| add_bignums(s, t)).collect()
               })
               .iter()
               .map(|(flag, limbs)| 
                    match flag{
                        false => limbs_to_fe::<F>(limbs),
                        _ => limbs_to_fe::<F>(limbs).neg(),
               })
            //    .map(|(flag, limbs)| match flag{
            //     false => - (limbs.iter().sum::<u64>() as i128),
            //     _ => (limbs.iter().sum::<u64>() as i128),
            //    })
               .collect_vec())
        .collect_vec();
    
    let final_evals = evalsxy.iter()
        .zip(Py.chunks(num_limbs))
        .map(|(a, b)|{
            let a = extend_evals_by_2l_symmetric(&a, degree_of_first_product, deg);
            let b = coeffs_to_evals_with_precompute(b, degree_of_second_product + 1);
            println!("{:?}, {:?}", a, b);
            let res = a.iter()
                .zip(b)
                .map(|(s, t)| {
                    i128_to_fe::<F>(t)*s
                })
                .collect_vec();
            println!("{:?}", res);
            res
        })
        .fold( vec![F::zero(); degree_of_second_product + 1], | acc, x|{
            acc.iter().zip(x).map(|(x, y)| *x + y).collect()
        });
        final_evals
//    todo!();
}
