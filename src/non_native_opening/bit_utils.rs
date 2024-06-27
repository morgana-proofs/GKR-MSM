use super::*;

pub fn bytes_to_bit_le(
    n: Vec<u8>,
) -> Vec<u8>
{
    let mut bits = vec![];
    for byte in n{
        for i in 0..8 {
            let mask = 1 << i;
            let bit_is_set = ((mask & byte) > 0) as u8;
            bits.push(bit_is_set);
        }
    }
    bits

}


pub fn bytes_to_bit_be(
    n: Vec<u8>,
) -> Vec<u8>
{
    let mut bits = vec![];
    for byte in n{
        for i in 0..8 {
            let mask = 1 << (7 - i);
            let bit_is_set = ((mask & byte) > 0) as u8;
            bits.push(bit_is_set);
        }
    }
    bits

}


pub fn prime_field_element_to_bits<F: PrimeField>(
    n: F,
) -> Vec<F>
{
    let mut bigint_n: <F as PrimeField>::BigInt = n.into_bigint();
    big_integer_to_bits_in_fe(bigint_n)

}

pub fn prime_field_element_to_bool_bits<F: PrimeField>(
    n: F,
) -> Vec<bool>
{
    let mut bigint_n: <F as PrimeField>::BigInt = n.into_bigint();
    big_integer_to_bool_bits(bigint_n)

}


pub fn big_integer_to_bool_bits<B: BigInteger>(
    bigint_n: B,
) -> Vec<bool>
{
    let bytes = bigint_n.to_bytes_be();
    let ans: Vec<_> = bytes_to_bit_be(bytes).iter()
                                        .map(|&x| x!= 0)
                                        .collect();
    ans
}

pub fn big_integer_to_bits_in_fe<F: PrimeField, B: BigInteger>(
    bigint_n: B,
) -> Vec<F>
{
    let bytes = bigint_n.to_bytes_be();
    let ans: Vec<F> = bytes_to_bit_be(bytes).iter()
                                        .map(|&x| F::from_le_bytes_mod_order(&[x]))
                                        .collect();
    ans
}

fn transpose<T>(v: Vec<Vec<T>>) -> Vec<Vec<T>>
where
    T: Clone,
{
    assert!(!v.is_empty());
    (0..v[0].len())
        .map(|i| v.iter().map(|inner| inner[i].clone()).collect::<Vec<T>>())
        .collect()
}

pub fn evals_to_long_bit_vec_sorted_by_bits_be<B: BigInteger>(evals: Vec<B>) -> Vec<bool>
{

    let bit_vec_vec: Vec<_> = evals.iter()
                                .map(|&x| big_integer_to_bool_bits(x))
                                .collect();

    let bit_vec_vec_t: Vec<_> = transpose(bit_vec_vec);
    
    let bit_vec: Vec<_> = bit_vec_vec_t.iter()
                                .flatten()
                                .map(|&x| x)
                                .collect();
    bit_vec
}

// takes a polynomial with evaluations in F that can be treated as non-negative integers
// returns a list of polynomials with evaluations in F that are bits of the original polynomial
// e.g. input = {p(0) = 0, p(1) = 1, p(2) = 2, p(3) = 3}
// output = vec![{p(0) = 0, p(1) = 1, p(2) = 0, p(3) = 1}, {p(0) = 0, p(1) = 0, p(2) = 1, p(3) = 1}]
pub fn polynomial_to_many_bit_polynomials<F: PrimeField>(
    p: DensePolynomial<F>,
) -> Vec<DensePolynomial<F>>
{
    let (num_vars, len, Z) = (p.num_vars, p.len, p.Z);
    let v: Vec<_> = Z.iter()
                    .map(|&x| prime_field_element_to_bits(x))
                    .collect();
    let w = transpose(v);
    let ans: Vec<_> = w.iter()
                    .map(|x| DensePolynomial{num_vars, len, Z: x.to_vec()})
                    .collect();
    ans
}

// takes a polynomial with evaluations in F that can be treated as non-negative integers
// returns a polynomial with evaluations in F that are bits of the original polynomial
// sorted by significance of bits
// e.g. input = {p(0) = 0, p(1) = 1, p(2) = 2, p(3) = 3}
// output = {p(0) = 0, p(1) = 1, p(2) = 0, p(3) = 1, p(4) = 0, p(5) = 0, p(6) = 1, p(7) = 1}
pub fn polynomial_to_one_polynomial_of_bits_sorted_by_bits<F: PrimeField>(
    p: DensePolynomial<F>,
) -> DensePolynomial<F>
{
    let (num_vars, len, Z) = (p.num_vars, p.len, p.Z);
    let v: Vec<_> = Z.iter()
                    .map(|&x| prime_field_element_to_bits(x))
                    .collect();
    let w = transpose(v);
    let w: Vec<_> = w.iter().flatten().map(|&x| x).collect();
    DensePolynomial{num_vars, len, Z: w}
}

// takes a polynomial with evaluations in F that can be treated as non-negative integers
// returns a polynomial with evaluations in F that are bits of the original polynomial
// sorted by the order of original values
// e.g. input = {p(0) = 0, p(1) = 1, p(2) = 2, p(3) = 3}
// output = {p(0) = 0, p(1) = 0, p(2) = 1, p(3) = 0, p(4) = 0, p(5) = 1, p(6) = 1, p(7) = 1}
pub fn polynomial_to_one_polynomial_of_bits_sorted_by_values<F: PrimeField>(
    p: DensePolynomial<F>,
) -> DensePolynomial<F>
{
    let (num_vars, len, Z) = (p.num_vars, p.len, p.Z);
    let v: Vec<_> = Z.iter()
                                    .map(|&x| prime_field_element_to_bits(x))
                                    .collect();
                                
    let w: Vec<_> = v.iter().flatten().map(|&x| x).collect();
    DensePolynomial{num_vars, len, Z: w}    
}

