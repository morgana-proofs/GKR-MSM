#[allow(unused_imports)]
use std::{iter::repeat, marker::PhantomData, ops::{Add, AddAssign, SubAssign, Sub, Mul, MulAssign}, sync::Arc, u64};

use ark_ff::{PrimeField, Zero, One};
use ark_ff::biginteger::BigInteger;


pub mod polynomial_utils{
    use super::*;

    // given coefficients computes evals at -degree/2, ..., 0, 1, 2, ... , degree/2
    pub fn coeffs_to_evals_univar<F1, F2>(P: &[F1], degree: usize) -> Vec<F2>
    where F1: From<u64> + Mul<Output = F1> + AddAssign + SubAssign + Zero + Copy,
    F2: From<F1> + From<u64> + MulAssign + AddAssign + SubAssign + Zero + Copy + One{
        let mut res = vec![];
        for i in 0..degree + 1{
            let mut curr_res = F2::zero();
            let mut curr_deg = F2::one();
            for j in 0..degree + 1{
                curr_res += F2::from(P[j]) * curr_deg;
                curr_deg *= F2::from(i as u64);
            }
            res.push(curr_res)
        }
        res
        //gaussian_elimination();
    }


    pub fn vandermonde_matrix(desired_len: usize) -> Vec<Vec<i128>>{
        let mut res = vec![];
        for i in -(desired_len as i128 + 1)/2..(desired_len as i128)/2 + 1{
            let mut row = vec![1, i];
            for j in 1..desired_len{
                row.push(row[j]*i)
            }
            res.push(row)
        }
        res
    }


    // given coefficients computes evals at -desired_len/2, ..., 0, 1, 2, ... , desired_len/2
    pub fn coeffs_to_evals_with_precompute(P: &[i128], desired_len: usize) -> Vec<i128>{
        // let res = vec![];
        let v = vandermonde_matrix(desired_len);
        let mut v = v.iter();

        (0..v.len()).map(|i|{
            P.iter()   
                .zip(v.next().unwrap())
                .fold(0, |acc, (&a, b)| acc + a*b)
        }).collect()

    }


    pub fn binomial(n: usize, k: usize) -> u64{
        if k > n{
            return 0}
        if k > n-k{
            return binomial(n, n-k)
        }
        let mut res = 1;
        for i in 0..k{
            res *= (n-i);
            res /= (i+1); 
        }
        res as u64
    }


    // given evals at m, m+1, m+2, ... , k, evaluates at k+1
    pub fn extend_evals<F1, F2>(P: &[F1], degree: usize) -> F2
        where F1: From<u64> + Mul<Output = F1> + AddAssign + Add + SubAssign + Sub + Zero + Copy,
        F2: From<F1> + From<u64> + Mul<Output = F2> + AddAssign + SubAssign + Zero + Copy
    {
        let mut res = F2::zero();
        let start_index = P.len() - degree - 1;
        for i in 0..degree+1{
            if i %2 == degree % 2{
                res += (F2::from(P[start_index + i]) * F2::from(binomial(degree+1, i)));
            }
            else{
                res -= (F2::from(P[start_index + i]) * F2::from(binomial(degree+1, i)));
            }
        }
        res
        
    }



    // given evals at m, m+1, m+2, ... , k, evaluates at m-1
    pub fn extend_evals_backwards<F1, F2>(P: &[F1], degree: usize) -> F2
        where F1: From<u64> + Mul<Output = F1> + AddAssign + Add + SubAssign + Sub + Zero + Copy,
        F2: From<F1> + From<u64> + Mul<Output = F2> + AddAssign + SubAssign + Zero + Copy
    {
        let mut res = F2::zero();
        for i in 0..degree+1{
            if i %2 == 0{
                res += (F2::from(P[i]) * F2::from(binomial(degree+1, i+1)));
            }
            else{
                res -= (F2::from(P[i]) * F2::from(binomial(degree+1, i + 1)));
            }
        }
        res
        
    }


    // given evals at 0, 1, 2, ... , k, evaluates at k+1, ... k+l
    pub fn extend_evals_by_l<F>(P: &mut Vec<F>, degree: usize, l: usize)
    where F: From<F> + From<u64> + Mul<Output = F> + AddAssign + SubAssign + Add + Sub + Zero + Copy,
    {
        assert!(P.len() > degree);
        // let mut P: Vec<_> = P.to_vec();
        for _ in (0..l){
            P.push(extend_evals(&P, degree));
        }
        // P
    }


}
pub mod overflow_multiplication_utils{
    use std::path::absolute;

    /// credit https://stackoverflow.com/questions/70313420/128-bit-a-b-c-in-rust-with-phantom-overflow-protection
    /// 
    /// Returns the least significant 64 bits of a
    pub fn lo128(a: u128) -> u128 {
        a & ((1<<64)-1)
    }

    /// Returns the most significant 64 bits of a
    pub fn hi128(a: u128) -> u128 {
        a >> 64
    }

    /// Returns 2^128 - a (two's complement)
    pub fn neg128(a: u128) -> u128 {
        (!a).wrapping_add(1)
    }

    /// Returns 2^128 / a
    pub fn div128(a: u128) -> u128 {
        (neg128(a)/a).wrapping_add(1)
    }

    /// Returns 2^128 % a
    pub fn mod128(a: u128) -> u128 {
        neg128(a) % a
    }

    /// Returns a+b (wrapping)
    pub fn add256(a0: u128, a1: u128, b0: u128, b1: u128) -> (u128, u128) {
        let (r0, overflow) = a0.overflowing_add(b0);
        let r1 = a1.wrapping_add(b1).wrapping_add(overflow as u128);
        (r0, r1)
    }

    /// Returns a*b (in 256 bits)
    pub fn mul128(a: u128, b: u128) -> [u64;4] {
        // Split a and b into hi and lo 64-bit parts
        // a*b = (a1<<64 + a0)*(b1<<64 + b0)
        // = (a1*b1)<<128 + (a1*b0 + b1*a0)<<64 + a0*b0
        let (a0, a1) = (lo128(a), hi128(a));
        let (b0, b1) = (lo128(b), hi128(b));
        let (x, y) = (a1*b0, b1*a0);
        
        let (r0, r1) = (a0*b0, a1*b1);
        let (r0, r1) = add256(r0, r1, lo128(x)<<64, hi128(x));
        let (r0, r1) = add256(r0, r1, lo128(y)<<64, hi128(y));
        [(r0 >> 64) as u64, r0 as u64, (r1 >> 64) as u64, r1 as u64]
    }

        /// Returns sign and a*b (in 256 bits)
        pub fn mul_i128(a: i128, b: i128) -> (bool, [u64;4]) {
            // Split a and b into hi and lo 64-bit parts
            // a*b = (a1<<64 + a0)*(b1<<64 + b0)
            // = (a1*b1)<<128 + (a1*b0 + b1*a0)<<64 + a0*b0
            let sign = (a > 0) ^ (b < 0);

            let (a, b) = (a.abs() as u128, b.abs() as u128);

            let (a0, a1) = (lo128(a), hi128(a));
            let (b0, b1) = (lo128(b), hi128(b));
            let (x, y) = (a1*b0, b1*a0);
            
            let (r0, r1) = (a0*b0, a1*b1);
            let (r0, r1) = add256(r0, r1, lo128(x)<<64, hi128(x));
            let (r0, r1) = add256(r0, r1, lo128(y)<<64, hi128(y));
            (sign, [(r0 >> 64) as u64, r0 as u64, (r1 >> 64) as u64, r1 as u64])
        }

            /// Adds two 256 bit numbers, assuming no overflow
    pub fn add_bignums(a: (bool, [u64;4]), b: (bool, [u64;4])) ->(bool, [u64;4]) {

        // if both numbers have the same sign, add with carry;
        // otherwise, we determine the sign on the outcome, and subtract the one with smaller absolute value
        let mut  res = zero_256();
        
        if a.0 == b.0{
            res.0 = a.0;
            let mut carry = false;
            let mut new_carry = false;
            for i in 0..4{
                (res.1[3-i], carry) = a.1[3-i].overflowing_add(carry as u64) ;
                (res.1[3-i], new_carry) = res.1[3-i].overflowing_add(b.1[3-i]) ;
                carry = carry || new_carry;
            } 
        }
        else{
            let (a, b) = match a.0{
                false => (a, b),
                _ => (b, a)
            };
            res.0 = (a.1[0] < b.1[0]) ||(a.1[0] == b.1[0] && a.1[1] < b.1[1]) ||(a.1[1] == b.1[1] && a.1[2] < b.1[2])||(a.1[2] == b.1[2] && a.1[3] < b.1[3])  ;

            let (a, b) = match res.0{
                false => (a, b),
                _ => (b, a)
            };

            let mut borrow = false;
            let mut new_borrow = false;
            for i in 0..4{
                (res.1[3-i], borrow) = a.1[3-i].overflowing_sub(borrow as u64) ;
                (res.1[3-i], new_borrow) = res.1[3-i].overflowing_sub(b.1[3-i]) ;
                borrow = borrow || new_borrow;
                }
        }
        res
    }

    pub fn zero_256()->(bool, [u64; 4]){
        (false, [0; 4])
    }
}




pub mod bit_utils{
    use liblasso::utils::math::Math;

    use ark_ff::{biginteger::{BigInt, BigInteger64 as B1}, BigInteger};

    use super::*;

    pub trait BitMath {
        fn to_bits(self, max_bit_len: usize) ->  Vec<bool>;
      }
    
    impl BitMath for usize {
    fn to_bits(self, max_bit_len: usize) -> Vec<bool> {
        (0..max_bit_len)
            .map(|n| (self>>n)%2 == 1 )
            .collect()
        
        }
    }


    /// Splits field element into 64-bit limbs
    pub fn fe_to_limbs<F: PrimeField>(x: &F) -> Vec<u64>
    {
        x.into_bigint().as_ref().iter().map(|x| *x).collect()
    }

    pub fn limbs_to_fe<F: PrimeField>(x: &[u64]) -> F
    {
        // let x = x.iter().chain(repeat(&0)).take(F::BigInt::NUM_LIMBS);
        // F::from_bigint(F::BigInt(x)).unwrap()
        x.iter().rev().fold(F::zero(), |acc, x| acc + acc*F::from(u64::MAX) + F::from(*x))
    }


     

    pub fn big_num_to_limbs<F1: PrimeField, F2: PrimeField>(x: &F1, limb_len: usize) -> Vec<F2>
    {
        let x = x.into_bigint();

        assert_eq!(limb_len%8, 0);

        x.to_bytes_le()
            .chunks(limb_len)
            .map(|bytes| F2::from(F2::from_le_bytes_mod_order(bytes)))
            .collect()

    }


    pub fn big_num_to_bits_u64<const N: usize>(x: BigInt<N>) -> Vec<u64>
    {
        x.to_bits_le().iter().map(|&b| b as u64).collect()
    }


    pub fn big_num_to_bits_F<F: PrimeField, const N: usize>(x: BigInt<N>) -> Vec<F>
    { 
        x.to_bits_le().iter().map(|&b| F::from(b as u64)).collect()
    }

    
    pub fn roundup_to_pow2(x: usize) -> usize
    { 
        x.log_2().pow2()
    }

    pub fn transpose<T>(v: Vec<Vec<T>>) -> Vec<Vec<T>> // credit https://stackoverflow.com/questions/64498617/how-to-transpose-a-vector-of-vectors-in-rust
    where
        T: Clone,
    {
        // assert!(!v.is_empty());
        (0..v[0].len())
            .map(|i| v.iter().map(|inner| inner[i].clone()).collect::<Vec<T>>())
            .collect()
    }
}


#[cfg(test)]
pub mod test{
    #[allow(unused_imports)]

    use super::{polynomial_utils::{*}, overflow_multiplication_utils::{*}};

    use ark_bls12_381::Fr;
    use ark_bls12_381::Fq;
    use ark_bls12_381::G1Projective;
    use ark_ff::{MontBackend};
    use ark_ff::{biginteger::BigInteger, biginteger::BigInt};
    use ark_std::{test_rng, UniformRand};
    use ark_std::rand::Rng;
    use itertools::Itertools;
    use liblasso::utils::math::Math;
    use crate::protocol::protocol::MultiEvalClaim;
    use crate::protocol::protocol::{ProtocolVerifier, ProtocolProver};
    use crate::protocol::sumcheck::{*, SumcheckPolyMapVerifier, SumcheckPolyMapProver};
    use crate::transcript::Challenge;
    use crate::transcript::IndexedProofTranscript;
    use liblasso::utils::test_lib::TestTranscript;
        
    

    #[test]
    fn test_binomial_things(){
        let rng = &mut test_rng();
        let deg: u64 = 5;
        let coeffs = (0..deg + 1).map(|_| Fq::rand(rng)).collect_vec();
        //let coeffs = (0..deg + 1).map(|i| Fq::from(i)).collect_vec();

        let true_evals: Vec<_> = (0..deg + 1).map(|i| 
            coeffs.iter()
                .rev()
                .fold(Fq::from(0), |acc, x| Fq::from(i)*acc + x)
        ).collect();



        let mut evals: Vec<Fq> = coeffs_to_evals_univar(&coeffs, deg as usize);
        let last_eval = extend_evals(&evals, deg as usize);
        evals.push(last_eval);

        //println!("{:?}, \n\n{:?}", evals, true_evals);
        assert!(evals == true_evals);
    }

    #[test]
    fn test_vandermonde(){
        let rng = &mut test_rng();
        let deg_odd = 5;
        let deg_even = 6;
        let coeffs_odd = (0..deg_odd + 1).map(|_| i16::rand(rng) as i128).collect_vec();
        let coeffs_even = (0..deg_even + 1).map(|i| i16::rand(rng) as i128).collect_vec();

        let true_evals_odd: Vec<_> = ((-deg_odd - 1)/2 - 1..deg_odd/2 + 2).map(|i| 
            coeffs_odd.iter()
                .rev()
                .fold(0, |acc, x| i*acc + x)
        ).collect();



        let mut evals_odd = coeffs_to_evals_with_precompute(&coeffs_odd, deg_odd as usize);
        let last_eval_odd = extend_evals(&evals_odd, deg_odd as usize);
        let first_eval_odd = extend_evals_backwards(&evals_odd, deg_odd as usize);
        evals_odd.push(last_eval_odd);
        evals_odd.insert(0, first_eval_odd);

        println!("{:?}, \n\n{:?}", evals_odd, true_evals_odd);
        assert!(evals_odd == true_evals_odd);

        let true_evals_even: Vec<_> = ((-deg_even - 1)/2- 1..deg_even/2 + 2).map(|i| 
            coeffs_even.iter()
                .rev()
                .fold(0, |acc, x| i*acc + x)
        ).collect();



        let mut evals_even = coeffs_to_evals_with_precompute(&coeffs_even, deg_even as usize);
        let first_eval_even = extend_evals_backwards(&evals_even, deg_even as usize);
        let last_eval_even = extend_evals(&evals_even, deg_even as usize);
        evals_even.push(last_eval_even);
        evals_even.insert(0, first_eval_even);


        println!("{:?}, \n\n{:?}", evals_even, true_evals_even);
        assert!(evals_even == true_evals_even);
    }

    use test_case::test_case;
    #[test_case([(false, [0, 0, 0, 1]), (true, [0, 0, 0, 5]), (true, [0, 0, 0, 4])] ; "one negative one positive")]
    #[test_case([(true, [0, 0, 0, 1]), (false, [0, 0, 0, 5]), (false, [0, 0, 0, 4])]  ; "one negative one positive, positive result")]
    #[test_case([(true, [0, 0, 0, 5]), (true, [0, 0, 0, 1]), (true, [0, 0, 0, 6])]  ; "when operands are swapped")]
    fn test_add_bignums(ins  : [(bool, [u64; 4]) ; 3]) {
        let [a, b, c] = ins;
        assert_eq!(add_bignums(a, b), c);

        //TODO: add a random test

        // let rng = &mut test_rng();
        // let a_digits = (0..4).map(|_|u32::rand(rng) as u64).try_into();
        // let b_digits = (0..4).map(|_|u32::rand(rng) as u64).try_into();
        // let a = (true, a_digits);
        // let b = (true, b_digits);
        // let c = (true, a_digits.iter().zip(b_digits).map(|(x, y)| x+y).try_into());
        // assert_eq!(add_bignums(a, b), c);

    }


}

