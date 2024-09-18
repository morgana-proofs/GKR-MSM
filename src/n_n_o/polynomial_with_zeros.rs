use super::*;

use ark_ff::{biginteger::{BigInt, BigInteger64 as B1}, BigInteger};

use ark_ff::PrimeField;
use liblasso::utils::math::Math;

use super::non_native_equalizer::bit_utils::{*, BitMath};

use rayon::iter::plumbing::UnindexedConsumer;
use rayon::prelude::*;

use core::num;
use std::ops::{Neg, AddAssign, Add, SubAssign, Sub, Mul,};
use std::cmp::{Eq, PartialEq};
use std::iter;

use ark_std::{One, Zero, UniformRand};

use rand::prelude::{Rng, thread_rng};



#[derive(Debug, Default, Clone)]
pub struct PolynomialWithZeros<F: Zero>{
    // evals is a list of (non-zero) evaluations; the real eval list has length 2**log_len with the last several evals being zero
    // e.g. if we want to encode bits of a 254-bit number as evals, len should be 254, and log_len is 8
    pub evals: Vec<F>,
    pub len: usize,
    pub log_len: usize,
}


impl <F: Sub<Output = F> + Add + AddAssign + Mul + One + Zero + Send + Sync + Sized + Copy> PolynomialWithZeros<F>
{
    pub fn new(evals: &[F]) -> Self
    {
        let eval_vec = evals.into();
        let len = evals.len();
        let log_len = len.log_2();

        PolynomialWithZeros{
            evals: eval_vec,
            len,
            log_len
        }
    }

    pub fn zero_of_given_len(len: usize) -> Self{
        let log_len = len.log_2();
        let evals = vec![F::zero(); len];
        PolynomialWithZeros{
            evals,
            len,
            log_len,
        }
        
    }
    
    pub fn zero_of_given_num_vars(num_vars: usize) -> Self{
        PolynomialWithZeros{
            evals: vec![],
            len: 0,
            log_len: num_vars,
        }
        
    }

    pub fn split(&self) -> (Self, Self)
    {
        let l_evals = self.evals.clone().into_iter().step_by(2).collect();  
        let r_evals =self.evals.clone().into_iter().skip(1).step_by(2).collect(); 
        let l = PolynomialWithZeros{
            evals: l_evals,
            len : (self.len + 1)/2,
            log_len : self.log_len - 1
        };

        let r = PolynomialWithZeros{
            evals: r_evals,
            len : self.len /2,
            log_len : self.log_len - 1
        };

        (l, r)
    }

    pub fn bind_from(&mut self, rhs: &Self, f: &F){
        assert_eq!(self.log_len, rhs.log_len, "only call this function from bind");
        assert!(self.len >= rhs.len, "only call this function from bind");
        self.evals.iter_mut()
            .zip(rhs.evals.iter().chain(iter::repeat(&F::zero())))
            .map(|(l, r)| { *l += *f * (*r - *l) }).count();
    }


    // sets the last variable equal to f
    pub fn bind(&self, f: &F) -> Self {
        let (mut l, r) = self.split();
        l.bind_from(&r, f);
        l
    }

    
    // sums all evals
    pub fn sum(&self) -> F {
        self.evals.iter().fold(F::zero(),|acc, &x| acc + x)
    }


    // for testing
    pub fn evaluate(&self, r: &[F]) -> F
    {
        assert_eq!(r.len(), self.log_len, "trying to evaluate at a point with different dimention");

        let ans = self.evals.iter().enumerate().map(
            |(i, &ev)|{
                let i_bits = i.to_bits(self.log_len);
                let copol = i_bits
                    .iter()
                    .zip(r)
                    .map(|(&y, ev)|
                        match y {
                            true => ev.to_owned(),
                            false => F::one() - ev.to_owned(),
                    }).fold(F::one(), |acc, x| acc*x);
                copol*ev
            }  
        ).fold(F::zero(), |acc, x| acc+x);
        ans
    }
    
}


impl <F: UniformRand + Zero + Send + Sync + Sized + Copy> PolynomialWithZeros<F>
{
    pub fn rand<RNG: Rng>(rng: &mut RNG, len: usize, num_vars: usize) -> Self{
        let evals = (0..len).map(|_| F::rand(rng)).collect();
        PolynomialWithZeros{
            evals,
            len: len,
            log_len: num_vars,
        }
        
    }
}


impl<F: Sub<Output = F> + Zero + Send + Sync + Sized + Copy> SubAssign<&Self> for  PolynomialWithZeros<F> {
    fn sub_assign(&mut self, rhs: &Self) {
        assert_eq!(self.log_len, rhs.log_len);
        if self.len >= rhs.len{
            self.evals = self.evals.iter()
                        .zip(rhs.evals.iter().chain(iter::repeat(&F::zero())))
                        .map(|(&a, &b)| a- b)
                        .collect();
        }
        else{
            self.evals = rhs.evals.iter()
                        .zip(self.evals.iter().chain(iter::repeat(&F::zero())))
                        .map(|(&a, &b)| a- b)
                        .collect();
            self.len = rhs.len;
        }
    }
}

impl<F: Add<Output = F> +  Zero + Send + Sync + Sized + Copy> AddAssign<&Self> for  PolynomialWithZeros<F> {
    fn add_assign(&mut self, rhs: &Self) {assert_eq!(self.log_len, rhs.log_len);
        if self.len >= rhs.len{
            self.evals = self.evals.iter()
                        .zip(rhs.evals.iter().chain(iter::repeat(&F::zero())))
                        .map(|(&a, &b)| a+ b)
                        .collect();
        }
        else{
            self.evals = rhs.evals.iter()
                        .zip(self.evals.iter().chain(iter::repeat(&F::zero())))
                        .map(|(&a, &b)| a+ b)
                        .collect();
            self.len = rhs.len;
        }
    }
}

impl<F:  Add<Output = F> + Zero + Send + Sync + Sized + Copy> Add for PolynomialWithZeros<F>{
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let mut ans = self.clone();
        ans += &rhs;
        ans

    }
}

impl<F:  Sub<Output = F> + Zero + Send + Sync + Sized + Copy> Sub for PolynomialWithZeros<F>{
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let mut ans = self.clone();
        ans -= &rhs;
        ans

    }
}


impl<F:  Zero + Send + Sync + Sized + Copy + Eq> PartialEq for PolynomialWithZeros<F> {
    fn eq(&self, other: &Self) -> bool  {
        if ! (self.log_len == other.log_len){
            false
        }
        else if self.len >= other.len {
            self.evals.iter().zip(other.evals.iter().chain(iter::repeat(&F::zero()))).fold(true, |acc, (&a,  &b)| acc && (a== b))
        }
        else{
            other.evals.iter().zip(self.evals.iter().chain(iter::repeat(&F::zero()))).fold(true, |acc, (&a,  &b)| acc && (a== b))
        }
    }
}

