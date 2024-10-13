use super::*;

use ark_ff::{biginteger::{BigInt, BigInteger64 as B1}, BigInteger};

use ark_ff::PrimeField;
use liblasso::utils::math::Math;

use super::non_native_equalizer::bit_utils::{*, BitMath};

use rayon::iter::plumbing::UnindexedConsumer;
use rayon::prelude::*;

use core::num;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
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


impl <F: Sub<Output = F> + Add + AddAssign + SubAssign + Mul + MulAssign+ One + Zero + Send + Sync + Sized + Copy> PolynomialWithZeros<F>
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
        // computing lhs + (rhs-lhs)*f = (lhs - rhs)*(1-f) + rhs, trying not to clone
        *self-=rhs;
        *self*=(F::one() - *f);
        *self += rhs;
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
        assert_eq!(r.len(), self.log_len, "trying to evaluate at a point in the wrong dimention");

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


mod utils{
    use super::*;
    pub(super) fn add_if_lhs_is_longer<F: AddAssign + Zero + Send + Sync + Sized + Copy>(lhs: &mut PolynomialWithZeros<F>, rhs: &PolynomialWithZeros<F>){
        lhs.evals.iter_mut()
            .zip(rhs.evals.iter().chain(iter::repeat(&F::zero())))
            .map(|(a, b)| *a+= *b)
            .count();
    }

    pub(super) fn sub_if_lhs_is_longer<F: SubAssign + Zero + Send + Sync + Sized + Copy>(lhs: &mut PolynomialWithZeros<F>, rhs: &PolynomialWithZeros<F>){
        lhs.evals.iter_mut()
            .zip(rhs.evals.iter().chain(iter::repeat(&F::zero())))
            .map(|(a, b)| *a-= *b)
            .count();
    }
}
use utils::*;
impl<F: Sub<Output = F> + SubAssign + Zero + Send + Sync + Sized + Copy> SubAssign<&Self> for  PolynomialWithZeros<F> {
    fn sub_assign(&mut self, rhs: &Self) {
        assert_eq!(self.log_len, rhs.log_len);
        if self.len >= rhs.len{
            sub_if_lhs_is_longer(self, rhs);
        }
        else{
            let mut vec_zeros = vec![F::zero();  rhs.len - self.len];
            self.evals.append(&mut vec_zeros);
            self.len = rhs.len;
            sub_if_lhs_is_longer(self, rhs); 
        }
    }
}

impl<F: Add<Output = F> + AddAssign + Zero + Send + Sync + Sized + Copy> AddAssign<&Self> for  PolynomialWithZeros<F> {
    fn add_assign(&mut self, rhs: &Self) {assert_eq!(self.log_len, rhs.log_len);
        if self.len >= rhs.len{
            add_if_lhs_is_longer(self, rhs)  
        }
        // else if self.len == rhs.len - 1{
        //     self.evals.push(F::zero());
        //     self.len += 1;
        //     add_if_lhs_is_longer(self, rhs); 
        // }
        else{
            let mut vec_zeros = vec![F::zero();  rhs.len - self.len];
            self.evals.append(&mut vec_zeros);
            self.len = rhs.len;
            add_if_lhs_is_longer(self, rhs); 
            // self.evals = rhs.evals.iter()
            //             .zip(self.evals.iter().chain(iter::repeat(&F::zero())))
            //             .map(|(&a, &b)| a+ b)
            //             .collect();
        }
    }
}


impl<F: Mul<Output = F> + MulAssign + Zero + Send + Sync + Sized + Copy> MulAssign<F> for  PolynomialWithZeros<F> {
    fn mul_assign(&mut self, rhs: F)
    {
        self.evals.iter_mut()
            .map(|a | *a *= rhs)
            .count();
    }
        
}


impl<F:  Add<Output = F> + AddAssign+ Zero + Send + Sync + Sized + Copy> Add for PolynomialWithZeros<F>{
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let mut ans = self.clone();
        ans += &rhs;
        ans

    }
}

impl<F:  Sub<Output = F> + SubAssign+ Zero + Send + Sync + Sized + Copy> Sub for PolynomialWithZeros<F>{
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let mut ans = self.clone();
        ans -= &rhs;
        ans

    }
}




impl<F:  Mul<Output = F> + Zero + One + Send + Sync + Sized + Copy> Mul<F> for PolynomialWithZeros<F>{
    type Output = Self;
    fn mul(self, rhs: F) -> Self {
        let evals = self.evals.iter()
                    .map(|&a | a * rhs)
                    .collect();
        PolynomialWithZeros{
            evals,
            len: self.len,
            log_len : self.log_len,
        }

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




#[derive(Debug, Default, Clone)]
pub struct PolynomialWithZeros2D<F: Zero>{
    pub evals: Vec<PolynomialWithZeros<F>>,
    pub height: usize,
    pub log_height: usize,
}


impl <F: Sub<Output = F> + SubAssign + AddAssign + Mul + MulAssign + One + Zero + Send + Sync + Sized + Copy> PolynomialWithZeros2D<F>
{
    pub fn new(evals: Vec<Vec<F>>) -> Self // make into evals: &[&[_]]
    {
        //todo!();
        let evals : Vec<_> = evals.iter().map(|x| PolynomialWithZeros::new(x)).collect();
        let height = evals.len();
        let log_height = height.log_2();

        PolynomialWithZeros2D{
            evals,
            height,
            log_height
        }
    }

    pub fn zero_of_given_len_height(len: usize, height: usize) -> Self{
        let zero_of_len = PolynomialWithZeros::zero_of_given_len(len);
        let log_height = height.log_2();
        let evals = vec![zero_of_len; height];
        PolynomialWithZeros2D{
            evals,
            height,
            log_height
        }
        
    }

    pub fn split_by_height(&self) -> (Self, Self)  // the polynomials inside stay the same, but go into two different bunches
    {
        let top_evals = self.evals.clone().into_iter().step_by(2).collect();  
        let bot_evals =self.evals.clone().into_iter().skip(1).step_by(2).collect(); 
        let top = PolynomialWithZeros2D{
            evals: top_evals,
            height: (self.height+1)/2,
            log_height: self.log_height-1,
        };

        let bot = PolynomialWithZeros2D{
            evals: bot_evals,
            height: self.height/2,
            log_height: self.log_height-1,
        };

        (top, bot)
    }
    pub  fn split(&self) -> (Self, Self){
        self.split_by_len()
    }


    pub fn split_by_len(&self) -> (Self, Self)  // heigh remains the same, each of the polynomials gets split
    {
        let (l_evals, r_evals): (Vec<_>, Vec<_>) = self.evals.clone().into_iter().map(|x| x.split()).unzip();
        let l = PolynomialWithZeros2D{
            evals: l_evals,
            height: self.height,
            log_height: self.log_height,
        };
        
        let r = PolynomialWithZeros2D{
            evals: r_evals,
            height: self.height,
            log_height: self.log_height,
        };

        (l, r)
    }

    pub fn bind_from(&mut self, rhs: &Self, f: &F){
        assert_eq!(self.log_height, rhs.log_height, "only call this function from bind");
        assert!(self.height >= rhs.height, "only call this function from bind");
        let (len, log_len) = (self.evals[0].len, self.evals[0].log_len);
        let zero = PolynomialWithZeros::zero_of_given_len(len);
        self.evals.iter_mut()
            .zip(rhs.evals.iter().chain(iter::repeat(&zero)))
            .map(|(l, r)| { 
                // computing l + (r-l)*f = (l - r)*(1-f) + r, trying not to clone
                *l-=r;
                *l*=(F::one() - *f);
                *l += r;
            }).count();
    }


    // sets the last variable equal to f
    pub fn bind(&self, f: &F) -> Self {
        let (mut l, r) = self.split();
        l.bind_from(&r, f);
        l
    }

    
    // sums all evals
    pub fn sum(&self) -> F {
        todo!();
    //     self.evals.iter().fold(F::zero(),|acc, &x| acc + x)
    }


    // for testing
    pub fn evaluate(&self, r: &[F]) -> F
    {
        todo!();
        // assert_eq!(r.len(), self.log_len, "trying to evaluate at a point with different dimention");

        // let ans = self.evals.iter().enumerate().map(
        //     |(i, &ev)|{
        //         let i_bits = i.to_bits(self.log_len);
        //         let copol = i_bits
        //             .iter()
        //             .zip(r)
        //             .map(|(&y, ev)|
        //                 match y {
        //                     true => ev.to_owned(),
        //                     false => F::one() - ev.to_owned(),
        //             }).fold(F::one(), |acc, x| acc*x);
        //         copol*ev
        //     }  
        // ).fold(F::zero(), |acc, x| acc+x);
        // ans
    }
    
}


impl <F: UniformRand + Zero + Send + Sync + Sized + Copy> PolynomialWithZeros2D<F>
{
    pub fn rand<RNG: Rng>(rng: &mut RNG, len: usize, num_vars_len: usize, height: usize, num_vars_height: usize) -> Self{
        let evals = (0..len).map(|_| PolynomialWithZeros::rand(rng, len, num_vars_len)).collect();
        PolynomialWithZeros2D{
            evals,
            height,
            log_height: num_vars_height,
        }
        
    }
}


impl<F: Sub<Output = F> + Add<Output = F> + AddAssign + SubAssign + MulAssign + Zero + One + Send + Sync + Sized + Copy> SubAssign<&Self> for  PolynomialWithZeros2D<F> {
    fn sub_assign(&mut self, rhs: &Self) {
        assert_eq!(self.log_height, rhs.log_height, "trying to add polynomials with different number of variables");
        let (len, _log_len) = (self.evals[0].len, self.evals[0].log_len);
        let zero = PolynomialWithZeros::zero_of_given_len(len);
        if self.height >= rhs.height{
            self.evals.iter_mut()
                .zip(rhs.evals.iter().chain(iter::repeat(&zero)))
                .map(|(a, b)| {*a-= b})
                .count();
        }
        else{
            unreachable!("The current protocol shoouldn't go here")
            // self.evals = rhs.evals.clone().iter_mut()
            //             .zip(self.evals.iter().chain(iter::repeat(&zero)))
            //             .map(|(a, b)| {*a -= b; a})
            //             .collect();
            // self.height = rhs.height;
        }
    }
}

impl<F: Sub<Output = F> + Add<Output = F> + AddAssign + SubAssign + Zero + MulAssign + One + Send + Sync + Sized + Copy> AddAssign<&Self>  for  PolynomialWithZeros2D<F> {
    fn add_assign(&mut self, rhs: &Self) {
        assert_eq!(self.log_height, rhs.log_height, "trying to add polynomials with different number of variables");
        let (len, _log_len) = (self.evals[0].len, self.evals[0].log_len);
        let zero = PolynomialWithZeros::zero_of_given_len(len);
        if self.height >= rhs.height{
            self.evals.iter_mut()
                        .zip(rhs.evals.iter().chain(iter::repeat(&zero)))
                        .map(|(a, b)| {*a+= b})
                        .count();
        }
        else{
            // this is implemented poorly, but i believe, this arm should be unreacheable in the actual protocol
            self.evals = rhs.evals.iter()
                        .zip(self.evals.iter().chain(iter::repeat(&zero)))
                        .map(|(a, b)| a.clone()+ b.clone())
                        .collect();
            self.height = rhs.height;
        }
    }
}

impl<F: Sub<Output = F> + Add<Output = F> + AddAssign + SubAssign + MulAssign + Zero + One + Send + Sync + Sized + Copy> Add for PolynomialWithZeros2D<F>{
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let mut ans = self.clone();
        ans += &rhs;
        ans

    }
}

impl<F: Sub<Output = F> + Add<Output = F> + AddAssign + SubAssign + MulAssign + Zero + One + Send + Sync + Sized + Copy> Sub for PolynomialWithZeros2D<F>{
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let mut ans = self.clone();
        ans -= &rhs;
        ans

    }
}


impl<F: Mul<Output = F> + MulAssign + Zero + Send + Sync + Sized + Copy> MulAssign<F> for  PolynomialWithZeros2D<F> {
    fn mul_assign(&mut self, rhs: F)
    {
        self.evals.iter_mut()
            .map(|a | *a *= rhs)
            .count();
    }
        
}




impl<F:  Mul<Output = F> + Zero + One + Send + Sync + Sized + Copy> Mul<F> for PolynomialWithZeros2D<F>{
    type Output = Self;
    fn mul(self, rhs: F) -> Self {
        let evals = self.evals.iter()
                    .map(|a | a.clone() * rhs)
                    .collect();
        PolynomialWithZeros2D{
            evals,
            height: self.height,
            log_height : self.log_height,
        }

    }
}


impl<F:  Zero + Send + Sync + Sized + Copy + Eq> PartialEq for PolynomialWithZeros2D<F> {
    fn eq(&self, other: &Self) -> bool  {
        if ! (self.log_height == other.log_height){
            false
        }
        else if self.height == other.height {
            let (len, _log_len) = (self.evals[0].len, self.evals[0].log_len);
            self.evals.iter().zip(other.evals.iter()).fold(true, |acc, (a,  b)| acc && (a== b))
        }
        else{
            false
            //other.evals.iter().zip(self.evals.iter().chain(iter::repeat(&F::zero()))).fold(true, |acc, (&a,  &b)| acc && (a== b))
        }
    }
}

