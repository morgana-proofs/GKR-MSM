use super::*;
use ark_ff::{biginteger::{BigInt, BigInteger64 as B1}, BigInteger};
use ark_ff::PrimeField;
use liblasso::utils::math::Math;
use rayon::iter::plumbing::UnindexedConsumer;
use rayon::prelude::*;
use core::fmt;
use std::ops::{Neg, AddAssign, Add, SubAssign, Sub, Mul,};
use std::iter;
use ark_std::{One, Zero};
use std::fmt::Debug;

use super::cleanup::utils::bit_utils::{*, BitMath};
use super::polynomial_with_zeros::{PolynomialWithZeros};

  
#[derive(Debug, Default, Clone)]
pub struct Splits<F: PrimeField> {
    pub lpolys: Vec<PolynomialWithZeros<F>>,
    pub rpolys: Vec<PolynomialWithZeros<F>>,
}

#[derive(Clone)]
pub struct NonNatOpen<FNat: PrimeField> {
    pub polys: Vec<PolynomialWithZeros<FNat>>,
    splits: Option<Splits<FNat>>,
    gamma: Option<FNat>,
    challenges: Vec<FNat>,
    round_polys : Vec<UniPoly<FNat>>,
    //f: PolynomialMapping<FNat>,
    folded_f: Option<Arc<dyn Fn(&[FNat]) -> FNat + Sync + Send>>,
    degree: usize,
}

impl<FNat: PrimeField> Debug for NonNatOpen<FNat>{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result{
        f.debug_struct("Non-Native Open Protocol")
         .field("input polynomials", &self.polys)
         .field("challenges", &self.challenges)
         .field("round_polynomials", &self.round_polys)
         .finish()
    }
}

impl<FNat : PrimeField> NonNatOpen<FNat>{
    pub fn new_from_polys(polys : &[PolynomialWithZeros<FNat>]) -> Self{
        NonNatOpen{
            polys : polys.into(),
            splits : None,
            gamma : None,
            challenges : vec![],
            round_polys : vec![],
            folded_f : None,  
            degree: 1,
        }
    }

    pub fn new_from_evals(evals : &[&[FNat]]) -> Self{
        let polys = evals.iter().map(|&eval_vec| PolynomialWithZeros::new(eval_vec)).collect();
        NonNatOpen{
            polys : polys,
            splits : None,
            gamma : None,
            challenges : vec![],
            round_polys : vec![],
            folded_f : None,
            degree: 1,
        }
    }
}

impl<FNat: PrimeField> Sumcheckable<FNat> for NonNatOpen<FNat>{
    fn bind(&mut self, f: &FNat){
        self.split();
        let Splits { mut lpolys, rpolys, .. } = self.splits.take().unwrap();

        lpolys.par_iter_mut().zip(rpolys.par_iter()).map(|(l, r)| {
            l.bind_from(r, f);
        }).count();
        self.polys = lpolys;
    }

    fn split(&mut self) {
        
        if self.splits.is_some() {
            return;
        }
        let (lpolys, rpolys): (Vec<PolynomialWithZeros<FNat>>, Vec<PolynomialWithZeros<FNat>>) = self.polys.par_iter().map(|p| p.split()).unzip();
        self.splits = Some(Splits {
            lpolys,
            rpolys,
        })
    }
    fn unipoly(&mut self) -> UniPoly<FNat>{
        self.split();
        let Splits { lpolys, rpolys } = self.splits.take().unwrap();

        let lsum: Vec<_> = lpolys.iter().map(|p| p.sum()).collect();
        let rsum: Vec<_> = rpolys.iter().map(|p| p.sum()).collect();

        

        todo!();

    }

    fn final_evals(&self) -> Vec<FNat>{
        self.polys.par_iter().map(|poly| poly.evals[0]).collect()
    }
}
