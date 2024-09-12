use super::*;
use ark_ff::{biginteger::{BigInt, BigInteger64 as B1}, BigInteger};

use ark_ff::PrimeField;
use liblasso::utils::math::Math;

use super::non_native_equalizer::bit_utils::{*, BitMath};

use rayon::iter::plumbing::UnindexedConsumer;
use rayon::prelude::*;

use std::ops::{Neg, AddAssign, Add, SubAssign, Sub, Mul,};
use std::iter;

use ark_std::{One, Zero};

use super::polynomial_with_zeros::{PolynomialWithZeros};


#[derive(Debug, Default, Clone)]
pub struct Splits<F: PrimeField> {
    pub lpolys: Vec<PolynomialWithZeros<F>>,
    pub rpolys: Vec<PolynomialWithZeros<F>>,
}

#[derive(Debug, Default, Clone)]
pub struct NonNatOpen<FNat: PrimeField> {
    polys: Vec<PolynomialWithZeros<FNat>>,
    splits: Option<Splits<FNat>>,
    //copolys: Vec<Box<dyn Copolynomial<F> + Send + Sync>>,
    //folded_f: Option<Arc<dyn Fn(&[F]) -> F + Sync + Send>>,
    //degree: usize,
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

        let poly_diffs = lpolys
            .par_iter()
            .zip(rpolys.par_iter())
            .map(|(l, r)| {let mut r = r.clone(); r -= l; r})
           .collect::<Vec<_>>();

        
        // let degree = 1;
        // let mut poly_extensions = Vec::with_capacity(degree);

        // let mut last_poly = &rpolys;

        // for i in 0..self.degree {
        //     poly_extensions.push(last_poly.clone());
        //     poly_extensions[i].par_iter_mut().zip(poly_diffs.par_iter()).map(|(p, d)| p.add_assign(d)).count();
        //     last_poly = poly_extensions.last().unwrap();

        //     copoly_extensions.push(last_copoly.clone());
        //     copoly_extensions[i].par_iter_mut().zip(copoly_diffs.par_iter()).map(|(p, d)| p.add_assign(d)).count();
        //     last_copoly = copoly_extensions.last().unwrap();
        // }

        // let folded = self.folded_f.as_ref().unwrap().clone();
        // let poly_ext_iter = once(&lpolys).chain(once(&rpolys)).chain(poly_extensions.par_iter());
        // let copoly_ext_iter = once(&lcopolys).chain(once(&rcopolys)).chain(copoly_extensions.par_iter());
        // let results = poly_ext_iter.zip(copoly_ext_iter).map(|(polys, eqpolys)| {
        //     let tmp = (0..polys[0].items_len()).into_par_iter().map(|i| {
        //         folded(&polys.iter().map(|p| p[i]).chain(eqpolys.iter().map(|ep| ep[i])).collect_vec())
        //     }).collect::<Vec<_>>();
        //     tmp.par_iter().sum()
        // }).collect::<Vec<F>>();

        // self.splits = Some(Splits {
        //     lpolys,
        //     rpolys,
        //     lcopolys,
        //     rcopolys,
        // });
        // UniPoly::from_evals(&results);
        todo!();

    }

    fn final_evals(&self) -> Vec<FNat>{
        self.polys.par_iter().map(|poly| poly.evals[0]).collect()
    }
}


mod tests{
    use std::os::unix::thread;

    use super::*;

    use ark_bls12_381::Fr;
    use ark_bls12_381::Fq;
    use ark_bls12_381::G1Projective;
    use ark_ff::{MontBackend};
    use ark_std::{test_rng, UniformRand};
    use rand::prelude::*;
    use liblasso::poly;
    use liblasso::utils::math::Math;
    use crate::transcript::IndexedProofTranscript;
    use liblasso::utils::test_lib::TestTranscript;

    #[test]
    fn test_nnat_open_split(){

        let mut rng  = thread_rng();

        let num_vars = 7;
        let num_polys = 10;

        let polys: Vec<PolynomialWithZeros<Fq>> = (0..num_polys)
                .map(|_| PolynomialWithZeros::rand(&mut rng, thread_rng().gen_range(0..1<<num_vars), num_vars))
                .collect();

        let point: Vec<_> = (0..num_vars)
                .map( |_| Fq::rand(&mut rng))
                .collect();

        let mut test_opener = NonNatOpen{
            polys : polys.clone(),
            splits : None,
        };

        let vals: Vec<_> = polys.clone().iter()
                .map(|p| p.evaluate(&point))
                .collect();

        (0..num_vars).map(|i| test_opener.bind(&point[i])).count();

        let final_evals = test_opener.final_evals();

        (0..num_polys).map(|i| 
            {
                assert_eq!(test_opener.polys[i].evals.len(), 1);
                assert_eq!(test_opener.polys[i].evals[0], vals[i]);
                assert_eq!(final_evals[i], vals[i]);
            })
            .count();

    }
}



