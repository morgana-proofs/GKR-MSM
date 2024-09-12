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

pub struct Splits<F: PrimeField> {
    pub lpolys: Vec<PolynomialWithZeros<F>>,
    pub rpolys: Vec<PolynomialWithZeros<F>>,
}

pub struct NonNatEqualizer<FNat: PrimeField> {
    polys: Vec<PolynomialWithZeros<FNat>>,
    splits: Option<Splits<FNat>>,
    //copolys: Vec<Box<dyn Copolynomial<F> + Send + Sync>>,
    //folded_f: Option<Arc<dyn Fn(&[F]) -> F + Sync + Send>>,
    //degree: usize,
}

impl<FNat: PrimeField> Sumcheckable<FNat> for NonNatEqualizer<FNat>{
    fn bind(&mut self, f: &FNat){
        todo!()
    }

    fn split(&mut self) {
        unimplemented!()
    }
    fn unipoly(&mut self) -> UniPoly<FNat>{
        // self.split();
        // let Splits { lpolys, rpolys } = self.splits.take().unwrap();

        // let poly_diffs = lpolys
        //     .par_iter()
        //     .zip(rpolys.par_iter())
        //     .map(|(l, r)| {let mut r = r.clone(); r -= l; r})
        //     .collect::<Vec<_>>();

        // let copoly_diffs = lcopolys
        //     .par_iter()
        //     .zip(rcopolys.par_iter())
        //     .map(|(l, r)| {let mut r = r.clone(); r -= l; r})
        //     .collect::<Vec<_>>();

        // let mut poly_extensions = Vec::with_capacity(self.degree);

        // let mut copoly_extensions = Vec::with_capacity(self.degree);

        // let mut last_poly = &rpolys;
        // let mut last_copoly = &rcopolys;

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
        todo!()
    }
}


mod tests{
    use super::*;

    use ark_bls12_381::Fr;
    use ark_bls12_381::Fq;
    use ark_bls12_381::G1Projective;
    use ark_ff::{MontBackend};
    use ark_std::{test_rng, UniformRand};
    use ark_std::rand::Rng;
    use liblasso::poly;
    use liblasso::utils::math::Math;
    use crate::transcript::IndexedProofTranscript;
    use liblasso::utils::test_lib::TestTranscript;

    #[test]
    fn test_polynomial_new(){

        let mut rng  = test_rng();
        let num_limbs = 3;
        let limb_len = roundup_to_pow2( Fq::MODULUS_BIT_SIZE  as usize / num_limbs);

        let poly_size = 6u64;
        let log_poly_size = 3u64;

        let poly1: Vec<_> =  (0..poly_size).map(|i| Fq::from(i)).collect();
        let poly2: Vec<_> =  (0..poly_size).map(|i| Fq::from(i+1)).collect();
        // let r_bits = big_num_to_bits_F(r);
        let point: Vec<_> = (0..log_poly_size).map(|i| Fq::from(2*i + 1)).collect();

        let p1 = PolynomialWithZeros::new(&poly1);
        let value1 = p1.evaluate(&point);
        
        let p2 = PolynomialWithZeros::new(&poly2);
        let value2 = p2.evaluate(&point);

        assert_eq!(p1.len, poly_size as usize);
        assert_eq!(p1.log_len, log_poly_size as usize);
        assert_eq!(value1 +  Fq::from(78), Fq::from(0));
        assert_eq!(value2 +  Fq::from(78)+  Fq::from(15), Fq::from(1));

    }
}



