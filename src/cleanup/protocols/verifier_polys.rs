use std::{iter::{repeat, repeat_n}, marker::PhantomData};
use ark_ff::PrimeField;
use crate::utils::{eq_poly_sequence_last, eq_sum};

/// Trait for polynomials computable by the verifier. Roughly corresponds to Copoly from the previous version, though it has far less moving parts now.
pub trait VerifierPoly<F: PrimeField> {
    fn num_vars(&self) -> usize;
    fn evals(&self) -> Vec<F>; // expected to be of size num_vars
    fn evaluate(&self, pt: &[F]) -> F; 
}

/// This is equivalent to EqPolynomial from liblasso
/// We eventually will shift to this version.
pub struct EqPoly<F: PrimeField> {
    pub num_vars: usize,
    pub r: Vec<F>,
}

impl<F: PrimeField> EqPoly<F> {
    pub fn new(num_vars: usize, r: &[F]) -> Self {
        assert!(r.len() == num_vars);
        Self { num_vars, r: r.to_vec() }
    }
}

impl<F: PrimeField> VerifierPoly<F> for EqPoly<F>{
    fn num_vars(&self) -> usize {
        self.num_vars
    }

    fn evals(&self) -> Vec<F> {
        eq_poly_sequence_last(&self.r).unwrap()
    }

    fn evaluate(&self, pt: &[F]) -> F {
        assert!(pt.len() == self.num_vars);
        self.r.iter().zip(pt.iter()).fold(F::one(), |acc, (&x, &y)| acc * (F::one() - x - y + (x * y).double()))
    }
}

/// Equals 1 for values in 0..k, and 0-s otherwise.
pub struct SelectorPoly<F: PrimeField> {
    pub num_vars: usize,
    pub k: usize,
    pub _marker: PhantomData<F>,
}

impl<F: PrimeField> SelectorPoly<F> {
    pub fn new(num_vars: usize, k: usize) -> Self {
        assert!(k <= (1 << num_vars));
        Self { num_vars, k, _marker: PhantomData }
    }
}

impl<F: PrimeField> VerifierPoly<F> for SelectorPoly<F> {
    fn num_vars(&self) -> usize {
        self.num_vars
    }

    fn evals(&self) -> Vec<F> {
        repeat_n(F::one(), self.k).chain(repeat(F::zero())).take(1 << self.num_vars).collect()
    }

    fn evaluate(&self, pt: &[F]) -> F {
        assert!(pt.len() == self.num_vars);
        eq_sum(pt, self.k)
    }
}

/// Multilinearization of a product of the selector and eq-polynomial - i,e, it equals EqPoly if index is in 0..k and = 0 otherwise.
pub struct EqTruncPoly<F: PrimeField> {
    pub num_vars: usize,
    pub k: usize,
    pub r: Vec<F>,
}

impl<F: PrimeField> EqTruncPoly<F> {
    pub fn new(num_vars: usize, k: usize, r: &[F]) -> Self {
        assert!(k <= (1 << num_vars));
        assert!(r.len() == num_vars);
        Self { num_vars, k, r: r.to_vec() }
    }
}

impl<F: PrimeField> VerifierPoly<F> for EqTruncPoly<F> {
    fn num_vars(&self) -> usize {
        self.num_vars
    }

    fn evals(&self) -> Vec<F> {
        let mut ret = EqPoly::new(self.num_vars, &self.r).evals();
        for i in self.k .. (1 << self.num_vars) {
            ret[i] = F::zero()
        }
        ret
    }

    fn evaluate(&self, pt: &[F]) -> F {
        assert!(pt.len() == self.num_vars);

        let mut partial_evals = Vec::with_capacity(self.num_vars + 1);
        partial_evals.push(F::one()); // Partial evaluations correspond to eq(r_0, ..., r_{k-1}; p_0, ..., p_{k-1}).

        for i in 0..self.num_vars {
            let j = self.num_vars - i - 1;
            partial_evals.push(
                *partial_evals.last().unwrap() * (F::one() - pt[j] - self.r[j] + (self.r[j] * pt[j]).double())
            )
        }

        let mut multiplier = F::one();
        let mut acc = F::zero();
        let mut k = self.k;

        if k >= (1 << self.num_vars) {
            if k == 1 << self.num_vars {
                return partial_evals[self.num_vars];
            } else {
                panic!();
            }
        }
    
        for i in 0..self.num_vars {
            let left_bit = k >> (self.num_vars - i - 1);
    
            let _multiplier = multiplier;
            if left_bit == 1 {
                multiplier *= pt[i] * self.r[i];
                acc += _multiplier * (F::one() - pt[i]) * (F::one() - self.r[i]) * partial_evals[self.num_vars - i - 1];         
            } else {
                multiplier *= (F::one() - pt[i]) * (F::one() - self.r[i]);
            }
            k -= left_bit << (self.num_vars - i - 1);
        }
    
        acc
    }
}



#[cfg(test)]
mod tests {

    use ark_bls12_381::Fr;
    use liblasso::poly::eq_poly::EqPolynomial;
    use super::*;
    use ark_std::{UniformRand, test_rng, Zero, One};

    #[test]
    fn eq_poly_tests() {
        let rng = &mut test_rng();
        let pt : Vec<Fr> = (0..16).map(|_| Fr::rand(rng)).collect();
        let r : Vec<Fr> = (0..16).map(|_| Fr::rand(rng)).collect();

        for i in 0..17 {
            let lhs = EqPoly::new(i, &pt[..i]);
            let rhs = EqPolynomial::new(pt[..i].to_vec());
            assert!(lhs.evals() == rhs.evals());
            assert!(lhs.evaluate(&r[..i]) == rhs.evaluate(&r[..i]))
        }
    }

    #[test]
    fn selector_poly_tests() {
        let rng = &mut test_rng();
        let num_vars = 8;

        let pt : Vec<Fr> = (0..num_vars).map(|_| Fr::rand(rng)).collect();


        for k in 0 .. (1 << num_vars) + 1 {
            let lhs = SelectorPoly::new(num_vars, k).evaluate(&pt);
            let rhs = EqPoly::new(num_vars, &pt).evals().into_iter().take(k).sum::<Fr>();

            assert!(lhs == rhs);
        }
    }

    #[test]
    fn truncated_eq_tests() {
        let rng = &mut test_rng();
        let num_vars = 8;
        
        let u : Vec<Fr> = (0..num_vars).map(|_| Fr::rand(rng)).collect();
        let v : Vec<Fr> = (0..num_vars).map(|_| Fr::rand(rng)).collect();

        let eq_u = EqPoly::new(num_vars, &u).evals();
        let eq_v = EqPoly::new(num_vars, &v).evals();

        for k in 0 .. (1 << num_vars) + 1 {
            let lhs = EqTruncPoly::new(num_vars, k, &u).evaluate(&v);
            let rhs = {let mut acc = Fr::zero(); for i in 0..k {acc += eq_u[i] * eq_v[i]}; acc};
            assert!(lhs == rhs);
        }

    }
}