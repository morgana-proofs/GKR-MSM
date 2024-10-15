#![allow(unused_imports)]

use std::{marker::PhantomData};
use std::ops::{AddAssign, Sub, SubAssign};
use std::sync::Arc;

use ark_ff::{Field, PrimeField};
use ark_std::iterable::Iterable;

use itertools::Itertools;
use liblasso::{poly::{eq_poly::EqPolynomial, unipoly::{CompressedUniPoly, UniPoly}}};
use liblasso::poly::dense_mlpoly::DensePolynomial;
#[cfg(feature = "prof")]
use profi::{prof, prof_guard};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, once, ParallelIterator};

use crate::transcript::TranscriptSender;
use crate::{transcript::{Challenge, TranscriptReceiver}, utils::{make_gamma_pows, map_over_poly_legacy}};
use crate::copoly::{CopolyData, Copolynomial, EqPoly};
use crate::polynomial::fragmented::{FragmentedPoly, InterOp};
use crate::utils::{fix_var_bot};

use crate::protocol::protocol::{EvalClaim, MultiEvalClaim, PolynomialMapping, Protocol, ProtocolProver, ProtocolVerifier};
use crate::protocol::sumcheck::{SumcheckPolyMap, Splits, FragmentedLincomb, SumcheckPolyMapParams, SumcheckPolyMapProver, SumcheckPolyMapProof, SumcheckPolyMapVerifier, Sumcheckable,};


// pub mod prover;
// pub mod verifier;
pub mod non_native_equalizer;
pub mod n_n_sumcheck;
pub mod polynomial_with_zeros;

pub mod cleanup;

#[cfg(test)]
mod tests;
