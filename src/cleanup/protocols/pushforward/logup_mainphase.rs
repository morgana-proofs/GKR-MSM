// We use GKR-logup in a following fashion:

// There is a collection of pairs of polynomials, treated as numerators and denominators. Different pairs might have different logsizes.
// We then do the following two processes
// WHILE logsize > 0:
//     WHILE there exists a unique pair with max logsize:
//         do normal bintree GKR
//     WHILE there are two pairs with max logsize:
//         merge them

// This process is optimal in terms of verifier rounds, but it spits out different claims for different polynomials.
// We circumvent it by doing a first phase synchronously (which is application-specific and needs to be combined with other protocols, anyway).
// I.e. this protocol will spit out different claims, but the separate first layer will reduce these claims to openings in somewhat related points.

// Most annoying part of this is a witness generator. Currently, we will just do it for dense polynomials (but if this becomes a hotspot and we will need to
// to move to padded ones, the pain will be immense).

use std::marker::PhantomData;

use ark_ff::PrimeField;
use hashcaster::ptr_utils::{AsSharedMUMutPtr, UninitArr, UnsafeIndexRawMut};
use itertools::Itertools;
use rayon::iter::IntoParallelIterator;

use crate::cleanup::{proof_transcript::TProofTranscript2, protocol2::Protocol2, protocols::sumcheck::{PointClaim}};
use crate::cleanup::utils::algfn::{AlgFn, AlgFnSO};


#[derive(Debug, Clone, Copy)]
pub struct LogupLayerFn<F: PrimeField> {
    _marker: PhantomData<F>,
}

impl<F: PrimeField> AlgFn<F> for LogupLayerFn<F>{
    fn exec(&self, args: &impl std::ops::Index<usize, Output = F>) -> impl Iterator<Item = F> {
        [
            args[0] * args[3] + args[1] * args[2], // ad + bc
            args[1] * args[3]                      // bd
        ].into_iter()
    }

    fn deg(&self) -> usize {
        2
    }

    fn n_ins(&self) -> usize {
        4
    }

    fn n_outs(&self) -> usize {
        2
    }
}




#[derive(Clone)]
pub struct LogupMainphaseProtocol<F: PrimeField> {
    pub logsizes: Vec<usize>,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> LogupMainphaseProtocol<F> {
    pub fn new(logsizes: Vec<usize>) -> Self {
        assert!(logsizes.len() > 0);
        for i in 0 .. logsizes.len() - 1 {
            assert!(logsizes[i] >= logsizes[i+1], "logsizes must be non-increasing")
        }
        Self { logsizes, _marker: PhantomData }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct LogupClaim<F: PrimeField> {
    pub numerator: F,
    pub denominator: F,
}

#[derive(Clone, Debug)]
pub struct MultipointClaim<F: PrimeField> {
    pub points: Vec<Vec<F>>,
    pub evs: Vec<F>,
    pub point_indices: Vec<usize>,
}

impl<F: PrimeField, PT: TProofTranscript2> Protocol2<PT> for LogupMainphaseProtocol<F> {
    type ProverInput = Vec<[Vec<F>; 2]>;

    type ProverOutput = ();

    type ClaimsBefore = LogupClaim<F>;

    type ClaimsAfter = Vec<PointClaim<F>>; // In reality, some of these opening points might coincide, but not in our case + we don't care for now.

    fn prove(&self, transcript: &mut PT, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        // advice.iter().zip_eq(self.logsizes.iter()).map(|(fraction_arr, logsize)| assert!(fraction_arr[0].len() == 1 << logsize && fraction_arr[1].len() == 1 << logsize)).count();

        // let mut advice = advice;
        // let mut intermediate_layers : Vec<[Vec<F>; 2]> = vec![];
        
        // let mut logsizes = self.logsizes.clone();

        // let mut advice_idx = 0;

        // while advice_idx < self.logsizes.len() {
        //     let next_logsize = *logsizes.get(advice_idx + 1).unwrap_or(0);
        //     let curr_logsize = &mut logsizes[advice_idx];

        //     if *curr_logsize > next_logsize {
        //         *curr_logsize -= 1;
        //         // dispatch intermediate layer with split
        //     } else {
        //         advice_idx += 1;
        //         // dispatch intermediate layer w/o split
        //     }
        // }

        todo!();
        
    }

    fn verify(&self, transcript: &mut PT, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        todo!()
    }
}