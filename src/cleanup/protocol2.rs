// This describes a greatly simplified (sub)protocol API. It is stateless, i.e. it does not support feeding challenges one by one,
// which means that there is no simple parallel composition. However, it is much more ergonomic.

// The contract is the same: one MUST ensure that all the polynomials involved in a protocol are committed before its start (and, thus, are contained in proof transcript object)

// Witness generator is removed from this trait, and should be constructed for each protocol separately, on an ad-hoc basis - as our previous witness generator API did not cover some important cases.

use super::proof_transcript::{TProverTranscript, TVerifierTranscript};

/// Expected to contain the configuration of the protocol.
pub trait Protocol2 {
    /// Arbitrary advice to prover.
    type Advice;

    type ClaimsBefore; // Input and output claims. Names changed do before and after to prevent confusion, because "before" claims are actually claims about the output of the protocol.
    type ClaimsAfter;
    
    fn prove<PT: TProverTranscript>(&self, pt: &mut PT, advice: Self::Advice, claims: Self::ClaimsBefore) -> Self::ClaimsAfter;
    fn verify<PT: TVerifierTranscript>(&self, pt: &mut PT, claims: Self::ClaimsBefore) -> Self::ClaimsAfter;
}