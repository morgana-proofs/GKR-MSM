// This describes a greatly simplified (sub)protocol API. It is stateless, i.e. it does not support feeding challenges one by one,
// which means that there is no simple parallel composition. However, it is much more ergonomic.

// The contract is the same: one MUST ensure that all the polynomials involved in a protocol are committed before its start (and, thus, are contained in proof transcript object)

// Witness generator is removed from this trait, and should be constructed for each protocol separately, on an ad-hoc basis - as our previous witness generator API did not cover some important cases.
// Witness for a protocol can be given through ProverInput type (and what remains of it can be returned through ProverOutput if desired).

use super::proof_transcript::{TProverTranscript, TVerifierTranscript};

/// Expected to contain the configuration of the protocol.
pub trait Protocol2 {
    /// Arbitrary advice to prover.
    type ProverInput;
    /// Arbitrary data returned by prover in addition to output claims.
    type ProverOutput;

    type ClaimsBefore; // Input and output claims. Names changed to before and after to prevent confusion, because "before" claims are actually claims about the output of the protocol.
    type ClaimsAfter;
    
    fn prove<PT: TProverTranscript>(&self, transcript: &mut PT, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput);
    fn verify<PT: TVerifierTranscript>(&self, transcript: &mut PT, claims: Self::ClaimsBefore) -> Self::ClaimsAfter;
}