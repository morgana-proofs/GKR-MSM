use std::marker::PhantomData;
use std::sync::Arc;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use liblasso::utils::transcript::ProofTranscript;

#[derive(Clone)]
pub struct PolynomialMapping<F: PrimeField> {
    pub exec: Arc<dyn Fn(&[F]) -> Vec<F> + Send + Sync>,
    pub degree: usize,
    pub num_i: usize,
    pub num_o: usize,
}

// Claim
pub struct Claim<F: PrimeField> {
    point: Vec<F>,
    value: F,
}
pub enum Either<T1, T2>{
    A(T1),
    B(T2),
}


pub trait Protocol<F: PrimeField> {

    type Prover : ProtocolProver<
        F,
        ClaimsToReduce = Self::ClaimsToReduce,
        ClaimsNew = Self::ClaimsNew,
        Proof = Self::Proof,
        Params = Self::Params,
        Trace = Self::Trace,
    >;

    type Verifier : ProtocolVerifier<
        F,
        ClaimsToReduce = Self::ClaimsToReduce,
        ClaimsNew = Self::ClaimsNew,
        Proof = Self::Proof,
        Params = Self::Params,
    >;

    type ClaimsToReduce;
    type ClaimsNew;

    type WitnessInput;
    type Trace;
    type WitnessOutput;
    type Proof;
    type Params;

    fn witness(args: Self::WitnessInput, params: &Self::Params) -> (Self::Trace, Self::WitnessOutput);
}


pub trait ProtocolProver<F: PrimeField> {

    type ClaimsToReduce;
    type ClaimsNew;
    type Proof;
    type Params;
    type Trace;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        args: Self::Trace,
        params: &Self::Params,
    ) -> Self;


    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
                                       ->
                                       Option<(Self::ClaimsNew, Self::Proof)>;
}

pub trait ProtocolVerifier<F: PrimeField> {
    type Params;
    type ClaimsToReduce;
    type ClaimsNew;
    type Proof;

    fn start(
        claims_to_reduce: Self::ClaimsToReduce,
        proof: Self::Proof,
        params: &Self::Params,
    ) -> Self;


    fn round<T: TranscriptReceiver<F>>(&mut self, challenge: Challenge<F>, transcript: &mut T)
                                       ->
                                       Option<Self::ClaimsNew>;
}

pub trait TranscriptReceiver<F: PrimeField> {
    fn append_scalar(&mut self, label: &'static [u8], scalar: &F);
    fn append_scalars(&mut self, label: &'static [u8], scalars: &[F]);
}

pub trait TranscriptSender<F: PrimeField> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Challenge<F>;
}

#[derive(Clone, Copy)]
pub struct Challenge<X> {
    pub value: X,
    pub round_id: usize,
}

/// A very thin wrapper over normal proof transcript from liblasso,
/// counting amount of challenges. Protocols under parallel composition
/// should check that their index monotonically increases.
pub struct IndexedProofTranscript<G : CurveGroup, P: ProofTranscript<G>> {
    global_round: usize,
    pub transcript: P,
    _marker: PhantomData<G>,
}

impl<G: CurveGroup, P: ProofTranscript<G>> IndexedProofTranscript<G, P> {
    pub fn new(transcript: P) -> Self {
        Self { global_round: 0, transcript, _marker: PhantomData }
    }

    pub fn release(self) -> P {
        self.transcript
    }

    pub fn current_global_round(&self) -> usize {
        self.global_round
    }
}

impl<G: CurveGroup, P: ProofTranscript<G>> TranscriptReceiver<G::ScalarField> for IndexedProofTranscript<G, P> {
    fn append_scalar(&mut self, label: &'static [u8], scalar: &<G>::ScalarField) {
        self.transcript.append_scalar(label, scalar)
    }
    fn append_scalars(&mut self, label: &'static [u8], scalars: &[<G>::ScalarField]) {
        self.transcript.append_scalars(label, scalars)
    }
}

impl<G: CurveGroup, P: ProofTranscript<G>> TranscriptSender<G::ScalarField> for IndexedProofTranscript<G, P> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Challenge<<G>::ScalarField> {
        let ret = Challenge {value: self.transcript.challenge_scalar(label), round_id : self.global_round};
        self.global_round += 1;
        ret
    }
}

