use std::marker::PhantomData;

use ark_serialize::CanonicalSerialize;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use merlin::Transcript;

pub trait TranscriptReceiver<F: PrimeField> {
    fn append_scalar(&mut self, label: &'static [u8], scalar: &F);
    fn append_scalars(&mut self, label: &'static [u8], scalars: &[F]);
    fn append_message(&mut self, label: &'static [u8], msg: &[u8]);
    fn append_point<G: CurveGroup>(&mut self, label: &'static[u8], point: impl Into<G::Affine>);
}

pub trait TranscriptSender<F: PrimeField> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Challenge<F>;
}

#[derive(Clone, Copy)]
pub struct Challenge<X> {
    pub value: X,
}

/// A very thin wrapper over normal proof transcript from liblasso,
/// counting amount of challenges. Protocols under parallel composition
/// should check that their index monotonically increases.
pub struct IndexedProofTranscript<G : CurveGroup, P: liblasso::utils::transcript::ProofTranscript<G>> {
    global_round: usize,
    pub transcript: P,
    _marker: PhantomData<G>,
}

impl<G: CurveGroup, P: liblasso::utils::transcript::ProofTranscript<G>> IndexedProofTranscript<G, P> {
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

impl<G: CurveGroup, P: liblasso::utils::transcript::ProofTranscript<G>> TranscriptReceiver<G::ScalarField> for IndexedProofTranscript<G, P> {
    fn append_scalar(&mut self, label: &'static [u8], scalar: &<G>::ScalarField) {
        self.transcript.append_scalar(label, scalar)
    }
    fn append_scalars(&mut self, label: &'static [u8], scalars: &[<G>::ScalarField]) {
        self.transcript.append_scalars(label, scalars)
    }
    fn append_message(&mut self, label: &'static [u8], msg: &[u8]) {
        todo!()
    }
    fn append_point<G2: CurveGroup>(&mut self, label: &'static[u8], point: impl Into<G2::Affine>) {
        todo!()
    }
}

impl<G: CurveGroup, P: liblasso::utils::transcript::ProofTranscript<G>> TranscriptSender<G::ScalarField> for IndexedProofTranscript<G, P> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Challenge<<G>::ScalarField> {
        let ret = Challenge {value: self.transcript.challenge_scalar(label)};
        self.global_round += 1;
        ret
    }
}

impl<F: PrimeField> TranscriptReceiver<F> for Transcript {
    fn append_scalar(&mut self, _: &'static [u8], scalar: &F) {
        let mut buf = vec![];
        scalar.serialize_compressed(&mut buf).unwrap();
        self.append_message(b"", &buf);
    }

    fn append_scalars(&mut self, _: &'static [u8], scalars: &[F]) {
        //self.append_message(label, b"begin_append_vector");
        for item in scalars.iter() {
            Self::append_scalar(self, b"", item);
        }
        //self.append_message(label, b"end_append_vector");
      }
    
    fn append_message(&mut self, label: &'static [u8], msg: &[u8]) {
        self.append_message(b"", msg)
    }

    fn append_point<G: CurveGroup>(&mut self, label: &'static[u8], point: impl Into<G::Affine>) {
        let mut buf : Vec<u8> = vec![];
        point.into().serialize_compressed(&mut buf).unwrap();
        self.append_message(label, &buf);
    }
}

impl<F: PrimeField> TranscriptSender<F> for Transcript {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Challenge<F> {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        Challenge{value: F::from_le_bytes_mod_order(&buf)}
    }
}