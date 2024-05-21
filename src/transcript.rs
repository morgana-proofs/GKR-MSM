use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use merlin::Transcript;

use crate::protocol::{TranscriptReceiver, TranscriptSender};

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

    fn append_point<G: CurveGroup>(&mut self, label: &'static[u8], point: G) {
        let mut buf : Vec<u8> = vec![];
        point.serialize_compressed(&mut buf).unwrap();
        self.append_message(label, &buf);
    }
}

impl<F: PrimeField> TranscriptSender<F> for Transcript {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> crate::protocol::Challenge<F> {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        crate::protocol::Challenge{value: F::from_le_bytes_mod_order(&buf)}
    }
}