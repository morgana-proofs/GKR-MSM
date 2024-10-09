use ark_ec::{CurveGroup, AffineRepr};
use ark_ff::{PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use merlin::Transcript;

#[derive(Debug, Clone, Copy)]
pub enum PTMode {
    Prover,
    Verifier,
}

/// Trait for combined proof and protocol transcript. Prover messages sent to this are both appended to the proof and fed to the sponge.
pub trait TProofTranscript2 : Sized {
    type PParam; // Domain separator for our instance.
    type RawProof;

    fn mode(&self) -> PTMode;

    fn _start_prover(pparam: Self::PParam) -> Self;
    /// Should fail in verifier mode.
    fn _end(self) -> Self::RawProof;
    fn _start_verifier(pparam: Self::PParam, proof: Self::RawProof) -> Self;

    fn raw_challenge(&mut self, bytesize: usize) -> Vec<u8>;
    
    fn _read_raw_msg(&mut self, bytesize: usize) -> &[u8];
    fn _write_raw_msg(&mut self, msg: &[u8]);


    fn challenge<F: PrimeField>(&mut self, bitsize: usize) -> F {
        F::from_le_bytes_mod_order(&self.raw_challenge((bitsize+7) / 8))
    }

    fn challenge_vec<F: PrimeField>(&mut self, n: usize, bitsize: usize) -> Vec<F> {
        let bytes = self.raw_challenge(n * ((bitsize + 7) / 8));
        bytes.chunks(16).map(|chunk| F::from_le_bytes_mod_order(chunk)).collect()
    }
    
    fn _read_scalars<F: PrimeField>(&mut self, size: usize) -> Vec<F> {
        let mult = F::compressed_size(&F::zero());
        self._read_raw_msg(size * mult).chunks(mult).map(|chunk| F::deserialize_compressed(chunk).unwrap()).collect()
    }

    fn _write_scalars<F: PrimeField>(&mut self, msg: &[F]) {
        let mult = F::compressed_size(&F::zero());
        let mut writer = Vec::with_capacity(msg.len() * mult);
        msg.iter().map(|x| x.serialize_compressed(&mut writer)).count();
        self._write_raw_msg(&writer);
    }

    fn _read_points<G: CurveGroup>(&mut self, size: usize) -> Vec<<G as CurveGroup>::Affine> {
        let mult = G::Affine::compressed_size(&G::Affine::generator());
        self._read_raw_msg(size * mult).chunks(mult).map(|chunk| G::Affine::deserialize_compressed(chunk).unwrap()).collect()
    }
    
    fn _write_points<G: CurveGroup>(&mut self, msg: &[impl Into<G::Affine> + Copy]) {
        let mult = G::Affine::compressed_size(&G::Affine::generator());
        let mut writer = Vec::with_capacity(msg.len() * mult);
        msg.iter().map(|x| (*x).into().serialize_compressed(&mut writer)).count();
        self._write_raw_msg(&writer);
    }
}

pub trait TProverTranscript : TProofTranscript2 {
    fn start_prover(pparam: Self::PParam) -> Self {
        Self::_start_prover(pparam)
    }

    fn write_raw_msg(&mut self, msg: &[u8]) {
        self._write_raw_msg(msg);
    }

    fn write_scalars<F: PrimeField>(&mut self, msg: &[F]) {
        self._write_scalars(msg);
    }

    fn write_points<G: CurveGroup>(&mut self, msg: &[impl Into<G::Affine> + Copy]) {
        self._write_points::<G>(msg);
    }

    fn end(self) -> Self::RawProof {
        self._end()
    }
}

pub trait TVerifierTranscript : TProofTranscript2 {
    fn start_verifier(pparam: Self::PParam, proof: Self::RawProof) -> Self {
        Self::_start_verifier(pparam, proof)
    }
    fn read_raw_msg(&mut self, bytesize: usize) -> &[u8] {
        self._read_raw_msg(bytesize)
    }
    fn read_scalars<F: PrimeField>(&mut self, size: usize) -> Vec<F> {
        self._read_scalars(size)
    }
    fn read_points<G: CurveGroup>(&mut self, size: usize) -> Vec<<G as CurveGroup>::Affine> {
        self._read_points::<G>(size)
    }
}

impl<T : TProofTranscript2> TProverTranscript for T {}
impl<T : TProofTranscript2> TVerifierTranscript for T {}

pub struct ProofTranscript2 {
    merlin_transcript: Transcript,
    proof: Vec<u8>,
    ctr: usize,
    mode: PTMode,
}

impl TProofTranscript2 for ProofTranscript2 {
    type PParam = &'static [u8];

    type RawProof = Vec<u8>;

    fn mode(&self) -> PTMode {
        self.mode
    }

    fn _start_prover(pparam: Self::PParam) -> Self {
        let merlin_transcript = Transcript::new(&pparam);
        let proof = vec![];
        Self { merlin_transcript, proof, ctr: 0, mode: PTMode::Prover }
    }

    fn _end(self) -> Self::RawProof {
        self.proof
    }

    fn _start_verifier(pparam: Self::PParam, proof: Self::RawProof) -> Self {
        let merlin_transcript = Transcript::new(&pparam);
        Self {merlin_transcript, proof, ctr: 0, mode: PTMode::Verifier}
    }

    fn raw_challenge(&mut self, bytesize: usize) -> Vec<u8> {
        let mut ret = vec![0u8; bytesize];
        self.merlin_transcript.challenge_bytes(&[], &mut ret);
        ret
    }

    fn _read_raw_msg(&mut self, bytesize: usize) -> &[u8] {
        match self.mode() {
            PTMode::Prover => panic!(),
            PTMode::Verifier => {
                assert!(self.ctr + bytesize <= self.proof.len(), "Out of bounds");
                let msg = &self.proof[self.ctr .. self.ctr + bytesize];
                self.ctr += bytesize;
                self.merlin_transcript.append_message(&[], msg);
                msg
            }
        }
    }

    fn _write_raw_msg(&mut self, msg: &[u8]) {
        match self.mode() {
            PTMode::Verifier => panic!(),
            PTMode::Prover => {
                self.merlin_transcript.append_message(&[], msg);
                self.proof.extend_from_slice(msg);
            }
        }
    }

}


#[cfg(test)]
mod tests {
    use ark_bls12_381::{G1Affine, G1Projective, g1::Config};
    use ark_ec::{CurveConfig, Group};
    use ark_std::{test_rng, UniformRand};
    use super::*;

    type Fr = <Config as CurveConfig>::ScalarField;

    #[test]
    fn transcript2_io() {
        let mut transcript = ProofTranscript2::start_prover(b"fgsdstglsp");
        let rng = &mut test_rng();
        
        let mut msg1 = vec![];
        for i in 0..1000 {
            msg1.push(Fr::rand(rng));
            msg1.push(Fr::from(i));
        }

        transcript.write_scalars(&msg1);

        let c1 : Fr = transcript.challenge(128);
        let c2 : Fr = transcript.challenge(128);

        let mut msg2 = vec![];
        for i in 0..1000 {
            msg2.push(G1Affine::rand(rng));
            msg2.push((G1Projective::generator() * Fr::from(i)).into());
        }

        transcript.write_points::<G1Projective>(&msg2);

        let c3 : Fr = transcript.challenge(128);

        let proof = transcript.end();

        let mut v_transcript = ProofTranscript2::start_verifier(b"fgsdstglsp", proof);
        assert_eq!(msg1, v_transcript.read_scalars(2000));
        assert_eq!(c1, v_transcript.challenge(128));
        assert_eq!(c2, v_transcript.challenge(128));
        assert_eq!(msg2, v_transcript.read_points::<G1Projective>(2000));
        assert_eq!(c3, v_transcript.challenge(128));
    }
}