// a new, highly simplified protocol API

pub mod proof_transcript;
pub mod protocol2;
pub mod protocols;
// pub mod unipoly; // need to eventually replace liblasso unipoly by our own type (possibly even trait which support some sort of compression given a hint, to accomodate different bases / Gruen's trick? postponed for now)