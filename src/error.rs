use crate::link::error::LinkError;
use ark_relations::r1cs::SynthesisError;

#[derive(Clone, Debug)]
pub enum Error {
    SynthesisError(SynthesisError),
    LinkError(LinkError),
    VectorLongerThanExpected(usize, usize),
    InvalidProof,
    InvalidLinkCommitment,
    InvalidProofCommitment,
}

impl From<SynthesisError> for Error {
    fn from(e: SynthesisError) -> Self {
        Self::SynthesisError(e)
    }
}

impl From<LinkError> for Error {
    fn from(e: LinkError) -> Self {
        Self::LinkError(e)
    }
}
