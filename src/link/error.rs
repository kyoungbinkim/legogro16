#[derive(Clone, Debug)]
pub enum LinkError {
    InvalidIndex(usize, usize),
    VectorLongerThanExpected(usize, usize),
    VectorWithUnexpectedLength(usize, usize),
    InvalidProof,
}
