pub mod circuit;
pub mod error;
pub mod r1cs;
#[cfg(feature = "std")]
pub mod r1cs_reader;
#[cfg(test)]
mod tests;
pub mod wasm;
pub mod witness;

// BN128 curve's largest subgroup order
pub const BN128_ORDER: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";
// BLS12-381 curve's largest subgroup order
pub const BLS12_381_ORDER: &str =
    "52435875175126190479447740508185965837690552500527637822603658699938581184513";

pub use circuit::CircomCircuit;
pub use error::CircomError;
pub use r1cs::R1CS;
pub use witness::WitnessCalculator;
