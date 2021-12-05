//! An implementation of the [`Groth16`] zkSNARK.
//!
//! [`Groth16`]: https://eprint.iacr.org/2016/260.pdf
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(unused, future_incompatible, nonstandard_style, rust_2018_idioms)]
#![allow(clippy::many_single_char_names, clippy::op_ref)]
#![forbid(unsafe_code)]

// #[macro_use]
// extern crate bench_utils;

#[cfg(feature = "r1cs")]
#[macro_use]
extern crate derivative;

/// Reduce an R1CS instance to a *Quadratic Arithmetic Program* instance.
pub(crate) mod r1cs_to_qap;

/// Data structures used by the prover, verifier, and generator.
pub mod data_structures;

/// Generate public parameters for the Groth16 zkSNARK construction.
pub mod generator;

/// Create proofs for the Groth16 zkSNARK construction.
pub mod prover;

/// Verify proofs for the Groth16 zkSNARK construction.
pub mod verifier;

pub mod link;

/// Generate public parameters for the LegoGroth16 zkSNARK construction.
pub mod generator_new;
pub mod prover_new;
pub mod verifier_new;

/// Constraints for the Groth16 verifier.
// Cannot yet create a LegoGroth16 gadget (for recursive proof) so commenting it out.
// #[cfg(feature = "r1cs")]
// pub mod constraints;

#[cfg(test)]
mod test;

#[cfg(test)]
mod test_new;

pub use self::data_structures::*;
pub use self::{generator::*, prover::*, verifier::*};

use ark_std::vec::Vec;
