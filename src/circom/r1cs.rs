use ark_ec::PairingEngine;
use ark_std::{marker::PhantomData, vec::Vec};

/// A linear combination
pub type LC<E> = Vec<(usize, <E as PairingEngine>::Fr)>;
/// A single constraint. Comprised of 3 linear combinations
pub type Constraint<E> = (LC<E>, LC<E>, LC<E>);

/// Only the following curves are supported.
#[derive(Clone, Debug, PartialEq)]
pub enum Curve {
    Bn128,
    Bls12_381,
}

/// Result of the parsed R1CS file.
#[derive(Clone, Debug)]
pub struct R1CS<E: PairingEngine> {
    pub curve: Curve,
    /// Total number of wires in the circuit. Includes private and public inputs, outputs as well as
    /// intermediate wires and the wire corresponding to the always present input "1".
    pub num_variables: usize,
    /// Total number of public values in the circuit. Includes public inputs and outputs and the always
    /// present input "1".
    pub num_public: usize,
    /// Total number of private values in the circuit. Includes the private input as well as the intermediate
    /// wires. Should always be `num_variables - num_public`
    pub num_aux: usize,
    pub constraints: Vec<Constraint<E>>,
    /// The indices of the vector specify the wire index and the value specifies the label index
    pub wire_to_label_mapping: Vec<usize>,
}

#[derive(Clone, Debug)]
pub struct R1CSFile<E: PairingEngine> {
    /// R1CS file version. This is different from the Circom compiler version.
    pub version: u32,
    pub header: Header<E>,
    pub constraints: Vec<Constraint<E>>,
    pub wire_mapping: Vec<u64>,
}

/// Header section of R1CS file
#[derive(Clone, Debug)]
pub struct Header<E: PairingEngine> {
    /// Size in bytes of a field element
    pub field_size: u32,
    /// Order of the largest subgroup of the curves
    pub subgroup_order: Vec<u8>,
    /// The curve used when compiling the circuit. Specified with flag `-p` with Circom.
    pub curve: Curve,
    pub n_wires: u32,
    pub n_pub_out: u32,
    pub n_pub_in: u32,
    pub n_prv_in: u32,
    pub n_labels: u64,
    pub n_constraints: u32,
    pub phantom: PhantomData<E>,
}

impl<E: PairingEngine> From<R1CSFile<E>> for R1CS<E> {
    fn from(file: R1CSFile<E>) -> Self {
        let num_inputs = (1 + file.header.n_pub_in + file.header.n_pub_out) as usize;
        let num_variables = file.header.n_wires as usize;
        let num_aux = num_variables - num_inputs;
        R1CS {
            curve: file.header.curve,
            num_aux,
            num_public: num_inputs,
            num_variables,
            constraints: file.constraints,
            wire_to_label_mapping: file.wire_mapping.iter().map(|e| *e as usize).collect(),
        }
    }
}
