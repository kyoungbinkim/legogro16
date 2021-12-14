//! zkSNARK for Linear Subspaces as defined in appendix D of the paper.
//! Use to prove knowledge of openings of multiple Pedersen commitments. Can also prove knowledge
//! and equality of committed values in multiple commitments. Note that this SNARK requires a trusted
//! setup as the key generation creates a trapdoor.

use crate::link::matrix::*;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{bytes::ToBytes, One, UniformRand};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::io::{Read, Result as IoResult, Write};
use ark_std::marker::PhantomData;
use ark_std::ops::Neg;
use ark_std::rand::Rng;
use ark_std::vec;
use ark_std::vec::Vec;

/// Public params
#[derive(Clone, Default, PartialEq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PP<
    G1: Clone + ToBytes + Default + CanonicalSerialize + CanonicalDeserialize,
    G2: Clone + ToBytes + Default + CanonicalSerialize + CanonicalDeserialize,
> {
    pub l: usize, // # of rows
    pub t: usize, // # of cols
    pub g1: G1,
    pub g2: G2,
}

impl<
        G1: Clone + ToBytes + Default + CanonicalSerialize + CanonicalDeserialize,
        G2: Clone + ToBytes + Default + CanonicalSerialize + CanonicalDeserialize,
    > PP<G1, G2>
{
    pub fn new(l: usize, t: usize, g1: G1, g2: G2) -> PP<G1, G2> {
        PP { l, t, g1, g2 }
    }
}

impl<
        G1: Clone + ToBytes + Default + CanonicalSerialize + CanonicalDeserialize,
        G2: Clone + ToBytes + Default + CanonicalSerialize + CanonicalDeserialize,
    > ToBytes for PP<G1, G2>
{
    fn write<W: Write>(&self, _: W) -> IoResult<()> {
        unimplemented!();
    }
}

/// Evaluation key
#[derive(Clone, Default, PartialEq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EK<G1: Clone + ToBytes + Default + CanonicalSerialize + CanonicalDeserialize> {
    pub p: Vec<G1>,
}

impl<G1: Clone + ToBytes + Default + CanonicalSerialize + CanonicalDeserialize> ToBytes for EK<G1> {
    fn write<W: Write>(&self, _: W) -> IoResult<()> {
        unimplemented!();
    }
}

/// Verification key
#[derive(Clone, Default, PartialEq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct VK<G2: Clone + ToBytes + Default + CanonicalSerialize + CanonicalDeserialize> {
    pub c: Vec<G2>,
    pub a: G2,
}

impl<G2: Clone + ToBytes + Default + CanonicalSerialize + CanonicalDeserialize> ToBytes for VK<G2> {
    fn write<W: Write>(&self, _: W) -> IoResult<()> {
        unimplemented!();
    }
}

pub trait SubspaceSnark {
    type KMtx;
    type InVec;
    type OutVec;

    type PP;

    type EK;
    type VK;

    type Proof;

    fn keygen<R: Rng>(rng: &mut R, pp: &Self::PP, m: Self::KMtx) -> (Self::EK, Self::VK);
    fn prove(pp: &Self::PP, ek: &Self::EK, x: &[Self::InVec]) -> Self::Proof;
    fn verify(pp: &Self::PP, vk: &Self::VK, y: &[Self::OutVec], pi: &Self::Proof) -> bool;
}

pub struct PESubspaceSnark<PE: PairingEngine> {
    pairing_engine_type: PhantomData<PE>,
}

// NB: Now the system is for y = Mx
impl<PE: PairingEngine> SubspaceSnark for PESubspaceSnark<PE> {
    type KMtx = SparseMatrix<PE::G1Affine>;
    type InVec = PE::Fr;
    type OutVec = PE::G1Affine;

    type PP = PP<PE::G1Affine, PE::G2Affine>;

    type EK = EK<PE::G1Affine>;
    type VK = VK<PE::G2Affine>;

    type Proof = PE::G1Affine;

    /// Matrix should be such that a column will have more than 1 non-zero item only if those values
    /// are equal. Eg for matrix below, h2 and h3 commit to same value
    /// h1, 0, 0, 0
    /// 0, h2, 0, 0
    /// 0, h3, h4, 0
    fn keygen<R: Rng>(rng: &mut R, pp: &Self::PP, m: Self::KMtx) -> (Self::EK, Self::VK) {
        // `k` is the trapdoor
        let mut k: Vec<PE::Fr> = Vec::with_capacity(pp.l);
        for _ in 0..pp.l {
            k.push(PE::Fr::rand(rng));
        }

        let a = PE::Fr::rand(rng);

        let p = SparseLinAlgebra::<PE>::sparse_vector_matrix_mult(&k, &m);

        let c = scale_vector::<PE>(&a, &k);
        let ek = EK::<PE::G1Affine> { p };
        let vk = VK::<PE::G2Affine> {
            c: multiples_of_g::<PE::G2Affine>(&pp.g2, &c),
            a: pp.g2.mul(a).into_affine(),
        };
        (ek, vk)
    }

    fn prove(pp: &Self::PP, ek: &Self::EK, w: &[Self::InVec]) -> Self::Proof {
        assert_eq!(pp.t, w.len());
        inner_product::<PE>(w, &ek.p)
    }

    fn verify(pp: &Self::PP, vk: &Self::VK, x: &[Self::OutVec], pi: &Self::Proof) -> bool {
        assert_eq!(pp.l, x.len());

        let mut pairs = vec![];
        for i in 0..x.len() {
            pairs.push((PE::G1Prepared::from(x[i]), PE::G2Prepared::from(vk.c[i])));
        }
        pairs.push((PE::G1Prepared::from(*pi), PE::G2Prepared::from(vk.a.neg())));
        PE::Fqk::one() == PE::product_of_pairings(pairs.iter())
    }
}
