use ark_ec::PairingEngine;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::{
    cfg_into_iter, cfg_iter,
    fmt::Debug,
    io::{Read, Write},
    vec::Vec,
};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::aggregation::error::AggregationError;
use crate::aggregation::key::{PreparedVKey, VKey, WKey};
use crate::aggregation::utils::{pairing_product, pairing_product_with_g2_prepared};

/// Commits to either a single vector of group G1 elements or 2 vectors, 1 of group G1 and 1 of group G2 elements.
/// Both commitment outputs a pair of $F_q^k$ element.
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug, PartialEq)]
pub struct PairCommitment<E: PairingEngine> {
    pub t: E::Fqk,
    pub u: E::Fqk,
}

impl<E: PairingEngine> PairCommitment<E> {
    /// Commits to a single vector of group G1 elements.
    pub fn single(vkey: &VKey<E>, a_vec: &[E::G1Affine]) -> Result<Self, AggregationError> {
        vkey.ensure_sufficient_len(a_vec)?;
        let t = pairing_product::<E>(a_vec, &vkey.a);
        let u = pairing_product::<E>(a_vec, &vkey.b);
        Ok(Self { t, u })
    }

    pub fn single_with_prepared_key(
        vkey: &PreparedVKey<E>,
        a_vec: &[E::G1Affine],
    ) -> Result<Self, AggregationError> {
        vkey.ensure_sufficient_len(a_vec)?;
        let t = pairing_product_with_g2_prepared::<E>(a_vec, vkey.a.clone());
        let u = pairing_product_with_g2_prepared::<E>(a_vec, vkey.b.clone());
        Ok(Self { t, u })
    }

    /// Commits to 2 vector, 1 of group G1 elements and 1 of group G2 elements.
    pub fn double(
        vkey: &VKey<E>,
        wkey: &WKey<E>,
        a: &[E::G1Affine],
        b: &[E::G2Affine],
    ) -> Result<Self, AggregationError> {
        let b_prep = cfg_iter!(b)
            .map(|e| E::G2Prepared::from(*e))
            .collect::<Vec<_>>();
        let pairs1: Vec<(E::G1Prepared, E::G2Prepared)> = cfg_iter!(a)
            .map(|e| E::G1Prepared::from(*e))
            .zip(cfg_iter!(vkey.a).map(|e| E::G2Prepared::from(*e)))
            .collect::<Vec<_>>();
        let pairs2: Vec<(E::G1Prepared, E::G2Prepared)> = cfg_iter!(wkey.a)
            .map(|e| E::G1Prepared::from(*e))
            .zip(cfg_into_iter!(b_prep.clone()))
            .collect::<Vec<_>>();
        let pairs3: Vec<(E::G1Prepared, E::G2Prepared)> = cfg_iter!(a)
            .map(|e| E::G1Prepared::from(*e))
            .zip(cfg_iter!(vkey.b).map(|e| E::G2Prepared::from(*e)))
            .collect::<Vec<_>>();
        let pairs4: Vec<(E::G1Prepared, E::G2Prepared)> = cfg_iter!(wkey.b)
            .map(|e| E::G1Prepared::from(*e))
            .zip(cfg_into_iter!(b_prep))
            .collect::<Vec<_>>();

        Ok(Self::from_pairs(pairs1, pairs2, pairs3, pairs4))
    }

    pub fn double_with_prepared_key_and_message(
        vkey: &PreparedVKey<E>,
        wkey: &WKey<E>,
        a: &[E::G1Affine],
        b: Vec<E::G2Prepared>,
    ) -> Result<Self, AggregationError> {
        let pairs1: Vec<(E::G1Prepared, E::G2Prepared)> = cfg_iter!(a)
            .map(|e| E::G1Prepared::from(*e))
            .zip(cfg_into_iter!(vkey.a.clone()))
            .collect::<Vec<_>>();
        let pairs2: Vec<(E::G1Prepared, E::G2Prepared)> = cfg_iter!(wkey.a)
            .map(|e| E::G1Prepared::from(*e))
            .zip(cfg_into_iter!(b.clone()))
            .collect::<Vec<_>>();
        let pairs3: Vec<(E::G1Prepared, E::G2Prepared)> = cfg_iter!(a)
            .map(|e| E::G1Prepared::from(*e))
            .zip(cfg_into_iter!(vkey.b.clone()))
            .collect::<Vec<_>>();
        let pairs4: Vec<(E::G1Prepared, E::G2Prepared)> = cfg_iter!(wkey.b)
            .map(|e| E::G1Prepared::from(*e))
            .zip(cfg_into_iter!(b))
            .collect::<Vec<_>>();
        Ok(Self::from_pairs(pairs1, pairs2, pairs3, pairs4))
    }

    fn from_pairs(
        pairs1: Vec<(E::G1Prepared, E::G2Prepared)>,
        pairs2: Vec<(E::G1Prepared, E::G2Prepared)>,
        pairs3: Vec<(E::G1Prepared, E::G2Prepared)>,
        pairs4: Vec<(E::G1Prepared, E::G2Prepared)>,
    ) -> Self {
        // (A * v)
        let t1 = E::product_of_pairings(pairs1.iter());
        // (w * B)
        let t2 = E::product_of_pairings(pairs2.iter());
        let u1 = E::product_of_pairings(pairs3.iter());
        let u2 = E::product_of_pairings(pairs4.iter());

        Self {
            t: t1 * t2,
            u: u1 * u2,
        }
    }
}
