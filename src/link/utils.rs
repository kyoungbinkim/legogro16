//! Utils for matrix and vector operations

use ark_ec::msm::{FixedBaseMSM, VariableBaseMSM};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{PrimeField, Zero};
use ark_std::cfg_iter;
use ark_std::marker::PhantomData;
use ark_std::ops::{AddAssign, Mul};
use ark_std::vec;
use ark_std::vec::Vec;

use crate::link::error::LinkError;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// CoeffPos: A struct to help build sparse matrices.
#[derive(Clone, Debug)]
pub struct CoeffPos<T> {
    val: T,
    pos: usize,
}

// a column is a vector of CoeffPos-s
type Col<T> = Vec<CoeffPos<T>>;

/* TODO: One could consider a cache-friendlier implementation for the 2-row case*/

/// Column-Major Sparse Matrix
#[derive(Clone, Debug)]
pub struct SparseMatrix<T> {
    cols: Vec<Col<T>>, // a vector of columns
    pub nr: usize,     // no. of rows
    pub nc: usize,     // no. of columns
}

impl<T: Copy> SparseMatrix<T> {
    // NB: Given column by column
    pub fn new(nr: usize, nc: usize) -> SparseMatrix<T> {
        SparseMatrix {
            cols: vec![vec![]; nc],
            nr,
            nc,
        }
    }

    /// Insert value `v` in the column index `c` at row index `r`
    pub fn insert_val(&mut self, r: usize, c: usize, v: T) -> Result<(), LinkError> {
        if self.cols.len() < c {
            return Err(LinkError::InvalidIndex(c, self.cols.len()));
        }
        let coeff_pos = CoeffPos { pos: r, val: v };
        self.cols[c].push(coeff_pos);
        Ok(())
    }

    /// insert a continuous sequence of values at row r starting from c_offset
    pub fn insert_row_slice(
        &mut self,
        r: usize,
        c_offset: usize,
        vs: Vec<T>,
    ) -> Result<(), LinkError> {
        // NB: could be improved in efficiency by first extending the vector
        for (i, x) in vs.into_iter().enumerate() {
            self.insert_val(r, c_offset + i, x)?;
        }
        Ok(())
    }

    pub fn get_col(&self, c: usize) -> Result<&Col<T>, LinkError> {
        if self.cols.len() < c {
            return Err(LinkError::InvalidIndex(c, self.cols.len()));
        }
        Ok(&self.cols[c])
    }
}

pub struct SparseLinAlgebra<PE: PairingEngine> {
    pairing_engine_type: PhantomData<PE>,
}

impl<PE: PairingEngine> SparseLinAlgebra<PE> {
    /// Inner product of a column of a sparse matrix and another (sparse) vector
    /// this is basically a multi-exp
    pub fn sparse_inner_product(
        v: &Vec<PE::Fr>,
        w: &Col<PE::G1Affine>,
    ) -> Result<PE::G1Affine, LinkError> {
        let mut res: PE::G1Projective = PE::G1Projective::zero();
        for coeffpos in w {
            let g = coeffpos.val;
            let i = coeffpos.pos;
            if v.len() < i {
                return Err(LinkError::InvalidIndex(i, v.len()));
            }
            // XXX: Can be optimized using MSM but its part of setup so less priority
            // XXX: Should this be optimized for special cases
            //         (e.g. 0 or 1) or is this already in .mul?
            let tmp = g.mul(v[i]);

            res.add_assign(&tmp);
        }
        Ok(res.into_affine())
    }

    /// Inner products of all columns of a sparse matrix and another (sparse) vector to compute the
    /// matrix multiplication `m^T \dot v` where `m^T` is the transpose of `m`.
    /// v has dimensions `v.len() x 1` and m has dimensions `nr x nc`. Returns a matrix of dimension `nr x 1`
    pub fn sparse_vector_matrix_mult(
        v: &Vec<PE::Fr>,
        m: &SparseMatrix<PE::G1Affine>,
    ) -> Result<Vec<PE::G1Affine>, LinkError> {
        // the result should contain every column of m multiplied by v
        let mut res: Vec<PE::G1Affine> = Vec::with_capacity(m.nc);
        for c in 0..m.nc {
            res.push(Self::sparse_inner_product(&v, m.get_col(c)?)?);
        }
        Ok(res)
    }
}

/// MSM between a scalar vector and a G1 vector
pub fn inner_product<PE: PairingEngine>(a: &[PE::Fr], b: &[PE::G1Affine]) -> PE::G1Affine {
    let a = cfg_iter!(a).map(|a| a.into_repr()).collect::<Vec<_>>();
    VariableBaseMSM::multi_scalar_mul(b, &a).into_affine()
}

/// Scale given vector `v` by scalar `a`
pub fn scale_vector<PE: PairingEngine>(a: &PE::Fr, v: &[PE::Fr]) -> Vec<PE::Fr> {
    let mut res: Vec<PE::Fr> = Vec::with_capacity(v.len());
    for i in 0..v.len() {
        let x: PE::Fr = a.mul(&v[i]);
        res.push(x);
    }
    res
}

/// Given a group element `g` and vector `multiples` of scalars, returns a vector with elements `v_i * g`
pub fn multiples_of_g<G: AffineCurve>(g: &G, multiples: &[G::ScalarField]) -> Vec<G> {
    let scalar_size = G::ScalarField::size_in_bits();
    let window_size = FixedBaseMSM::get_mul_window_size(multiples.len());
    let table = FixedBaseMSM::get_window_table(scalar_size, window_size, g.into_projective());
    let mut muls = FixedBaseMSM::multi_scalar_mul(scalar_size, window_size, &table, multiples);
    G::Projective::batch_normalization(&mut muls);
    muls.into_iter().map(|v| v.into()).collect()
}