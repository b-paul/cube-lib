//! Pruning tables for the two phase solver.
//!
//! Choices of pruning tables are from cs0x7f's min2phase.

use crate::coord::Coordinate;
use crate::cube333::CubieCube;
use super::coords::SymCoordinate;

use std::marker::PhantomData;

// TODO future stuff:
//  look into alternative pruning table choices
//  look into alternative information to store in pruning tables
//  look into alternative compression schemes

/// A pruning table indexed by the class of a symmetry coordinate and a raw coordinate.
///
/// COUNT should be the number of symmetry coordinate classes times the number of raw coordinates
/// divided by 4 (we store 4 entries per byte). An entry is the optimal search depth of the state
/// modulo 3, see https://kociemba.org/math/pruning.htm for a detailed explanation. Essentially
/// though, we can compute the whole pruning depth based on solely the pruning depth modulo 3 if we
/// know the pruning depth of the current state we are in, when searching.
pub struct SymRawPruningTable<S: SymCoordinate, R: Coordinate<CubieCube>, const COUNT: usize> {
    table: [u8; COUNT],
    _phantom1: PhantomData<S>,
    _phantom2: PhantomData<R>,
}

impl<S: SymCoordinate, R: Coordinate<CubieCube>, const COUNT: usize> SymRawPruningTable<S, R, COUNT> {
    pub fn generate() -> Self {
        todo!()
    }

    pub fn query(&self, s: S, r: R) -> u8 {
        // WE NEED CONJUGATE TABLES!!!!!!!!!!!!
        todo!()
    }
}
