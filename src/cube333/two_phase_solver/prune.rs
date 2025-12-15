//! Pruning tables for the two phase solver.
//!
//! Choices of pruning tables are from cs0x7f's min2phase.

use super::coords::{ESliceEdgeCoord, SymCoordinate};
use super::symmetry::{HalfSymmetry, Symmetry};
use crate::coord::{Coordinate, FromCoordinate};
use crate::cube333::{CubieCube, coordcube::EOCoord};

use std::marker::PhantomData;

// TODO future stuff:
//  look into alternative pruning table choices
//  look into alternative information to store in pruning tables
//  look into alternative compression schemes

/// A table storing results of conjugating raw coordinates by symmetries.
pub struct SymConjTable<S: Symmetry, R: Coordinate<CubieCube>, const SYMS: usize> {
    table: Box<[[R; SYMS]]>,
    _phantom1: PhantomData<S>,
    _phantom2: PhantomData<R>,
}

impl<S: Symmetry, R: Coordinate<CubieCube>, const SYMS: usize> SymConjTable<S, R, SYMS>
where
    CubieCube: FromCoordinate<R>,
{
    /// Generate the table
    pub fn generate() -> Self {
        let mut table: Box<[[R; SYMS]]> =
            vec![std::array::from_fn(|_| Default::default()); R::count()].into_boxed_slice();

        for r1 in (0..R::count()).map(R::from_repr) {
            let mut c = CubieCube::SOLVED;
            c.set_coord(r1);
            for s in S::get_all() {
                let d = c.clone().conjugate_symmetry(s);
                let r2 = R::from_puzzle(&d);
                table[r1.repr()][s.repr()] = r2;
            }
        }

        Self {
            table,
            _phantom1: PhantomData,
            _phantom2: PhantomData,
        }
    }

    /// Conjugate the given raw coordinate by the given symmetry
    pub fn conjugate(&self, r: R, s: S) -> R {
        self.table[r.repr()][s.repr()]
    }
}

type SliceConjTable = SymConjTable<HalfSymmetry, ESliceEdgeCoord, 8>;
type EoConjTable = SymConjTable<HalfSymmetry, EOCoord, 8>;

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

impl<S: SymCoordinate, R: Coordinate<CubieCube>, const COUNT: usize>
    SymRawPruningTable<S, R, COUNT>
{
    pub fn generate() -> Self {
        todo!()
    }

    pub fn query(&self, s: S, r: R) -> u8 {
        todo!()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cube333::moves::Move333;
    use crate::moves::MoveSequence;

    use proptest::collection::vec;
    use proptest::prelude::*;

    #[test]
    fn conj_generates() {
        //SliceConjTable::generate();
        EoConjTable::generate();
    }

    fn diagram_commutes<
        S: Symmetry,
        R: Coordinate<CubieCube> + std::fmt::Debug,
        const COUNT: usize,
    >(
        table: &SymConjTable<S, R, COUNT>,
        cube: CubieCube,
    ) where
        CubieCube: FromCoordinate<R>,
    {
        for s in S::get_all() {
            let a = table.conjugate(R::from_puzzle(&cube), s);
            let b = R::from_puzzle(&cube.clone().conjugate_symmetry(s));
            assert_eq!(a, b);
        }
    }

    #[test]
    fn conj_commutes() {
        let eo_conj_table = EoConjTable::generate();
        proptest!(|(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence))| {
            diagram_commutes(&eo_conj_table, CubieCube::SOLVED.make_moves(mvs.clone()));
        });
    }
}
