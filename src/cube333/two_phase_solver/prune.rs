//! Pruning tables for the two phase solver.
//!
//! Choices of pruning tables are from cs0x7f's min2phase.

use super::coords::{
    COSymCoord, DominoESliceCoord, EOSymCoord, ESliceEdgeCoord, RawSymTable, SymCoordinate,
};
use super::move_tables::{MoveTable, SubMove, SymMoveTable};
use super::symmetry::{HalfSymmetry, Symmetry};
use crate::coord::{Coordinate, FromCoordinate};
use crate::cube333::{CubieCube, coordcube::EOCoord, moves::Move333};

use std::marker::PhantomData;

// TODO future stuff:
//  look into alternative pruning table choices
//  look into alternative information to store in pruning tables
//  look into alternative compression schemes

/// A table storing results of conjugating raw coordinates by inverses of symmetries (i.e. we
/// compute S^-1 R S given R and S).
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
                let d = c.clone().conjugate_inverse_symmetry(s);
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

    /// Conjugate the given raw coordinate by the given symmetry's inverse (S^-1 R S).
    pub fn conjugate(&self, r: R, s: S) -> R {
        self.table[r.repr()][s.repr()]
    }
}

type SliceConjTable = SymConjTable<HalfSymmetry, ESliceEdgeCoord, 8>;
type EoConjTable = SymConjTable<HalfSymmetry, EOCoord, 8>;
type DominoESliceConjTable = SymConjTable<HalfSymmetry, DominoESliceCoord, 8>;

/// A pruning table indexed by the class of a symmetry coordinate and a raw coordinate.
///
/// COUNT should be the number of symmetry coordinate classes times the number of raw coordinates
/// divided by 4 (we store 4 entries per byte). An entry is the optimal search depth of the state
/// modulo 3, see https://kociemba.org/math/pruning.htm for a detailed explanation. Essentially
/// though, we can compute the whole pruning depth based on solely the pruning depth modulo 3 if we
/// know the pruning depth of the current state we are in, when searching.
pub struct SymRawPruningTable<
    S: SymCoordinate,
    R: Coordinate<CubieCube>,
    M: SubMove,
    const SYMS: usize,
    const MOVES: usize,
> {
    table: Box<[u8]>,
    conj_table: SymConjTable<S::Sym, R, SYMS>,
    _phantom1: PhantomData<S>,
    _phantom2: PhantomData<R>,
    _phantom3: PhantomData<M>,
}

impl<S: SymCoordinate, R: Coordinate<CubieCube>, M: SubMove, const SYMS: usize, const MOVES: usize>
    SymRawPruningTable<S, R, M, SYMS, MOVES>
where
    CubieCube: FromCoordinate<R>,
    CubieCube: FromCoordinate<S::Raw>,
{
    pub fn generate(
        sym_table: &RawSymTable<S>,
        sym_move_table: &SymMoveTable<M, S, MOVES, SYMS>,
        raw_move_table: &MoveTable<M, R, MOVES>,
    ) -> Self {
        let table = vec![0xff; S::classes() * R::count() / 4].into_boxed_slice();
        let conj_table = SymConjTable::generate();
        let mut table = Self {
            table,
            conj_table,
            _phantom1: PhantomData,
            _phantom2: PhantomData,
            _phantom3: PhantomData,
        };

        let s = sym_table.puzzle_to_sym(&CubieCube::SOLVED);
        let r = R::from_puzzle(&CubieCube::SOLVED);
        table.set(s, r, 0, sym_table);
        let mut stack = vec![(s, r)];
        let mut next = vec![];
        let mut depth = 1;

        while !stack.is_empty() {
            while let Some((s, r)) = stack.pop() {
                for &m in M::MOVE_LIST {
                    let s2 = sym_move_table.make_move(s, m);
                    let r2 = raw_move_table.make_move(r, m);
                    if table.query(s2, r2) == 3 {
                        next.push((s2, r2));
                        table.set(s2, r2, depth % 3, sym_table);
                    }
                }
            }

            stack = next;
            next = vec![];
            depth += 1;
        }

        table
    }

    fn index(&self, s: S, r: R) -> (usize, usize) {
        let r2 = self.conj_table.conjugate(r, s.sym());
        let i = r2.repr() * S::classes() + s.class();
        (i >> 2, (i & 3) * 2)
    }

    /// Set the depth in the search tree of this coordinate pair modulo 3.
    fn set(&mut self, s: S, r: R, val: u8, sym_table: &RawSymTable<S>) {
        assert!(val & !3 == 0);

        // Some S::Raw coordinates can be represented in multiple ways by S (there can be multiple
        // symmetries that give an equivalent raw coordinate when conjugating some representative,
        // think the solved state for example which could be represented by any symmetry). Because
        // of this, there could be multiple entries into our pruning table corresponding to the
        // same state. With just s and r, we would only update the entry corresponding to (if S is
        // the symmetry) S^-1 r S, and so we must iterate over all symmetries and find the
        // duplicates we need to update.

        /* i'll do it later
        for sym in S::Sym::get_all() {
            todo!()
        }
        */

        let (index, shift) = self.index(s, r);

        self.table[index] &= !(3 << shift);
        self.table[index] |= val << shift;
    }

    pub fn query(&self, s: S, r: R) -> u8 {
        let (index, shift) = self.index(s, r);

        (self.table[index] >> shift) & 3
    }
}

type ESliceTwistPruneTable = SymRawPruningTable<COSymCoord, ESliceEdgeCoord, Move333, 8, 18>;
type ESliceFlipPruneTable = SymRawPruningTable<EOSymCoord, ESliceEdgeCoord, Move333, 8, 18>;

#[cfg(test)]
mod test {
    use super::super::move_tables::{DrMove, SubMove};
    use super::*;
    use crate::cube333::moves::Move333;
    use crate::moves::MoveSequence;

    use proptest::collection::vec;
    use proptest::prelude::*;

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
            let b = R::from_puzzle(&cube.clone().conjugate_inverse_symmetry(s));
            assert_eq!(a, b);
        }
    }

    #[test]
    fn conj_commutes() {
        let slice_conj_table = SliceConjTable::generate();
        let eo_conj_table = EoConjTable::generate();
        let domino_eo_conj_table = DominoESliceConjTable::generate();
        proptest!(|(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence))| {
            diagram_commutes(&slice_conj_table, CubieCube::SOLVED.make_moves(mvs.clone()));
            diagram_commutes(&eo_conj_table, CubieCube::SOLVED.make_moves(mvs.clone()));
        });
        proptest!(|(mvs in vec(any::<DrMove>(), 0..20).prop_map(|v| v.into_iter().map(SubMove::into_move).collect()).prop_map(MoveSequence))| {
            diagram_commutes(&domino_eo_conj_table, CubieCube::SOLVED.make_moves(mvs.clone()));
        });
    }

    #[test]
    fn prune_generates() {
        let co_sym_table = RawSymTable::generate();
        let co_sym_move_table = SymMoveTable::generate(&co_sym_table);
        let eo_sym_table = RawSymTable::generate();
        let eo_sym_move_table = SymMoveTable::generate(&eo_sym_table);
        let e_slice_move_table = MoveTable::generate();

        ESliceTwistPruneTable::generate(&co_sym_table, &co_sym_move_table, &e_slice_move_table);
        ESliceFlipPruneTable::generate(&eo_sym_table, &eo_sym_move_table, &e_slice_move_table);
    }
}
