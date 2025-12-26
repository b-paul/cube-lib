//! Pruning tables for the two phase solver.
//!
//! Choices of pruning tables are from cs0x7f's min2phase.

use super::coords::{
    COSymCoord, CPSymCoord, DominoEPSymCoord, DominoESliceCoord, EOSymCoord, ESliceEdgeCoord,
    RawSymTable, SymCoordinate,
};
use super::move_tables::{DrMove, MoveTable, SubMove, SymMoveTable};
use super::symmetry::Symmetry;
use crate::coord::{Coordinate, FromCoordinate};
use crate::cube333::{CubieCube, moves::Move333};

use std::marker::PhantomData;
use std::rc::Rc;

// TODO future stuff:
//  look into alternative pruning table choices
//  look into alternative information to store in pruning tables
//  look into alternative compression schemes

/// A table storing results of conjugating raw coordinates by symmetries or inverses of symmetries.
pub struct SymConjTable<S: Symmetry, R: Coordinate<CubieCube>, const SYMS: usize> {
    table: Box<[[R; SYMS]]>,
    inv_table: Box<[[R; SYMS]]>,
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
        let mut inv_table: Box<[[R; SYMS]]> =
            vec![std::array::from_fn(|_| Default::default()); R::count()].into_boxed_slice();

        for r1 in (0..R::count()).map(R::from_repr) {
            let mut c = CubieCube::SOLVED;
            c.set_coord(r1);
            for s in S::get_all() {
                let d = c.clone().conjugate_symmetry(s);
                let r2 = R::from_puzzle(&d);
                table[r1.repr()][s.repr()] = r2;
                let d = c.clone().conjugate_inverse_symmetry(s);
                let r2 = R::from_puzzle(&d);
                inv_table[r1.repr()][s.repr()] = r2;
            }
        }

        Self {
            table,
            inv_table,
            _phantom1: PhantomData,
            _phantom2: PhantomData,
        }
    }

    /// Conjugate the given raw coordinate by the given symmetry (S R S^-1).
    pub fn conjugate(&self, r: R, s: S) -> R {
        self.table[r.repr()][s.repr()]
    }

    /// Conjugate the given raw coordinate by the given symmetry's inverse (S^-1 R S).
    pub fn conjugate_inverse(&self, r: R, s: S) -> R {
        self.inv_table[r.repr()][s.repr()]
    }
}

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
> where
    CubieCube: FromCoordinate<R>,
    CubieCube: FromCoordinate<S::Raw>,
{
    table: Box<[u8]>,
    conj_table: SymConjTable<S::Sym, R, SYMS>,
    sym_table: Rc<RawSymTable<S>>,
    sym_move_table: Rc<SymMoveTable<M, S, MOVES, SYMS>>,
    raw_move_table: Rc<MoveTable<M, R, MOVES>>,
}

impl<S: SymCoordinate, R: Coordinate<CubieCube>, M: SubMove, const SYMS: usize, const MOVES: usize>
    SymRawPruningTable<S, R, M, SYMS, MOVES>
where
    CubieCube: FromCoordinate<R>,
    CubieCube: FromCoordinate<S::Raw>,
{
    /// Generate the table
    pub fn generate(
        sym_table: Rc<RawSymTable<S>>,
        sym_move_table: Rc<SymMoveTable<M, S, MOVES, SYMS>>,
        raw_move_table: Rc<MoveTable<M, R, MOVES>>,
    ) -> Self {
        let table = vec![0xff; S::classes() * R::count() / 4].into_boxed_slice();
        let conj_table = SymConjTable::generate();
        let mut table = Self {
            table,
            conj_table,
            sym_table,
            sym_move_table,
            raw_move_table,
        };

        let conj_table_s = SymConjTable::generate();

        let s = table.sym_table.puzzle_to_sym(&CubieCube::SOLVED);
        let r = R::from_puzzle(&CubieCube::SOLVED);
        table.set(s, r, 0, &conj_table_s);
        let mut stack = vec![(s, r)];
        let mut next = vec![];
        let mut depth = 1;

        while !stack.is_empty() {
            while let Some((s, r)) = stack.pop() {
                for &m in M::MOVE_LIST {
                    let s2 = table.sym_move_table.make_move(s, m);
                    let r2 = table.raw_move_table.make_move(r, m);
                    if table.query(s2, r2) == 3 {
                        next.push((s2, r2));
                        table.set(s2, r2, depth % 3, &conj_table_s);
                    }
                }
            }

            stack = next;
            next = vec![];
            depth += 1;
        }

        table
    }

    /// Compute the index and shift into the table given a coordinate pair.
    fn index(&self, s: S, r: R) -> (usize, usize) {
        let r2 = self.conj_table.conjugate_inverse(r, s.sym());
        let i = r2.repr() * S::classes() + s.class();
        (i >> 2, (i & 3) * 2)
    }

    /// Set the depth in the search tree of this coordinate pair modulo 3.
    fn set(&mut self, s: S, r: R, val: u8, conj_table_s: &SymConjTable<S::Sym, S::Raw, SYMS>) {
        assert!(val & !3 == 0);

        // Some S::Raw coordinates can be represented in multiple ways by S (there can be multiple
        // symmetries that give an equivalent raw coordinate when conjugating some representative,
        // think the solved state for example which could be represented by any symmetry). Because
        // of this, there could be multiple entries into our pruning table corresponding to the
        // same state. With just s and r, we would only update the entry corresponding to (if S is
        // the symmetry) S^-1 r S, and so we must iterate over all symmetries and find the
        // duplicates we need to update.

        let repr_raw = self.sym_table.index_to_repr(s.class());
        let sinv_raw = conj_table_s.conjugate(repr_raw, s.sym());
        for sym in S::Sym::get_all() {
            if conj_table_s.conjugate(repr_raw, sym) == sinv_raw {
                let s2 = S::from_repr(s.class(), sym);
                let (index, shift) = self.index(s2, r);

                self.table[index] &= !(3 << shift);
                self.table[index] |= val << shift;
            }
        }
    }

    /// Determine the bound of a coordinate pair modulo 3 with a lookup
    fn query(&self, s: S, r: R) -> u8 {
        let (index, shift) = self.index(s, r);

        (self.table[index] >> shift) & 3
    }

    /// Update a prune bound given the next state (fast)
    pub fn update(&self, cur: usize, s: S, r: R) -> usize {
        let n = self.query(s, r) as usize;
        let c = cur % 3;
        let d = (n + 3 - c).rem_euclid(3);
        match d {
            0 => cur,
            1 => cur + 1,
            2 => cur - 1,
            _ => unreachable!(),
        }
    }

    /// Compute the bound on a given coordinate pair (slow)
    pub fn bound(&self, mut s: S, mut r: R) -> usize {
        let mut bound = 0;
        let solved = (
            self.sym_table.puzzle_to_sym(&CubieCube::SOLVED).class(),
            R::from_puzzle(&CubieCube::SOLVED),
        );
        while (s.class(), r) != solved {
            let n = self.query(s, r);
            // n - 1 but underflow
            let goal = (n + 2).rem_euclid(3);
            (s, r) = M::MOVE_LIST
                .iter()
                .map(|&m| {
                    (
                        self.sym_move_table.make_move(s, m),
                        self.raw_move_table.make_move(r, m),
                    )
                })
                .find(|&(s, r)| self.query(s, r) == goal)
                .unwrap();

            bound += 1;
        }
        bound
    }
}

pub type ESliceTwistPruneTable = SymRawPruningTable<COSymCoord, ESliceEdgeCoord, Move333, 8, 18>;
pub type ESliceFlipPruneTable = SymRawPruningTable<EOSymCoord, ESliceEdgeCoord, Move333, 8, 18>;
pub type DominoSliceCPPruneTable =
    SymRawPruningTable<CPSymCoord, DominoESliceCoord, DrMove, 16, 10>;
pub type DominoSliceEPPruneTable =
    SymRawPruningTable<DominoEPSymCoord, DominoESliceCoord, DrMove, 16, 10>;

#[cfg(test)]
mod test {
    use super::super::move_tables::{DrMove, SubMove};
    use super::super::symmetry::HalfSymmetry;
    use super::*;
    use crate::coord::{Coordinate, FromCoordinate};
    use crate::cube333::coordcube::EOCoord;
    use crate::cube333::moves::Move333;
    use crate::moves::MoveSequence;

    use proptest::collection::vec;
    use proptest::prelude::*;

    type SliceConjTable = SymConjTable<HalfSymmetry, ESliceEdgeCoord, 8>;
    type EoConjTable = SymConjTable<HalfSymmetry, EOCoord, 8>;
    type DominoESliceConjTable = SymConjTable<HalfSymmetry, DominoESliceCoord, 8>;

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

    fn admissable_and_update_correct<
        S: SymCoordinate,
        R: Coordinate<CubieCube>,
        M: SubMove,
        const SYMS: usize,
        const MOVES: usize,
    >(
        prune_table: &SymRawPruningTable<S, R, M, SYMS, MOVES>,
        mvs: MoveSequence<M>,
    ) where
        CubieCube: FromCoordinate<R>,
        CubieCube: FromCoordinate<S::Raw>,
    {
        let s = prune_table.sym_table.puzzle_to_sym(&CubieCube::SOLVED);
        let s = prune_table.sym_move_table.make_moves(s, mvs.clone());
        let r = R::from_puzzle(&CubieCube::SOLVED);
        let r = prune_table.raw_move_table.make_moves(r, mvs.clone());
        let b = prune_table.bound(s, r);
        assert!(b <= mvs.len());

        for &m in M::MOVE_LIST {
            let s2 = prune_table.sym_move_table.make_move(s, m);
            let r2 = prune_table.raw_move_table.make_move(r, m);
            let b2 = prune_table.update(b, s2, r2);
            assert_eq!(b2, prune_table.bound(s2, r2));
        }
    }

    #[test]
    fn check_admissable_and_update() {
        let co_sym_table = Rc::new(RawSymTable::generate());
        let co_sym_move_table = Rc::new(SymMoveTable::generate(&co_sym_table));
        let eo_sym_table = Rc::new(RawSymTable::generate());
        let eo_sym_move_table = Rc::new(SymMoveTable::generate(&eo_sym_table));
        let e_slice_move_table = Rc::new(MoveTable::generate());
        let c_prune = ESliceTwistPruneTable::generate(
            co_sym_table,
            co_sym_move_table,
            e_slice_move_table.clone(),
        );
        let e_prune =
            ESliceFlipPruneTable::generate(eo_sym_table, eo_sym_move_table, e_slice_move_table);
        proptest!(|(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence))| {
            admissable_and_update_correct(&c_prune, mvs.clone());
            admissable_and_update_correct(&e_prune, mvs.clone());
        });
        let cp_sym_table = Rc::new(RawSymTable::generate());
        let cp_sym_move_table = Rc::new(SymMoveTable::generate(&cp_sym_table));
        let ep_sym_table = Rc::new(RawSymTable::generate());
        let ep_sym_move_table = Rc::new(SymMoveTable::generate(&ep_sym_table));
        let d_e_slice_move_table = Rc::new(MoveTable::generate());
        let d_c_prune = DominoSliceCPPruneTable::generate(
            cp_sym_table,
            cp_sym_move_table,
            d_e_slice_move_table.clone(),
        );
        let d_e_prune = DominoSliceEPPruneTable::generate(
            ep_sym_table,
            ep_sym_move_table,
            d_e_slice_move_table,
        );
        proptest!(|(mvs in vec(any::<DrMove>(), 0..20).prop_map(MoveSequence))| {
            admissable_and_update_correct(&d_c_prune, mvs.clone());
            admissable_and_update_correct(&d_e_prune, mvs.clone());
        });
    }
}
