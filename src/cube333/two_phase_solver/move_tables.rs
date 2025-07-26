//! Move tables for each coordinate type

use crate::coord::Coordinate;
use crate::cube333::CubieCube;
use crate::cube333::moves::{Move333, Move333Type};
use crate::moves::{Cancellation, Move, MoveSequence};

use super::coords::{DominoEPCoord, DominoESliceCoord, ESliceEdgeCoord};
use crate::cube333::coordcube::{COCoord, CPCoord, EOCoord};

use std::marker::PhantomData;

#[cfg(test)]
use proptest::strategy::Strategy;
#[cfg(test)]
use proptest_derive::Arbitrary;

// TODO This may be generalised later, but for now it'll be specialised to just `CubieCube`

/// A type that encodes a subset of the set of 3x3 moves, e.g. DR moves.
pub trait SubMove: Move + Copy
where
    Self: 'static,
{
    /// Interpret a move as a normal move to be applied to a `CubieCube`.
    fn into_move(self) -> Move333;

    /// The number of moves that exist
    fn count() -> usize;

    /// The list of all moves that this type encodes. The length of the returned vector should be
    /// `count()`.
    const MOVE_LIST: &'static [Self];

    /// Returns all of the states that come from applying each move to the given puzzle, along with
    /// the given move.
    fn successor_states(puzzle: CubieCube) -> impl Iterator<Item = (Self, CubieCube)> {
        Self::MOVE_LIST
            .iter()
            .map(move |m| (*m, puzzle.clone().make_move(m.into_move())))
    }

    /// Get the index of this move in the move list.
    fn index(self) -> usize;
}

/// A move table, which stores mappings of coordinate + move pairs to the coordinate that results
/// from applying the move.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MoveTable<M: SubMove, C: Coordinate<CubieCube>, const MOVES: usize> {
    table: Box<[[C; MOVES]]>,
    _phantom: PhantomData<M>,
}

impl<M: SubMove, C: Coordinate<CubieCube>, const MOVES: usize> MoveTable<M, C, MOVES> {
    /// Generate a move table. This is slightly expensive, so making move tables repeatedly should
    /// be avoided, since the resulting move table generated will be identical anyways.
    pub fn generate() -> Self {
        let mut visited = vec![false; C::count()];
        let mut stack = vec![CubieCube::SOLVED];
        visited[0] = true;

        let mut table: Box<[[C; MOVES]]> =
            vec![std::array::from_fn(|_| Default::default()); C::count()].into_boxed_slice();

        while let Some(cur_cube) = stack.pop() {
            let c = C::from_puzzle(&cur_cube);
            for (mv, next) in M::successor_states(cur_cube) {
                let c2 = C::from_puzzle(&next);

                table[c.repr()][mv.index()] = c2;

                if !visited[c2.repr()] {
                    visited[c2.repr()] = true;
                    stack.push(next);
                }
            }
        }

        debug_assert!(visited.into_iter().all(|b| b));

        Self {
            table,
            _phantom: PhantomData,
        }
    }

    /// Determine what coordinate comes from applying a move.
    pub fn make_move(&self, coord: C, mv: M) -> C {
        self.table[coord.repr()][mv.index()]
    }

    /// Determine what coordinate comes from applying a sequence of moves.
    fn make_moves(&self, coord: C, alg: MoveSequence<M>) -> C {
        alg.0.into_iter().fold(coord, |c, m| self.make_move(c, m))
    }
}

use crate::cube333::moves::MoveGenerator;
impl SubMove for Move333 {
    fn into_move(self) -> Move333 {
        self
    }

    fn count() -> usize {
        18
    }

    const MOVE_LIST: &'static [Move333] = crate::cube333::moves::Htm::MOVE_LIST;

    fn index(self) -> usize {
        self.into()
    }
}

// TODO proptest DrMoves preserve phase 2

/// A move in domino reduction (phase 2).
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(test, derive(Arbitrary))]
pub enum DrMove {
    R2,
    L2,
    F2,
    B2,
    #[cfg_attr(test, proptest(strategy = "(1..=3u8).prop_map(DrMove::U)", weight = 3))]
    U(u8),
    #[cfg_attr(test, proptest(strategy = "(1..=3u8).prop_map(DrMove::D)", weight = 3))]
    D(u8),
}

impl Move for DrMove {
    fn inverse(self) -> Self {
        match self {
            DrMove::U(n) => DrMove::U(4u8.wrapping_sub(n).rem_euclid(4)),
            DrMove::D(n) => DrMove::D(4u8.wrapping_sub(n).rem_euclid(4)),
            _ => self,
        }
    }

    fn commutes_with(&self, b: &Self) -> bool {
        use DrMove as M;
        match self {
            M::R2 | M::L2 => matches!(b, M::R2 | M::L2),
            M::F2 | M::B2 => matches!(b, M::F2 | M::B2),
            M::U(_) | M::D(_) => matches!(b, M::U(_) | M::D(_)),
        }
    }

    fn cancel(self, b: Self) -> Cancellation<Self> {
        use DrMove as M;
        match (self, b) {
            (M::R2, M::R2) => Cancellation::NoMove,
            (M::L2, M::L2) => Cancellation::NoMove,
            (M::F2, M::F2) => Cancellation::NoMove,
            (M::U(n), M::U(m)) if (n + m) % 4 == 0 => Cancellation::NoMove,
            (M::D(n), M::D(m)) if (n + m) % 4 == 0 => Cancellation::NoMove,
            (M::U(n), M::U(m)) => Cancellation::OneMove(M::U((n + m) % 4)),
            (M::D(n), M::D(m)) => Cancellation::OneMove(M::D((n + m) % 4)),
            (M::B2, M::B2) => Cancellation::NoMove,
            _ => Cancellation::TwoMove(self, b),
        }
    }
}

impl SubMove for DrMove {
    fn into_move(self) -> Move333 {
        use crate::mv;
        match self {
            DrMove::R2 => mv!(R, 2),
            DrMove::L2 => mv!(L, 2),
            DrMove::F2 => mv!(F, 2),
            DrMove::B2 => mv!(B, 2),
            DrMove::U(n) => mv!(U, n),
            DrMove::D(n) => mv!(D, n),
        }
    }

    fn count() -> usize {
        10
    }

    const MOVE_LIST: &'static [DrMove] = &[
        DrMove::R2,
        DrMove::L2,
        DrMove::F2,
        DrMove::B2,
        DrMove::U(1),
        DrMove::U(2),
        DrMove::U(3),
        DrMove::D(1),
        DrMove::D(2),
        DrMove::D(3),
    ];

    fn index(self) -> usize {
        match self {
            DrMove::R2 => 0,
            DrMove::L2 => 1,
            DrMove::F2 => 2,
            DrMove::B2 => 3,
            // Technically this mod is unnecessary if the invariant that n is always in 1..=3
            // holds! But that's unsatisfying
            DrMove::U(n) => 3 + (n % 4) as usize,
            DrMove::D(n) => 6 + (n % 4) as usize,
        }
    }
}

type COMoveTable = MoveTable<Move333, COCoord, 18>;
type EOMoveTable = MoveTable<Move333, EOCoord, 18>;
type ESliceEdgeMoveTable = MoveTable<Move333, ESliceEdgeCoord, 18>;
type DominoCPMoveTable = MoveTable<DrMove, CPCoord, 10>;
type DominoEPMoveTable = MoveTable<DrMove, DominoEPCoord, 10>;
type DominoESliceMoveTable = MoveTable<DrMove, DominoESliceCoord, 10>;

#[cfg(test)]
mod test {
    use super::*;

    use proptest::collection::vec;
    use proptest::prelude::*;

    #[test]
    fn generates() {
        COMoveTable::generate();
        EOMoveTable::generate();
        ESliceEdgeMoveTable::generate();
        DominoCPMoveTable::generate();
        DominoEPMoveTable::generate();
        DominoESliceMoveTable::generate();
    }

    /* We check that the following diagram commutes
     *
     *   CubieCube --apply_move--> CubieCube
     *      |                         |
     *      |                         |
     * from_puzzle              from_puzzle
     *      |                         |
     *      |                         |
     *      v                         v
     *    Coord -----apply_move---> Coord
     *
     * Move application should be compatable with coordinate translation.
     */

    fn diagram_commutes<
        M: SubMove,
        C: Coordinate<CubieCube> + std::fmt::Debug,
        const MOVES: usize,
    >(
        table: &MoveTable<M, C, MOVES>,
        p: CubieCube,
        mvs: MoveSequence<M>,
    ) {
        let l = table.make_moves(C::from_puzzle(&p), mvs.clone());
        let r = C::from_puzzle(&p.make_moves(MoveSequence(
            mvs.0.into_iter().map(|m| m.into_move()).collect(),
        )));
        assert_eq!(l, r);
    }

    #[test]
    fn commutes_normal() {
        let co_table = COMoveTable::generate();
        let eo_table = EOMoveTable::generate();
        let eslice_table = ESliceEdgeMoveTable::generate();
        proptest!(|(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence))| {
            diagram_commutes(&co_table, CubieCube::SOLVED, mvs.clone());
            diagram_commutes(&eo_table, CubieCube::SOLVED, mvs.clone());
            diagram_commutes(&eslice_table, CubieCube::SOLVED, mvs.clone());
        });
    }

    #[test]
    fn commutes_domino() {
        let cp_table = DominoCPMoveTable::generate();
        let ep_table = DominoEPMoveTable::generate();
        let eslice_table = DominoESliceMoveTable::generate();
        proptest!(|(mvs in vec(any::<DrMove>(), 0..20).prop_map(MoveSequence))| {
            diagram_commutes(&cp_table, CubieCube::SOLVED, mvs.clone());
            diagram_commutes(&ep_table, CubieCube::SOLVED, mvs.clone());
            diagram_commutes(&eslice_table, CubieCube::SOLVED, mvs.clone());
        });
    }
}
