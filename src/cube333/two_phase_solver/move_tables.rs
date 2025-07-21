//! Move tables for each coordinate type

use crate::coord::Coordinate;
use crate::cube333::{CubieCube, moves::Move333};
use crate::moves::{Cancellation, Move};

use super::coords::{DominoEPCoord, DominoESliceCoord, ESliceEdgeCoord};
use crate::cube333::coordcube::{COCoord, CPCoord, EOCoord};

use std::marker::PhantomData;

// TODO This may be generalised later, but for now it'll be specialised to just `CubieCube`

/// A type that encodes a subset of the set of 3x3 moves, e.g. DR moves.
pub trait SubMove: Move {
    /// Interpret a move as a normal move to be applied to a `CubieCube`.
    fn into_move(self) -> Move333;

    /// The number of moves that exist
    fn count() -> usize;

    /// The list of all moves that this type encodes. The length of the returned vector should be
    /// `count()`.
    fn moves() -> Vec<Self>;

    /// Get the index of this move in the move list.
    fn index(self) -> usize;
}

/// A move table, which stores mappings of coordinate + move pairs to the coordinate that results
/// from applying the move.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MoveTable<M: SubMove, C: Coordinate<CubieCube>> {
    table: Vec<Vec<C>>,
    _phantom: PhantomData<M>,
}

impl<M: SubMove, C: Coordinate<CubieCube>> MoveTable<M, C> {
    /// Generate a move table. This is slightly expensive, so making move tables repeatedly should
    /// be avoided, since the resulting move table generated will be identical anyways.
    pub fn generate() -> Self {
        let mut visited = vec![false; C::count()];
        let mut stack = vec![CubieCube::SOLVED];

        let mut table: Vec<Vec<C>> = (0..M::count())
            .map(|_| vec![C::default(); C::count()])
            .collect();

        while let Some(cur_cube) = stack.pop() {
            let c = C::from_puzzle(&cur_cube);
            for mv in M::moves() {
                let next = cur_cube.make_move(mv.clone().into_move());
                let c2 = C::from_puzzle(&next);

                table[mv.index()][c.repr()] = c2;

                if !visited[c.repr()] {
                    visited[c.repr()] = true;
                    stack.push(next);
                }
            }
        }

        Self {
            table,
            _phantom: PhantomData,
        }
    }

    /// Determine what coordinate comes from applying a move.
    fn apply(&self, coord: C, mv: M) -> C {
        self.table[mv.index()][coord.repr()]
    }
}

impl SubMove for Move333 {
    fn into_move(self) -> Move333 {
        self
    }

    fn count() -> usize {
        18
    }

    fn moves() -> Vec<Self> {
        use crate::cube333::moves::MoveGenerator;
        crate::cube333::moves::Htm::MOVE_LIST.to_vec()
    }

    fn index(self) -> usize {
        self.into()
    }
}

// TODO proptest DrMoves preserve phase 2

/// A move in domino reduction (phase 2).
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DrMove {
    R2,
    L2,
    F2,
    B2,
    U(u8),
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

    fn moves() -> Vec<Self> {
        use DrMove as M;
        vec![
            M::R2,
            M::L2,
            M::F2,
            M::B2,
            M::U(1),
            M::U(2),
            M::U(3),
            M::D(1),
            M::D(2),
            M::D(3),
        ]
    }

    fn index(self) -> usize {
        match self {
            DrMove::R2 => 0,
            DrMove::L2 => 1,
            DrMove::F2 => 2,
            DrMove::B2 => 3,
            // Technically this mod is unnecessary if the invariant that n is always in 1..=3
            // holds! But that's unsatisfying
            DrMove::U(n) => 4 + (n % 4) as usize,
            DrMove::D(n) => 7 + (n % 4) as usize,
        }
    }
}

type COMoveTable = MoveTable<Move333, COCoord>;
type EOMoveTable = MoveTable<Move333, EOCoord>;
type ESliceEdgeMoveTable = MoveTable<Move333, ESliceEdgeCoord>;
type DominoCPMoveTable = MoveTable<DrMove, CPCoord>;
type DominoEPTable = MoveTable<DrMove, DominoEPCoord>;
type DominoESliceMoveTable = MoveTable<DrMove, DominoESliceCoord>;
