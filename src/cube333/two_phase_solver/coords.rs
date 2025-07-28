//! This module contains the coordinate representations of cube states relevant to the two phases
//! of these solver.

use super::symmetry::Symmetry;
use crate::coord::{Coordinate, FromCoordinate};
use crate::cube333::{
    CubieCube,
    coordcube::{COCoord, CPCoord, EOCoord},
};

// TODO this is kinda unreadable lol
// this is copied from coordcube.rs then modified hmmm maybe copy pasting isn't ideal
fn to_p_coord<const COUNT: usize, const LOWER: usize, const UPPER: usize>(
    arr: &[u8; COUNT],
) -> u16 {
    (0..UPPER - LOWER).rev().fold(0, |acc, idx| {
        (acc * (idx + 1) as u16)
            + arr[LOWER..LOWER + idx]
                .iter()
                .filter(|&&x| x > arr[LOWER + idx])
                .count() as u16
    })
}

/// Coordinate for positions of E slice edges (ignoring what the edges actually arge)
#[derive(Debug, Default, PartialEq, Eq, Copy, Clone, Hash)]
pub struct ESliceEdgeCoord(u16);

/// Coordinate for positions of U/D layer edges, assuming the cube is in and says in domino
/// reduction.
#[derive(Debug, Default, PartialEq, Eq, Copy, Clone, Hash)]
pub struct DominoEPCoord(u16);

/// Coordinate for positions of the E slice edges, assuming the cube is in and says in domino
/// reduction.
#[derive(Debug, Default, PartialEq, Eq, Copy, Clone, Hash)]
pub struct DominoESliceCoord(u16);

impl Coordinate<CubieCube> for ESliceEdgeCoord {
    fn from_puzzle(puzzle: &CubieCube) -> Self {
        // https://kociemba.org/math/UDSliceCoord.htm
        let mut r = 0;

        // c is meant to be n choose (k-1) if k >= 1
        let mut k = 0;
        let mut c = 0;

        for n in 0..12 {
            if puzzle.ep[n as usize].e_slice() {
                // every time we reach an e slice edge, we increment k, and then have to fix the
                // value of c.
                k += 1;
                if k == 1 {
                    // if k was previously zero, c was 0, so just set c to be the next n value
                    c = 1;
                } else {
                    // Otherwise, c was previously equal to n choose k-1, and we want to update it
                    // to be n+1 choose k. To do this we can use the identity
                    // n choose k = (n/k) * (n-1 choose k-1)
                    // we have to divide at the end do dodge floor division
                    debug_assert!((c * (n + 1)) % (k - 1) == 0);
                    c = c * (n + 1) / (k - 1);
                }
            } else if k > 0 {
                r += c;
                // In this case we want to update n choose k-1 to be n+1 choose k-1. To do this we
                // can use the identity
                // (n choose k) = (n/(n-k)) (n-1 choose k)
                debug_assert!((c * (n + 1)) % (n + 1 - k + 1) == 0);
                c = c * (n + 1) / (n + 1 - k + 1);
            }
        }

        ESliceEdgeCoord(r)
    }

    fn count() -> usize {
        495
    }

    fn repr(self) -> usize {
        self.0 as usize
    }

    fn from_repr(n: usize) -> Self {
        ESliceEdgeCoord(n as u16)
    }
}

impl Coordinate<CubieCube> for DominoEPCoord {
    fn from_puzzle(puzzle: &CubieCube) -> Self {
        DominoEPCoord(to_p_coord::<12, 0, 8>(&puzzle.ep.map(|n| n.into())))
    }

    fn count() -> usize {
        40320
    }

    fn repr(self) -> usize {
        self.0 as usize
    }

    fn from_repr(n: usize) -> Self {
        DominoEPCoord(n as u16)
    }
}

impl Coordinate<CubieCube> for DominoESliceCoord {
    fn from_puzzle(puzzle: &CubieCube) -> Self {
        DominoESliceCoord(to_p_coord::<12, 8, 12>(&puzzle.ep.map(|n| n.into())))
    }

    fn count() -> usize {
        24
    }

    fn repr(self) -> usize {
        self.0 as usize
    }

    fn from_repr(n: usize) -> Self {
        DominoESliceCoord(n as u16)
    }
}

/// A symmetry coordinate over a `Symmetry`. A SymCoordinate should include both what equivalence
/// class the coordinate is in, along with the symmetry it has from the representant.
pub trait SymCoordinate: Copy + Default + Eq {
    type Sym: Symmetry;
    type Raw: Coordinate<CubieCube>;

    /// The number of possible coordinate states.
    fn count() -> usize;

    /// The number of equivalence classes this coordinate encodes modulo symmetry.
    fn classes() -> usize;

    /// A representation of this coordinate as a usize, for use, in table lookups.
    fn repr(self) -> (usize, Self::Sym);

    /// Convert the representation of a coordinate to the coordinate itself. We assume 0 with the
    /// identity symmetry corresponds to the solved state.
    fn from_repr(idx: usize, sym: Self::Sym) -> Self;
}

pub struct RawDrSymTable<S: SymCoordinate>
where
    CubieCube: FromCoordinate<S::Raw>,
{
    raw_to_sym: Box<[S]>,
    sym_to_raw: Box<[S::Raw]>,
}

impl<S: SymCoordinate> RawDrSymTable<S>
where
    CubieCube: FromCoordinate<S::Raw>,
{
    pub fn generate() -> Self {
        let mut raw_to_sym = vec![S::default(); S::Raw::count()].into_boxed_slice();
        let mut sym_to_raw = vec![S::Raw::default(); S::count()].into_boxed_slice();

        let mut sym_idx = 0;

        for raw in (0..S::Raw::count()).map(S::Raw::from_repr) {
            // Skip entries we have already initialised (note that states symmetric to the solved
            // state will not have solved SymCoordinate since a SymCoordinate will include its
            // symmetry)
            if sym_to_raw[raw.repr()] != S::Raw::default() {
                continue;
            }

            let mut c = CubieCube::SOLVED;
            c.set_coord(raw);

            // Then we go over every symmetry of this coordinate, and update the tables based on
            // them.
            for sym in S::Sym::get_all() {
                let d = c.clone().conjugate_symmetry(sym);
                let raw2 = S::Raw::from_puzzle(&d);
                raw_to_sym[raw2.repr()] = S::from_repr(sym_idx, sym);
            }

            sym_to_raw[sym_idx] = raw;
            sym_idx += 1;
        }

        RawDrSymTable {
            raw_to_sym,
            sym_to_raw,
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq, Copy, Clone)]
pub struct Phase1Cube {
    co: COCoord,
    eo: EOCoord,
    e_slice: ESliceEdgeCoord,
}

impl Phase1Cube {
    /// Convert a cubie cube into a phase 1 state cube. This will never fail as every cube can be
    /// put into the phase 1 solver.
    pub fn from_puzzle(puzzle: &CubieCube) -> Self {
        Phase1Cube {
            co: COCoord::from_puzzle(puzzle),
            eo: EOCoord::from_puzzle(puzzle),
            e_slice: ESliceEdgeCoord::from_puzzle(puzzle),
        }
    }
}

pub struct Phase2Cube {
    cp: CPCoord,
    ep: DominoEPCoord,
    e_slice: DominoESliceCoord,
}

fn cubie_in_domino(puzzle: &CubieCube) -> bool {
    let p1 = Phase1Cube::from_puzzle(puzzle);
    p1.co.repr() == 0 && p1.eo.repr() == 0 && p1.e_slice.repr() == 0
}

impl Phase2Cube {
    /// Attempt to convert a cubie cube into a Phase2Cube. This will fail if the cube is not in U/D
    /// domino reduction.
    pub fn from_puzzle(puzzle: &CubieCube) -> Option<Self> {
        cubie_in_domino(puzzle).then_some(Phase2Cube {
            cp: CPCoord::from_puzzle(puzzle),
            ep: DominoEPCoord::from_puzzle(puzzle),
            e_slice: DominoESliceCoord::from_puzzle(puzzle),
        })
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use itertools::Itertools;

    use super::ESliceEdgeCoord;
    use crate::{coord::Coordinate, cube333::CubieCube};

    #[test]
    fn e_slice_edge_uniqueness() {
        let mut coords = HashSet::new();
        for poses in (0..12).combinations(4) {
            let mut cube = CubieCube::SOLVED;

            for (a, b) in poses.into_iter().zip(8..12) {
                cube.ep.swap(a, b);
            }

            let coord = ESliceEdgeCoord::from_puzzle(&cube);
            assert!(!coords.contains(&coord));
            coords.insert(coord);
        }
        assert!(coords.len() == ESliceEdgeCoord::count());
        assert!(coords.iter().all(|c| c.repr() < ESliceEdgeCoord::count()));
    }
}
