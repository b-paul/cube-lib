//! This module contains the coordinate representations of cube states relevant to the two phases
//! of these solver.

use crate::coord::Coordinate;
use crate::cube333::CubieCube;

// TODO Copy pasted from the old coordcube file that i'll probably delete, should clean up
fn to_o_coord<const COUNT: usize, const STATES: u16>(arr: &[u8; COUNT]) -> u16 {
    arr.iter()
        .skip(1)
        .fold(0, |acc, &i| (acc * STATES) + i as u16)
}

/*
// TODO this is kinda unreadable lol
fn to_p_coord<const COUNT: usize>(arr: &[u8; COUNT]) -> u32 {
    (1..COUNT).rev().fold(0, |acc, idx| {
        (acc * (idx + 1) as u32) + arr[0..idx].iter().filter(|&&x| x > arr[idx]).count() as u32
    })
}
*/

#[derive(Debug, Default, PartialEq, Eq, Copy, Clone, Hash)]
struct COCoord(u16);

#[derive(Debug, Default, PartialEq, Eq, Copy, Clone, Hash)]
struct EOCoord(u16);

#[derive(Debug, Default, PartialEq, Eq, Copy, Clone, Hash)]
struct ESliceEdgeCoord(u16);

impl Coordinate<CubieCube> for COCoord {
    fn from_puzzle(puzzle: &CubieCube) -> Self {
        COCoord(to_o_coord::<8, 3>(&puzzle.co.map(|n| n.into())))
    }

    fn count() -> usize {
        // 3^7
        2187
    }

    fn repr(self) -> usize {
        self.0 as usize
    }
}

impl Coordinate<CubieCube> for EOCoord {
    fn from_puzzle(puzzle: &CubieCube) -> Self {
        EOCoord(to_o_coord::<12, 2>(&puzzle.eo.map(|n| n.into())))
    }

    fn count() -> usize {
        // 2^11
        2048
    }

    fn repr(self) -> usize {
        self.0 as usize
    }
}

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
                    c = n + 1;
                } else {
                    // Otherwise, c was previously equal to n choose k-1, and we want to update it
                    // to be n+1 choose k. To do this we can use the identity
                    // n choose k = (n/k) * (n-1 choose k-1)
                    // we have to divide at the end do dodge floor division
                    debug_assert!((c * n) % (k - 1) == 0);
                    c = c * (n + 1) / (k - 1);
                }
            } else if k > 0 {
                r += c;
                // In this case we want to update n choose k-1 to be n+1 choose k-1. To do this we
                // can use the identity
                // (n choose k) = (n/(n-k)) (n-1 choose k)
                debug_assert!((c * n) % (n - k + 1) == 0);
                c = c * (n + 1) / (n - k + 1);
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
}

#[derive(Debug, Default, PartialEq, Eq, Copy, Clone)]
// temp
#[allow(dead_code)]
struct Phase1Cube {
    co: COCoord,
    eo: EOCoord,
    e_slice: ESliceEdgeCoord,
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
    }
}
