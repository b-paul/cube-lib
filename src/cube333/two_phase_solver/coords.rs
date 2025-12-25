//! This module contains the coordinate representations of cube states relevant to the two phases
//! of these solver.

use super::symmetry::{DrSymmetry, HalfSymmetry, Symmetry};
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

fn set_p_coord<const COUNT: usize, const LOWER: usize, const UPPER: usize, P: Copy>(
    mut c: usize,
    perm: &mut [P; COUNT],
    mut bag: Vec<P>,
) {
    let mut n = [0; COUNT];
    for (i, n) in n.iter_mut().enumerate() {
        *n = c % (i + 1);
        c /= i + 1;
    }

    for i in (LOWER..=UPPER).rev() {
        let index = n[i - LOWER];
        perm[i] = bag[index];
        bag.remove(index);
    }
}

/// Coordinate for positions of E slice edges (ignoring what the edges actually are)
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct ESliceEdgeCoord(u16);

/// Coordinate for positions of U/D layer edges, assuming the cube is in and says in domino
/// reduction.
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct DominoEPCoord(u16);

/// Coordinate for positions of the E slice edges, assuming the cube is in and says in domino
/// reduction.
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct DominoESliceCoord(u16);

impl Coordinate<CubieCube> for ESliceEdgeCoord {
    fn from_puzzle(puzzle: &CubieCube) -> Self {
        // https://kociemba.org/math/UDSliceCoord.htm
        let mut r = 0;

        // c is meant to be n choose (k-1) if k >= 1
        let mut k = 0;
        let mut c = 0u16;

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
                    debug_assert!((c * (n + 1)).is_multiple_of(k - 1));
                    c = c * (n + 1) / (k - 1);
                }
            } else if k > 0 {
                r += c;
                // In this case we want to update n choose k-1 to be n+1 choose k-1. To do this we
                // can use the identity
                // (n choose k) = (n/(n-k)) (n-1 choose k)
                debug_assert!((c * (n + 1)).is_multiple_of(n + 1 - k + 1));
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

fn binom(n: usize, k: usize) -> usize {
    (n - k + 1..=n).product::<usize>() / (1..=k).product::<usize>()
}

impl FromCoordinate<ESliceEdgeCoord> for CubieCube {
    fn set_coord(&mut self, coord: ESliceEdgeCoord) {
        self.ep = CubieCube::SOLVED.ep;
        // Identify the locations of each e slice edge.
        let mut c = coord.repr();
        let mut poses = [0; 4];
        let (mut n, mut k) = (11, 3);
        let mut p = 0;
        for i in (0..12).rev() {
            let b = binom(n, k);
            if b > c {
                poses[p] = i;
                p += 1;
                if k == 0 {
                    break;
                }
                k -= 1;
            } else {
                c -= b;
            }
            n -= 1;
        }
        // swap e slice edges (8..=11 is the e slice edge positions)
        for (a, b) in poses.into_iter().rev().zip(8..=11) {
            self.ep.swap(a, b);
        }
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

impl FromCoordinate<DominoEPCoord> for CubieCube {
    fn set_coord(&mut self, coord: DominoEPCoord) {
        // UHHH i hope this is fine...
        // self.ep = CubieCube::SOLVED.ep;

        use crate::cube333::edge::Edge as E;
        let bag = vec![E::DR, E::DB, E::DL, E::DF, E::UR, E::UB, E::UL, E::UF];

        set_p_coord::<12, 0, 7, E>(coord.repr(), &mut self.ep, bag);
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

impl FromCoordinate<DominoESliceCoord> for CubieCube {
    fn set_coord(&mut self, coord: DominoESliceCoord) {
        //self.ep = CubieCube::SOLVED.ep;

        use crate::cube333::edge::Edge as E;
        let bag = vec![E::BR, E::BL, E::FL, E::FR];

        set_p_coord::<12, 8, 11, E>(coord.repr(), &mut self.ep, bag);
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
    fn repr(self) -> (usize, Self::Sym) {
        (self.class(), self.sym())
    }

    /// Convert the representation of a coordinate to the coordinate itself. We assume 0 with the
    /// identity symmetry corresponds to the solved state.
    fn from_repr(idx: usize, sym: Self::Sym) -> Self;

    /// Obtain the equivalence class this coordinate represents.
    fn class(self) -> usize;

    /// Obtain the underlying symmetry of this ooordinate.
    fn sym(self) -> Self::Sym;
}

pub struct RawSymTable<S: SymCoordinate>
where
    CubieCube: FromCoordinate<S::Raw>,
{
    raw_to_sym: Box<[S]>,
    class_to_repr: Box<[S::Raw]>,
}

impl<S: SymCoordinate> RawSymTable<S>
where
    CubieCube: FromCoordinate<S::Raw>,
{
    pub fn generate() -> Self {
        let mut raw_to_sym = vec![S::default(); S::Raw::count()].into_boxed_slice();
        let mut class_to_repr = vec![S::Raw::default(); S::classes()].into_boxed_slice();

        let mut sym_idx = 0;

        for raw in (0..S::Raw::count()).map(S::Raw::from_repr) {
            // Skip entries we have already initialised (note that states symmetric to the solved
            // state will not have solved SymCoordinate since a SymCoordinate will include its
            // symmetry)
            if raw_to_sym[raw.repr()] != S::default() {
                continue;
            }

            let mut c = CubieCube::SOLVED;
            c.set_coord(raw);

            // Then we go over every coordinate symmetric to this one, and update the tables based
            // on them.
            for sym in S::Sym::get_all() {
                let d = c.clone().conjugate_symmetry(sym);
                let raw2 = S::Raw::from_puzzle(&d);
                raw_to_sym[raw2.repr()] = S::from_repr(sym_idx, sym);
            }

            class_to_repr[sym_idx] = raw;
            sym_idx += 1;
        }

        RawSymTable {
            raw_to_sym,
            class_to_repr,
        }
    }

    pub fn raw_to_sym(&self, raw: S::Raw) -> S {
        self.raw_to_sym[raw.repr()]
    }

    pub fn index_to_repr(&self, idx: usize) -> S::Raw {
        self.class_to_repr[idx]
    }

    pub fn puzzle_to_sym(&self, p: &CubieCube) -> S {
        self.raw_to_sym(S::Raw::from_puzzle(p))
    }

    pub fn sym_to_raw(&self, sym: S) -> S::Raw {
        let repr = self.index_to_repr(sym.class());
        let mut c = CubieCube::SOLVED;
        c.set_coord(repr);
        let d = c.conjugate_symmetry(sym.sym());
        S::Raw::from_puzzle(&d)
    }
}

#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct COSymCoord(u16);

impl SymCoordinate for COSymCoord {
    type Sym = HalfSymmetry;

    type Raw = COCoord;

    fn count() -> usize {
        Self::classes() * 16
    }

    fn classes() -> usize {
        324
    }

    fn from_repr(idx: usize, sym: Self::Sym) -> Self {
        COSymCoord((idx as u16) << 3 | (sym.repr() as u16))
    }

    fn class(self) -> usize {
        (self.0 >> 3) as usize
    }

    fn sym(self) -> Self::Sym {
        HalfSymmetry::from_repr((self.0 & 7) as usize)
    }
}

#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct EOSymCoord(u16);

impl SymCoordinate for EOSymCoord {
    type Sym = HalfSymmetry;

    type Raw = EOCoord;

    fn count() -> usize {
        Self::classes() * 8
    }

    fn classes() -> usize {
        336
    }

    fn from_repr(idx: usize, sym: Self::Sym) -> Self {
        EOSymCoord((idx as u16) << 3 | (sym.repr() as u16))
    }

    fn class(self) -> usize {
        (self.0 >> 3) as usize
    }

    fn sym(self) -> Self::Sym {
        HalfSymmetry::from_repr((self.0 & 7) as usize)
    }
}

#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct CPSymCoord(u16);

impl SymCoordinate for CPSymCoord {
    type Sym = DrSymmetry;

    type Raw = CPCoord;

    fn count() -> usize {
        Self::classes() * 16
    }

    fn classes() -> usize {
        2768
    }

    fn from_repr(idx: usize, sym: Self::Sym) -> Self {
        CPSymCoord((idx as u16) << 4 | (sym.repr() as u16))
    }

    fn class(self) -> usize {
        (self.0 >> 4) as usize
    }

    fn sym(self) -> Self::Sym {
        DrSymmetry::from_repr((self.0 & 15) as usize)
    }
}

#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct DominoEPSymCoord(u16);

impl SymCoordinate for DominoEPSymCoord {
    type Sym = DrSymmetry;

    type Raw = DominoEPCoord;

    fn count() -> usize {
        Self::classes() * 16
    }

    fn classes() -> usize {
        2768
    }

    fn from_repr(idx: usize, sym: Self::Sym) -> Self {
        DominoEPSymCoord((idx as u16) << 4 | (sym.repr() as u16))
    }

    fn class(self) -> usize {
        (self.0 >> 4) as usize
    }

    fn sym(self) -> Self::Sym {
        DrSymmetry::from_repr((self.0 & 15) as usize)
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use itertools::Itertools;

    use super::super::move_tables::{DrMove, SubMove};
    use super::*;
    use crate::{
        coord::Coordinate,
        cube333::{CubieCube, moves::Move333},
        moves::MoveSequence,
    };

    use proptest::collection::vec;
    use proptest::prelude::*;

    fn sets_coord<C: Coordinate<CubieCube> + std::fmt::Debug>(mvs: MoveSequence<Move333>)
    where
        CubieCube: FromCoordinate<C>,
    {
        let coord = C::from_puzzle(&CubieCube::SOLVED.make_moves(mvs));
        let mut d = CubieCube::SOLVED;
        d.set_coord(coord);
        assert_eq!(C::from_puzzle(&d), coord);
    }

    #[test]
    fn from_coord() {
        proptest!(|(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence))| {
            sets_coord::<ESliceEdgeCoord>(mvs);
        });
    }

    #[test]
    fn from_coord_dr() {
        proptest!(|(mvs in vec(any::<DrMove>(), 0..20).prop_map(|v| v.into_iter().map(SubMove::into_move).collect()).prop_map(MoveSequence))| {
            sets_coord::<DominoESliceCoord>(mvs.clone());
            sets_coord::<DominoEPCoord>(mvs);
        });
    }

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

    #[test]
    fn sym_table_generates() {
        RawSymTable::<COSymCoord>::generate();
        RawSymTable::<EOSymCoord>::generate();
        RawSymTable::<CPSymCoord>::generate();
        RawSymTable::<DominoEPSymCoord>::generate();
    }

    #[test]
    fn sym_class_repr_in_class() {
        let co_sym = RawSymTable::<COSymCoord>::generate();
        let eo_sym = RawSymTable::<EOSymCoord>::generate();
        proptest!(|(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence))| {
            let c = CubieCube::SOLVED.make_moves(mvs);
            let co = COCoord::from_puzzle(&c);
            assert_eq!(co_sym.raw_to_sym(co_sym.index_to_repr(co_sym.raw_to_sym(co).class())).class(), co_sym.raw_to_sym(co).class());
            let eo = EOCoord::from_puzzle(&c);
            assert_eq!(eo_sym.raw_to_sym(eo_sym.index_to_repr(eo_sym.raw_to_sym(eo).class())).class(), eo_sym.raw_to_sym(eo).class());
        });
        let cp_sym = RawSymTable::<CPSymCoord>::generate();
        let ep_sym = RawSymTable::<DominoEPSymCoord>::generate();
        proptest!(|(mvs in vec(any::<DrMove>(), 0..20).prop_map(|v| v.into_iter().map(SubMove::into_move).collect()).prop_map(MoveSequence))| {
            let c = CubieCube::SOLVED.make_moves(mvs);
            let cp = CPCoord::from_puzzle(&c);
            assert_eq!(cp_sym.raw_to_sym(cp_sym.index_to_repr(cp_sym.raw_to_sym(cp).class())).class(), cp_sym.raw_to_sym(cp).class());
            let ep = DominoEPCoord::from_puzzle(&c);
            assert_eq!(ep_sym.raw_to_sym(ep_sym.index_to_repr(ep_sym.raw_to_sym(ep).class())).class(), ep_sym.raw_to_sym(ep).class());
        });
    }

    fn raw_to_sym_right_inverse<S: SymCoordinate>()
    where
        CubieCube: FromCoordinate<S::Raw>,
        S::Raw: std::fmt::Debug,
    {
        let table = RawSymTable::<S>::generate();
        for raw in (0..S::Raw::count()).map(S::Raw::from_repr) {
            assert_eq!(raw, table.sym_to_raw(table.raw_to_sym(raw)));
        }
    }

    #[test]
    fn raw_to_sym_right_inverse_all() {
        raw_to_sym_right_inverse::<COSymCoord>();
        raw_to_sym_right_inverse::<EOSymCoord>();
        raw_to_sym_right_inverse::<CPSymCoord>();
        raw_to_sym_right_inverse::<DominoEPSymCoord>();
    }
}
