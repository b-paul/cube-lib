//! Implements symmetries for the `CubieCube` and symmetry tables for use in move table generation.

use crate::cube333::{Corner as C, CornerTwist as CT, CubieCube, Edge as E, EdgeFlip as EF};

pub trait Symmetry: Copy + Default + Eq {
    /// A representation of this symmetry as a usize, for use in table lookups.
    fn repr(self) -> usize;

    /// Convert the representation of a symmetry to the symmetry itself. We assume 0 corresponds to
    /// the identity symmetry.
    fn from_repr(n: usize) -> Self;

    /// Iterator over every symmetry in order of representation
    fn get_all() -> impl Iterator<Item = Self>;

    /// Obtain a CubieCube that applies this symmetry when multiplied.
    fn to_puzzle(self) -> CubieCube;
}

impl CubieCube {
    /// Obtain the cube given by applying some symmetry
    pub(super) fn apply_symmetry<S: Symmetry>(self, sym: S) -> CubieCube {
        self.multiply_cube(sym.to_puzzle())
    }

    /// Obtain the cube given by conjugating by some symmetry. We conjugate in the order S C S^-1
    pub(super) fn conjugate_symmetry<S: Symmetry>(self, sym: S) -> CubieCube {
        sym.to_puzzle()
            .multiply_cube(self)
            .multiply_cube(sym.to_puzzle().inverse())
    }
}

/// Multiplication table for a `Symmetry` group.
pub struct SymMultTable<S: Symmetry, const COUNT: usize> {
    table: [[S; COUNT]; COUNT],
}

impl<S: Symmetry, const COUNT: usize> SymMultTable<S, COUNT> {
    /// Generate the table
    pub fn generate() -> Self {
        use std::array::from_fn;

        let cubie_syms: [_; COUNT] = from_fn(|n| S::from_repr(n).to_puzzle());

        let table = from_fn(|a| {
            from_fn(|b| {
                let a = S::from_repr(a);
                let b = S::from_repr(b);
                let c = a.to_puzzle().multiply_cube(b.to_puzzle());
                S::from_repr(cubie_syms.iter().position(|d| &c == d).unwrap())
            })
        });

        SymMultTable { table }
    }

    /// Multiply two symmetries
    pub fn multiply(&self, a: S, b: S) -> S {
        self.table[a.repr()][b.repr()]
    }
}

/// An element of the set of symmetries of a cube that preserve domino reduction. This is generated
/// by:
/// - A 180 degree rotation around the F/B axis (aka F2)
/// - A 90 degree rotation around the U/D axis (aka U4)
/// - A reflection around the R-L slice (aka RL2)
// We represent a symmetry as a product of these generators in a specific order:
//  - the 0th bit determines R-L reflection
//  - the 1st bit determines F/B 180 rotation
//  - the 2nd and 3rd bits determines U/D rotation
// We multiply from top to bottom of this list. It doesn't really make sense to expose this
// information publicly, since we could have multiplied different generators in a different order.
// We can just think of this 4 bit number as an identifier for each symmetry.
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct DrSymmetry(u8);

pub type DrSymMultTable = SymMultTable<DrSymmetry, 16>;

/// A cube that, when multiplied, applies the F2 symmetry.
#[rustfmt::skip]
const SYM_F2: CubieCube = CubieCube {
    co: [CT::Oriented; 8],
    cp: [C::DFL, C::DFR, C::DBR, C::DBL, C::UFL, C::UFR, C::UBR, C::UBL],
    eo: [EF::Oriented; 12],
    ep: [E::DF, E::DR, E::DB, E::DL, E::UF, E::UR, E::UB, E::UL, E::FL, E::FR, E::BR, E::BL],
};

/// A cube that, when multiplied, applies the U4 symmetry.
#[rustfmt::skip]
const SYM_U4: CubieCube = CubieCube {
    co: [CT::Oriented; 8],
    cp: [C::UBR, C::UFR, C::UFL, C::UBL, C::DBR, C::DFR, C::DFL, C::DBL],
    eo: [EF::Oriented, EF::Oriented, EF::Oriented, EF::Oriented, EF::Oriented, EF::Oriented, EF::Oriented, EF::Oriented, EF::Flipped, EF::Flipped, EF::Flipped, EF::Flipped],
    ep: [E::UR, E::UF, E::UL, E::UB, E::DR, E::DF, E::DL, E::DB, E::BR, E::FR, E::FL, E::BL],
};

// TODO BUG!!! reflection isn't an element of the cube!!! applying this symmetry is meant to flip
// clockwise and anticlockwise, but here it doesn't!
/// A cube that, when multiplied, applies the RL2 symmetry.
#[rustfmt::skip]
const SYM_RL2: CubieCube = CubieCube {
    co: [CT::Oriented; 8],
    cp: [C::UBR, C::UBL, C::UFL, C::UFR, C::DBR, C::DBL, C::DFL, C::DFR],
    eo: [EF::Oriented; 12],
    ep: [E::UB, E::UL, E::UF, E::UR, E::DB, E::DL, E::DF, E::DR, E::BR, E::BL, E::FL, E::FR],
};

impl DrSymmetry {
    /// Returns the power of RL2 in the standard product notation of this symmetry.
    fn rl2_count(self) -> usize {
        (self.0 & 1) as usize
    }

    /// Returns the power of F2 in the standard product notation of this symmetry.
    fn f2_count(self) -> usize {
        (self.0 >> 1 & 1) as usize
    }

    /// Returns the power of U4 in the standard product notation of this symmetry.
    fn u4_count(self) -> usize {
        (self.0 >> 2 & 3) as usize
    }

    // lol
    /// An array of each symmetry
    #[rustfmt::skip]
    pub const ARRAY: [DrSymmetry; 16] = [DrSymmetry(0), DrSymmetry(1), DrSymmetry(2), DrSymmetry(3), DrSymmetry(4), DrSymmetry(5), DrSymmetry(6), DrSymmetry(7), DrSymmetry(8), DrSymmetry(9), DrSymmetry(10), DrSymmetry(11), DrSymmetry(12), DrSymmetry(13), DrSymmetry(14), DrSymmetry(15)];
}

impl Symmetry for DrSymmetry {
    fn repr(self) -> usize {
        self.0 as usize
    }

    fn from_repr(n: usize) -> Self {
        DrSymmetry(n as u8)
    }

    fn get_all() -> impl Iterator<Item = Self> {
        Self::ARRAY.into_iter()
    }

    fn to_puzzle(self) -> CubieCube {
        let mut res = CubieCube::SOLVED;

        for _ in 0..self.rl2_count() {
            res = res.multiply_cube(SYM_RL2);
        }

        for _ in 0..self.f2_count() {
            res = res.multiply_cube(SYM_F2);
        }

        for _ in 0..self.u4_count() {
            res = res.multiply_cube(SYM_U4);
        }

        res
    }
}

/// An element of the set of symmetries of a cube that preserve domino reduction. This is generated
/// by:
/// - A 180 degree rotation around the F/B axis (aka F2)
/// - A 180 degree rotation around the U/D axis (aka U2)
/// - A reflection around the R-L slice (aka RL2)
// 0s bit is R-L
// 1s bit F/B
// 2s bit U/D
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct HalfSymmetry(u8);

impl HalfSymmetry {
    /// Returns the power of RL2 in the standard product notation of this symmetry.
    fn rl2_count(self) -> usize {
        (self.0 & 1) as usize
    }

    /// Returns the power of F2 in the standard product notation of this symmetry.
    fn f2_count(self) -> usize {
        (self.0 >> 1 & 1) as usize
    }

    /// Returns the power of U2 in the standard product notation of this symmetry.
    fn u2_count(self) -> usize {
        (self.0 >> 2 & 1) as usize
    }

    // lol
    /// An array of each symmetry
    #[rustfmt::skip]
    pub const ARRAY: [HalfSymmetry; 8] = [HalfSymmetry(0), HalfSymmetry(1), HalfSymmetry(2), HalfSymmetry(3), HalfSymmetry(4), HalfSymmetry(5), HalfSymmetry(6), HalfSymmetry(7)];
}

impl Symmetry for HalfSymmetry {
    fn repr(self) -> usize {
        self.0 as usize
    }

    fn from_repr(n: usize) -> Self {
        HalfSymmetry(n as u8)
    }

    fn get_all() -> impl Iterator<Item = Self> {
        Self::ARRAY.into_iter()
    }

    fn to_puzzle(self) -> CubieCube {
        let mut res = CubieCube::SOLVED;

        for _ in 0..self.rl2_count() {
            res = res.multiply_cube(SYM_RL2);
        }

        for _ in 0..self.f2_count() {
            res = res.multiply_cube(SYM_F2);
        }

        for _ in 0..self.u2_count() {
            res = res.multiply_cube(SYM_U4.multiply_cube(SYM_U4));
        }

        res
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use proptest::prelude::*;

    #[test]
    fn multiplication_correct() {
        let table = DrSymMultTable::generate();
        proptest!(|(sym1 in (0..16u8).prop_map(DrSymmetry), sym2 in (0..16u8).prop_map(DrSymmetry))| {
            assert_eq!(table.multiply(sym1, sym2).to_puzzle(), sym1.to_puzzle().multiply_cube(sym2.to_puzzle()));
        })
    }
}
