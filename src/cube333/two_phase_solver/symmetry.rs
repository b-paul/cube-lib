//! Implements symmetries for the `CubieCube` and symmetry tables for use in move table generation.

use crate::cube333::{Corner as C, CornerTwist as CT, CubieCube, Edge as E, EdgeFlip as EF};

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
#[derive(Debug, Default, PartialEq, Eq, Copy, Clone, Hash)]
pub struct DrSymmetry(u8);

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

    /// Obtain a CubieCube that applies this symmetry when multiplied.
    fn to_cubie(self) -> CubieCube {
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

impl CubieCube {
    /// Obtain the cube given by applying some symmetry
    fn apply_dr_symmetry(self, sym: DrSymmetry) -> CubieCube {
        self.multiply_cube(sym.to_cubie())
    }

    /// Obtain the cube given by conjugating by some symmetry. We conjugate in the order S C S^-1
    fn conjuate_dr_symmetry(self, sym: DrSymmetry) -> CubieCube {
        sym.to_cubie()
            .multiply_cube(self)
            .multiply_cube(sym.to_cubie().inverse())
    }
}

/// Multiplication table for the `DrSymmetry` group.
struct DrSymTable {
    table: [[DrSymmetry; 16]; 16],
}

impl DrSymTable {
    /// Generate the table
    fn generate() -> Self {
        use std::array::from_fn;

        let cubie_syms: [_; 16] = from_fn(|n| DrSymmetry(n as u8).to_cubie());

        let table = from_fn(|a| {
            from_fn(|b| {
                let a = DrSymmetry(a as u8);
                let b = DrSymmetry(b as u8);
                let c = a.to_cubie().multiply_cube(b.to_cubie());
                DrSymmetry(cubie_syms.iter().position(|d| &c == d).unwrap() as u8)
            })
        });

        DrSymTable { table }
    }

    /// Multiply two symmetries
    fn multiply(&self, a: DrSymmetry, b: DrSymmetry) -> DrSymmetry {
        self.table[a.0 as usize][b.0 as usize]
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use proptest::prelude::*;

    #[test]
    fn multiplication_correct() {
        let table = DrSymTable::generate();
        proptest!(|(sym1 in (0..16u8).prop_map(DrSymmetry), sym2 in (0..16u8).prop_map(DrSymmetry))| {
            assert_eq!(table.multiply(sym1, sym2).to_cubie(), sym1.to_cubie().multiply_cube(sym2.to_cubie()));
        })
    }
}
