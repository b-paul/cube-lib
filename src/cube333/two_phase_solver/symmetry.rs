//! Implements symmetries for the `CubieCube` and symmetry tables for use in move table generation.

use super::move_tables::SubMove;
use crate::cube333::{Corner as C, CornerTwist as CT, CubieCube, Edge as E, EdgeFlip as EF};

use std::marker::PhantomData;

pub trait Symmetry: Copy + Default + Eq {
    /// A representation of this symmetry as a usize, for use in table lookups.
    fn repr(self) -> usize;

    /// Convert the representation of a symmetry to the symmetry itself. We assume 0 corresponds to
    /// the identity symmetry.
    fn from_repr(n: usize) -> Self;

    /// Iterator over every symmetry in order of representation
    fn get_all() -> impl Iterator<Item = Self>;

    /// Apply this symmetry to the given puzzle, written P S
    fn apply(&self, cube: CubieCube) -> CubieCube;

    /// Apply the inverse of this symmetry to the given puzzle, written P S^-1
    fn apply_inverse(&self, cube: CubieCube) -> CubieCube;

    /// Conjugate the given puzzle by this symmetry, written S P S^-1
    fn conjugate(&self, cube: CubieCube) -> CubieCube {
        self.apply_inverse(self.apply(CubieCube::SOLVED).multiply_cube(cube))
    }

    /// Conjugate the given puzzle by the inverse of this symmetry, written S^-1 P S^
    fn conjugate_inverse(&self, cube: CubieCube) -> CubieCube {
        self.apply(self.apply_inverse(CubieCube::SOLVED).multiply_cube(cube))
    }
}

impl CubieCube {
    /// Obtain the cube given by applying some symmetry
    pub(super) fn apply_symmetry<S: Symmetry>(self, sym: S) -> CubieCube {
        sym.apply(self)
    }

    /// Obtain the cube given by conjugating by some symmetry. We conjugate in the order S C S^-1
    pub(super) fn conjugate_symmetry<S: Symmetry>(self, sym: S) -> CubieCube {
        sym.conjugate(self)
    }

    /// Obtain the cube given by conjugating by the inverse of some symmetry. We hence conjugate in
    /// the order S^-1 C S
    pub(super) fn conjugate_inverse_symmetry<S: Symmetry>(self, sym: S) -> CubieCube {
        sym.conjugate_inverse(self)
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

        let cubie_syms: [_; COUNT] = from_fn(|n| S::from_repr(n).apply(CubieCube::SOLVED));

        let table = from_fn(|a| {
            from_fn(|b| {
                let a = S::from_repr(a);
                let b = S::from_repr(b);
                let c = a
                    .apply(CubieCube::SOLVED)
                    .multiply_cube(b.apply(CubieCube::SOLVED));
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

/// A table of conjugates of moves by symmetries i.e. we identify moves corresponding to S^-1 M S.
/// We use an inverse conjugate to the usual convention of this repository as it is what is needed
/// for the symmetry move table.
pub struct SymMoveConjTable<S: Symmetry, M: SubMove, const SYMS: usize, const MOVES: usize> {
    table: [[M; MOVES]; SYMS],
    _phantom: PhantomData<S>,
}

impl<S: Symmetry, M: SubMove, const SYMS: usize, const MOVES: usize>
    SymMoveConjTable<S, M, SYMS, MOVES>
{
    /// Generate the table
    pub fn generate() -> Self {
        use std::array::from_fn;

        let table = from_fn(|s| {
            from_fn(|m| {
                let s = S::from_repr(s);
                let m = M::MOVE_LIST[m];

                let c = s.conjugate(CubieCube::SOLVED.make_move(m.into_move()));

                M::MOVE_LIST
                    .iter()
                    .filter_map(|&m2| {
                        (c.clone().make_move(m2.into_move()) == CubieCube::SOLVED).then_some(m2.inverse())
                    })
                    .next()
                    .expect("Moves should have conjugates in each symmetry")
            })
        });

        SymMoveConjTable { table, _phantom: PhantomData }
    }

    /// Determine the move corresponding to S^-1 M S given M and S.
    pub fn conjugate(&self, m: M, s: S) -> M {
        self.table[s.repr()][m.index()]
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

/// A cube that, when multiplied, almost applies the RL2 symmetry, but additionally the corner
/// orientations must be inverted (clockwise and anticlockwise swapped).
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

    fn apply(&self, mut cube: CubieCube) -> CubieCube {
        for _ in 0..self.rl2_count() {
            cube = cube.multiply_cube(SYM_RL2);
            cube.co = cube.co.map(|c| c.inverse());
        }

        for _ in 0..self.f2_count() {
            cube = cube.multiply_cube(SYM_F2);
        }

        for _ in 0..self.u4_count() {
            cube = cube.multiply_cube(SYM_U4);
        }

        cube
    }

    fn apply_inverse(&self, mut cube: CubieCube) -> CubieCube {
        for _ in 0..((4 - self.u4_count()) % 4) {
            cube = cube.multiply_cube(SYM_U4);
        }

        for _ in 0..self.f2_count() {
            cube = cube.multiply_cube(SYM_F2);
        }

        for _ in 0..self.rl2_count() {
            cube = cube.multiply_cube(SYM_RL2);
            cube.co = cube.co.map(|c| c.inverse());
        }

        cube
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

    fn apply(&self, mut cube: CubieCube) -> CubieCube {
        for _ in 0..self.rl2_count() {
            cube = cube.multiply_cube(SYM_RL2);
            cube.co = cube.co.map(|c| c.inverse());
        }

        for _ in 0..self.f2_count() {
            cube = cube.multiply_cube(SYM_F2);
        }

        for _ in 0..self.u2_count() {
            cube = cube.multiply_cube(SYM_U4.multiply_cube(SYM_U4));
        }

        cube
    }

    fn apply_inverse(&self, mut cube: CubieCube) -> CubieCube {
        for _ in 0..self.u2_count() {
            cube = cube.multiply_cube(SYM_U4.multiply_cube(SYM_U4));
        }

        for _ in 0..self.f2_count() {
            cube = cube.multiply_cube(SYM_F2);
        }

        for _ in 0..self.rl2_count() {
            cube = cube.multiply_cube(SYM_RL2);
            cube.co = cube.co.map(|c| c.inverse());
        }

        cube
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::cube333::moves::Move333;
    use crate::moves::MoveSequence;

    use proptest::collection::vec;
    use proptest::prelude::*;

    fn check_multiplication_correct<S: Symmetry + std::fmt::Debug, const COUNT: usize>() {
        let table = SymMultTable::<S, COUNT>::generate();
        proptest!(|(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence))| {
            let cube = CubieCube::SOLVED.make_moves(mvs);
            for sym1 in S::get_all() {
                for sym2 in S::get_all() {
                    assert_eq!(
                        table.multiply(sym1, sym2).apply(cube.clone()),
                        sym2.apply(sym1.apply(cube.clone())),
                        "{sym1:?} {sym2:?} {:?}", table.multiply(sym1, sym2),
                    );
                    assert_eq!(
                        table.multiply(sym1, sym2).apply_inverse(cube.clone()),
                        sym1.apply_inverse(sym2.apply_inverse(cube.clone())),
                        "{sym1:?} {sym2:?} {:?}", table.multiply(sym1, sym2),
                    );
                    assert_eq!(
                        table.multiply(sym1, sym2).conjugate(cube.clone()),
                        sym1.conjugate(sym2.conjugate(cube.clone())),
                        "{sym1:?} {sym2:?} {:?}", table.multiply(sym1, sym2),
                    );
                }
            }
        });
    }

    #[test]
    fn multiplication_correct() {
        check_multiplication_correct::<DrSymmetry, 16>();
        check_multiplication_correct::<HalfSymmetry, 8>();
    }
}
