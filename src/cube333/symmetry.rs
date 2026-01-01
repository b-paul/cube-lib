use super::CubieCube;

/// A subgroup of the symmetry group of the cube.
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
    pub fn apply_symmetry<S: Symmetry>(self, sym: S) -> CubieCube {
        sym.apply(self)
    }

    /// Obtain the cube given by conjugating by some symmetry. We conjugate in the order S C S^-1
    pub fn conjugate_symmetry<S: Symmetry>(self, sym: S) -> CubieCube {
        sym.conjugate(self)
    }

    /// Obtain the cube given by conjugating by the inverse of some symmetry. We hence conjugate in
    /// the order S^-1 C S
    pub fn conjugate_inverse_symmetry<S: Symmetry>(self, sym: S) -> CubieCube {
        sym.conjugate_inverse(self)
    }
}
