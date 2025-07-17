//! We give a general description of a coordinate, which is a type used to encode coset information
//! of a puzzle.

/// A coordinate type, encoding cosets of the puzzle P.
pub trait Coordinate<P>: Copy {
    /// Obtain the coordinate that corresponds to the given puzzle.
    fn from_puzzle(puzzle: &P) -> Self;

    /// The number of possible coordinate states.
    fn count() -> usize;

    /// A representation of this coordinate as a usize, for use, in table lookups.
    fn repr(self) -> usize;
}
