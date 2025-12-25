//! We give a general description of a coordinate, which is a type used to encode coset information
//! of a puzzle.

/// A coordinate type, encoding cosets of the puzzle P.
pub trait Coordinate<P>: Copy + Default + Eq {
    // TODO this API assumes that coord conversion doesn't require any additional data, perhaps
    // this should be changed
    /// Obtain the coordinate that corresponds to the given puzzle.
    fn from_puzzle(puzzle: &P) -> Self;

    // TODO should this be kept
    /// Determine whether the given coordinate represents a solved state
    fn solved(self) -> bool {
        self.repr() == 0
    }

    /// The number of possible coordinate states.
    fn count() -> usize;

    /// A representation of this coordinate as a usize, for use in table lookups.
    fn repr(self) -> usize;

    // TODO this might not be ideal it's not very type safe idk
    /// Convert the representation of a coordinate to the coordinate itself. We assume 0
    /// corresponds to the solved state.
    fn from_repr(n: usize) -> Self;
}

/// Gives the ability to set a coordinate onto a puzzle.
pub trait FromCoordinate<C>: Sized
where
    C: Coordinate<Self>,
{
    /// Modify the puzzle so that its coordinate for `C` is `coord`.
    fn set_coord(&mut self, coord: C);
}
