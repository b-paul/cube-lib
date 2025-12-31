use super::CubieCube;
use crate::moves::{Cancellation, MoveSequence};

#[cfg(test)]
use proptest_derive::Arbitrary;

/// Represents each type of move. Note that the `Move` struct uses this variable along with a
/// counter to represents move such as R2 or U'.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(test, derive(Arbitrary))]
pub enum Move333Type {
    /// Right
    R,
    /// Left
    L,
    /// Up
    U,
    /// Down
    D,
    /// Front
    F,
    /// Back
    B,
}

impl Move333Type {
    /// The move type on the face opposite to the given one.
    pub fn opposite(self) -> Move333Type {
        match self {
            Move333Type::R => Move333Type::L,
            Move333Type::L => Move333Type::R,
            Move333Type::U => Move333Type::D,
            Move333Type::D => Move333Type::U,
            Move333Type::F => Move333Type::B,
            Move333Type::B => Move333Type::F,
        }
    }
}

/// Stores a move type and counter. An anti-clockwise move will have a count of 3.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(test, derive(Arbitrary))]
#[allow(missing_docs)]
pub struct Move333 {
    pub ty: Move333Type,
    #[cfg_attr(test, proptest(strategy = "1..=3u8"))]
    pub count: u8,
}

impl crate::moves::Move for Move333 {
    fn inverse(self) -> Self {
        Self {
            ty: self.ty,
            count: 4u8.wrapping_sub(self.count).rem_euclid(4),
        }
    }

    fn commutes_with(&self, b: &Self) -> bool {
        use Move333Type as MT;
        match self.ty {
            MT::R | MT::L => [MT::R, MT::L].contains(&b.ty),
            MT::U | MT::D => [MT::U, MT::D].contains(&b.ty),
            MT::F | MT::B => [MT::F, MT::B].contains(&b.ty),
        }
    }

    fn cancel(self, b: Self) -> Cancellation<Self> {
        if self.ty == b.ty {
            let count = (self.count + b.count) % 4;
            if count == 0 {
                Cancellation::NoMove
            } else {
                Cancellation::OneMove(Move333 { ty: self.ty, count })
            }
        } else {
            Cancellation::TwoMove(self, b)
        }
    }
}

// I don't want to have the default derive debug for this!
impl std::fmt::Debug for Move333 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.count {
            1 => write!(f, "{:?}", self.ty),
            3 => write!(f, "{:?}'", self.ty),
            _ => write!(f, "{:?}{}", self.ty, self.count),
        }
    }
}

/// A trait to classify a type as a move generator. A move generator is a set which can be used to
/// generate a set, i.e. find every combination of moves using moves in the move generator to find
/// unique states.
pub trait MoveGenerator {
    /// The amount of moves that are available in the moveset.
    const SIZE: usize;
    /// A list of all valid moves. The index of a move in this list will be the same index used
    /// when accessing the move table.
    const MOVE_LIST: &'static [Move333];
}

impl From<Move333> for usize {
    fn from(mv: Move333) -> usize {
        (mv.count as usize - 1) * 6 + mv.ty as usize
    }
}

/// Create a move by specifying a move type and move count. Note that you do not need to specify
/// for example Move333Type::R, you only need to specify R. (TODO this might not be a good idea).
#[macro_export]
macro_rules! mv {
    ($ty:ident, $count: expr) => {
        Move333 {
            ty: Move333Type::$ty,
            count: $count,
        }
    };
}

/// Type for Half Turn Metric
pub struct Htm;

impl MoveGenerator for Htm {
    const SIZE: usize = 18;
    const MOVE_LIST: &'static [Move333] = &[
        mv!(R, 1),
        mv!(L, 1),
        mv!(U, 1),
        mv!(D, 1),
        mv!(F, 1),
        mv!(B, 1),
        mv!(R, 2),
        mv!(L, 2),
        mv!(U, 2),
        mv!(D, 2),
        mv!(F, 2),
        mv!(B, 2),
        mv!(R, 3),
        mv!(L, 3),
        mv!(U, 3),
        mv!(D, 3),
        mv!(F, 3),
        mv!(B, 3),
    ];
}

impl From<Move333Type> for usize {
    fn from(mv: Move333Type) -> Self {
        match mv {
            Move333Type::R => 0,
            Move333Type::L => 1,
            Move333Type::U => 2,
            Move333Type::D => 3,
            Move333Type::F => 4,
            Move333Type::B => 5,
        }
    }
}

const CO_OFFSETS: [[u8; 8]; 6] = [
    [2, 0, 0, 1, 1, 0, 0, 2],
    [0, 1, 2, 0, 0, 2, 1, 0],
    [0; 8],
    [0; 8],
    [1, 2, 0, 0, 2, 1, 0, 0],
    [0, 0, 1, 2, 0, 0, 2, 1],
];
const CP_OFFSETS: [[u8; 8]; 6] = [
    [4, 1, 2, 0, 7, 5, 6, 3],
    [0, 2, 6, 3, 4, 1, 5, 7],
    [3, 0, 1, 2, 4, 5, 6, 7],
    [0, 1, 2, 3, 5, 6, 7, 4],
    [1, 5, 2, 3, 0, 4, 6, 7],
    [0, 1, 3, 7, 4, 5, 2, 6],
];
const EO_OFFSETS: [[u8; 12]; 6] = [
    [0; 12],
    [0; 12],
    [0; 12],
    [0; 12],
    [1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0],
    [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1],
];
const EP_OFFSETS: [[u8; 12]; 6] = [
    [0, 1, 2, 8, 4, 5, 6, 11, 7, 9, 10, 3],
    [0, 10, 2, 3, 4, 9, 6, 7, 8, 1, 5, 11],
    [3, 0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11],
    [0, 1, 2, 3, 5, 6, 7, 4, 8, 9, 10, 11],
    [9, 1, 2, 3, 8, 5, 6, 7, 0, 4, 10, 11],
    [0, 1, 11, 3, 4, 5, 10, 7, 8, 9, 2, 6],
];

impl CubieCube {
    /// Apply an algorithm to a cube
    pub fn make_moves(self, mvs: MoveSequence<Move333>) -> CubieCube {
        mvs.0.into_iter().fold(self, |c, m| c.make_move(m))
    }

    // This function doesn't really need to be fast since coordinates exist
    /// Apply a move to a cube.
    pub fn make_move(self, mv: Move333) -> CubieCube {
        (0..mv.count).fold(self, |c, _| c.make_move_type(mv.ty))
    }

    // TODO make this const please that would be very handy :)

    /// Make a single application of a move
    pub fn make_move_type(self, mv: Move333Type) -> CubieCube {
        let co_offsets = CO_OFFSETS[mv as usize];
        let cp_offsets = CP_OFFSETS[mv as usize];
        let eo_offsets = EO_OFFSETS[mv as usize];
        let ep_offsets = EP_OFFSETS[mv as usize];

        let selfco: [u8; 8] = self.co.map(|t| t.into());
        let selfcp: [u8; 8] = self.cp.map(|t| t.into());
        let selfeo: [u8; 12] = self.eo.map(|t| t.into());
        let selfep: [u8; 12] = self.ep.map(|t| t.into());

        let mut co = [0; 8];
        let mut cp = [0; 8];
        let mut eo = [0; 12];
        let mut ep = [0; 12];

        for i in 0..8 {
            co[i] = (selfco[cp_offsets[i] as usize] + co_offsets[i]) % 3;
            cp[i] = selfcp[cp_offsets[i] as usize];
        }

        for i in 0..12 {
            eo[i] = (selfeo[ep_offsets[i] as usize] + eo_offsets[i]) % 2;
            ep[i] = selfep[ep_offsets[i] as usize];
        }

        let co = co.map(|n| n.try_into().unwrap());
        let cp = cp.map(|n| n.try_into().unwrap());
        let eo = eo.map(|n| n.try_into().unwrap());
        let ep = ep.map(|n| n.try_into().unwrap());

        CubieCube { co, cp, eo, ep }
    }

    /// Multiply two cube states in the Rubik's cube group.
    pub fn multiply_cube(self, other: CubieCube) -> CubieCube {
        let mut result = CubieCube::SOLVED;

        for i in 0..8 {
            let oa = self.co[other.cp[i] as usize];
            let ob = other.co[i];
            let o = oa.twist_by(ob);
            result.co[i] = o;
            result.cp[i] = self.cp[other.cp[i] as usize];
        }

        for i in 0..12 {
            let oa = self.eo[other.ep[i] as usize];
            let ob = other.eo[i];
            let o = oa.flip_by(ob);
            result.eo[i] = o;
            result.ep[i] = self.ep[other.ep[i] as usize];
        }

        result
    }

    /// Get the inverse in the Rubik's cube group.
    pub fn inverse(self) -> CubieCube {
        let mut result = CubieCube::SOLVED;

        for i in 0..8 {
            result.co[self.cp[i] as usize] = self.co[i].inverse();
            result.cp[self.cp[i] as usize] = (i as u8).try_into().unwrap();
        }

        for i in 0..12 {
            result.eo[self.ep[i] as usize] = self.eo[i];
            result.ep[self.ep[i] as usize] = (i as u8).try_into().unwrap();
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn r_loop() {
        let mut cube = CubieCube::SOLVED;
        for _ in 0..4 {
            cube = cube.make_move(Move333 {
                ty: Move333Type::B,
                count: 1,
            });
        }
        assert_eq!(cube, CubieCube::SOLVED);
    }

    use proptest::collection::vec;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn cancel_same_moves(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence)) {
            let cancelled = mvs.clone().cancel();
            assert!(cancelled.len() <= mvs.len());
            assert_eq!(CubieCube::SOLVED.make_moves(mvs), CubieCube::SOLVED.make_moves(cancelled));
        }

        #[test]
        fn invert_identity(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence)) {
            let cancelled = mvs.clone().cancel();
            assert_eq!(CubieCube::SOLVED.make_moves(mvs.clone()).make_moves(mvs.inverse()), CubieCube::SOLVED);
            assert!(cancelled.clone().append(cancelled.clone().inverse()).cancel().is_empty());
        }

        #[test]
        fn cancel_idemotent(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence)) {
            let cancelled = mvs.clone().cancel();
            assert_eq!(cancelled.clone().cancel(), cancelled);
        }

        #[test]
        fn inverse_apply(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence)) {
            // TODO use real random state for this proptest! doing random moves is silly!
            let fake_random_state = CubieCube::SOLVED.make_moves(mvs);
            assert_eq!(CubieCube::SOLVED, fake_random_state.clone().multiply_cube(fake_random_state.clone().inverse()));
            assert_eq!(CubieCube::SOLVED, fake_random_state.clone().inverse().multiply_cube(fake_random_state.clone()));
        }
    }
}
