use super::{Corner, CornerTwist, CubieCube, Edge, EdgeFlip};
use crate::coord::{Coordinate, FromCoordinate};

/// A coordinate representation of the corner orientation of a cube with respect to the U/F faces.
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct COCoord(u16);

/// A coordinate representation of the corner permutation of a cube with respect to the U/F faces.
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct CPCoord(u16);

/// A coordinate representation of the edge orientation of a cube with respect to the U/F faces.
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct EOCoord(u16);

/// A coordinate representation of the edge permutation of a cube with respect to the U/F faces.
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct EPCoord(u32);

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

    fn from_repr(n: usize) -> Self {
        COCoord(n as u16)
    }
}

impl FromCoordinate<COCoord> for CubieCube {
    fn set_coord(&mut self, coord: COCoord) {
        let mut first = CornerTwist::Oriented;
        let mut n = coord.0;

        for i in (1..8).rev() {
            self.co[i] = match n % 3 {
                0 => CornerTwist::Oriented,
                1 => {
                    first = first.anticlockwise();
                    CornerTwist::Clockwise
                }
                2 => {
                    first = first.clockwise();
                    CornerTwist::AntiClockwise
                }
                _ => unreachable!(),
            };
            n /= 3;
        }

        self.co[0] = first;
    }
}

impl Coordinate<CubieCube> for CPCoord {
    fn from_puzzle(puzzle: &CubieCube) -> Self {
        CPCoord(to_p_coord::<8>(&puzzle.cp.map(|n| n.into())) as u16)
    }

    fn count() -> usize {
        40320
    }

    fn repr(self) -> usize {
        self.0 as usize
    }

    fn from_repr(n: usize) -> Self {
        CPCoord(n as u16)
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

    fn from_repr(n: usize) -> Self {
        EOCoord(n as u16)
    }
}

impl FromCoordinate<EOCoord> for CubieCube {
    fn set_coord(&mut self, coord: EOCoord) {
        let mut first = EdgeFlip::Oriented;
        let mut n = coord.0;

        for i in (1..12).rev() {
            self.eo[i] = match n % 2 {
                0 => EdgeFlip::Oriented,
                1 => {
                    first = first.flip();
                    EdgeFlip::Flipped
                }
                _ => unreachable!(),
            };
            n /= 2;
        }

        self.eo[0] = first;
    }
}

impl Coordinate<CubieCube> for EPCoord {
    fn from_puzzle(puzzle: &CubieCube) -> Self {
        EPCoord(to_p_coord::<12>(&puzzle.ep.map(|n| n.into())))
    }

    fn count() -> usize {
        // a lot
        479001600
    }

    fn repr(self) -> usize {
        self.0 as usize
    }

    fn from_repr(n: usize) -> Self {
        EPCoord(n as u32)
    }
}

/// Implementation of a coord cube, representing pieces using coordinates, which are values which
/// are isomorphic to arrays represented in a cubie cube.
#[derive(Debug, PartialEq, Eq)]
pub struct CoordCube {
    co: COCoord,
    cp: CPCoord,
    eo: EOCoord,
    ep: EPCoord,
}

impl CoordCube {
    /// Convert a `CoordCube` to a `CubieCube`.
    pub fn to_cubie(mut self) -> CubieCube {
        let CubieCube {
            mut co,
            mut cp,
            mut eo,
            mut ep,
        } = CubieCube::SOLVED;

        let mut co_sum = 0;
        for i in (1..8).rev() {
            co[i] = ((self.co.0 % 3) as u8)
                .try_into()
                .expect("Somehow a mod 3 was out of bounds??");
            co_sum += 3 - (self.co.0 % 3) as u8;
            co_sum %= 3;
            self.co.0 /= 3;
        }
        co[0] = co_sum
            .try_into()
            .expect("Somehow a mod 3 was out of bounds??");

        let mut eo_sum = 0;
        for i in (1..12).rev() {
            eo[i] = ((self.eo.0 % 2) as u8)
                .try_into()
                .expect("Somehow a mod 2 was out of bounds??");
            eo_sum += 2 - (self.eo.0 % 2) as u8;
            eo_sum %= 2;
            self.eo.0 /= 2;
        }
        assert!(self.co.0 % 3 == self.co.0);
        eo[0] = eo_sum
            .try_into()
            .expect("Somehow a mod 2 was out of bounds??");

        let mut cp_orders = vec![0];
        for i in 1..8 {
            let n = self.cp.0 % (i + 1);
            cp_orders.push(n);
            self.cp.0 /= i + 1;
        }
        let mut corner_pieces = Corner::ARRAY.into_iter().collect::<Vec<_>>();
        for (i, n) in cp_orders.into_iter().enumerate().rev() {
            let j = i - n as usize;
            cp[i] = corner_pieces[j];
            corner_pieces.remove(j);
        }

        let mut ep_orders = vec![0];
        for i in 1..12 {
            let n = self.ep.0 % (i + 1);
            ep_orders.push(n);
            self.ep.0 /= i + 1;
        }
        let mut edge_pieces = Edge::ARRAY.into_iter().collect::<Vec<_>>();
        for (i, n) in ep_orders.into_iter().enumerate().rev() {
            let j = i - n as usize;
            ep[i] = edge_pieces[j];
            edge_pieces.remove(j);
        }

        CubieCube { co, cp, eo, ep }
    }

    /// The solved cube stored as a const.
    pub const SOLVED: Self = CoordCube {
        co: COCoord(0),
        cp: CPCoord(0),
        eo: EOCoord(0),
        ep: EPCoord(0),
    };
}

fn to_o_coord<const COUNT: usize, const STATES: u16>(arr: &[u8; COUNT]) -> u16 {
    arr.iter()
        .skip(1)
        .fold(0, |acc, &i| (acc * STATES) + i as u16)
}

// TODO this is kinda unreadable lol
fn to_p_coord<const COUNT: usize>(arr: &[u8; COUNT]) -> u32 {
    (1..COUNT).rev().fold(0, |acc, idx| {
        (acc * (idx + 1) as u32) + arr[0..idx].iter().filter(|&&x| x > arr[idx]).count() as u32
    })
}

/// Error for when converting from a `CubieCube` to a `CoordCube`.
/// Errors can occur in this case when the `CubieCube` is in an illegal state caused by an edge
/// flip, a corner twist, or permutation parity.
#[derive(Debug, PartialEq, Eq)]
pub struct CubieToCoordError {
    /// The edge flip coset we are in.
    pub eo: EdgeFlip,
    /// The corner twist coset we are in.
    pub co: CornerTwist,
    /// Whether we have permutation parity or not.
    pub perm: bool,
}

impl std::fmt::Display for CubieToCoordError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("a cube was in an illegal state")
    }
}
impl std::error::Error for CubieToCoordError {}

impl TryInto<CoordCube> for CubieCube {
    type Error = CubieToCoordError;

    fn try_into(self) -> Result<CoordCube, CubieToCoordError> {
        self.to_coord()
    }
}

impl CubieCube {
    /// Tries to convert a `CubieCube` to a `CoordCube`.
    pub fn to_coord(&self) -> Result<CoordCube, CubieToCoordError> {
        if self.illegal() {
            return Err(CubieToCoordError {
                eo: self.eo_parity(),
                co: self.co_parity(),
                perm: self.perm_parity(),
            });
        }

        let co = COCoord::from_puzzle(self);
        let cp = CPCoord::from_puzzle(self);
        let eo = EOCoord::from_puzzle(self);
        let ep = EPCoord::from_puzzle(self);

        Ok(CoordCube { co, cp, eo, ep })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cube333::{
        Corner, CornerTwist, CubieCube, Edge, EdgeFlip, StickerCube,
        coordcube::{CoordCube, CubieToCoordError},
        moves::{Move333, Move333Type},
    };
    use crate::mv;

    #[test]
    fn invertable_conversion() {
        assert_eq!(CubieCube::SOLVED.to_coord().unwrap(), CoordCube::SOLVED);
        assert_eq!(CoordCube::SOLVED.to_cubie(), CubieCube::SOLVED);
        let mut cube = CubieCube::SOLVED;
        for _ in 0..10 {
            cube = cube.make_move(mv!(U, 1));
            cube = cube.make_move(mv!(F, 1));
        }
        println!("{}", StickerCube::from(cube.clone()));
        println!(
            "{}",
            StickerCube::from(cube.clone().to_coord().unwrap().to_cubie())
        );
        assert_eq!(cube.to_coord().unwrap().to_cubie(), cube);
    }

    #[test]
    fn conversion_errors() {
        let mut twist = CubieCube::SOLVED;
        twist.co[0] = CornerTwist::Clockwise;
        assert_eq!(
            twist.to_coord(),
            Err(CubieToCoordError {
                eo: EdgeFlip::Oriented,
                co: CornerTwist::Clockwise,
                perm: false,
            })
        );
        twist.co[1] = CornerTwist::Clockwise;
        assert_eq!(
            twist.to_coord(),
            Err(CubieToCoordError {
                eo: EdgeFlip::Oriented,
                co: CornerTwist::AntiClockwise,
                perm: false,
            })
        );
        twist.co[2] = CornerTwist::AntiClockwise;
        assert_eq!(
            TryInto::<CoordCube>::try_into(twist.clone()),
            Err(CubieToCoordError {
                eo: EdgeFlip::Oriented,
                co: CornerTwist::Clockwise,
                perm: false,
            })
        );
        twist.co[2] = CornerTwist::Clockwise;
        assert!(twist.to_coord().is_ok());

        let mut flip = CubieCube::SOLVED;
        flip.eo[0] = EdgeFlip::Flipped;
        assert_eq!(
            flip.to_coord(),
            Err(CubieToCoordError {
                eo: EdgeFlip::Flipped,
                co: CornerTwist::Oriented,
                perm: false,
            })
        );
        flip.eo[1] = EdgeFlip::Flipped;
        assert!(flip.to_coord().is_ok());

        let mut swap = CubieCube::SOLVED;
        swap.ep[0] = Edge::UR;
        swap.ep[3] = Edge::UF;
        assert_eq!(
            swap.to_coord(),
            Err(CubieToCoordError {
                eo: EdgeFlip::Oriented,
                co: CornerTwist::Oriented,
                perm: true,
            })
        );
        assert_eq!(
            swap.to_coord().unwrap_err().to_string(),
            "a cube was in an illegal state"
        );
        swap.cp[0] = Corner::UBR;
        swap.cp[3] = Corner::UFR;
        assert!(swap.to_coord().is_ok());
    }

    use proptest::prelude::*;

    proptest! {
        // TODO this test is not good, it should take a *random state* as input to test that the
        // last piece is set correctly, but I haven't been bothered to make that yet...

        #[test]
        fn convert_invertible_co(c in (0..2187u16).prop_map(COCoord)) {
            let mut cube = CubieCube::SOLVED;
            cube.set_coord(c);
            assert_eq!(c, COCoord::from_puzzle(&cube));
        }

        #[test]
        fn convert_invertible_eo(c in (0..2048u16).prop_map(EOCoord)) {
            let mut cube = CubieCube::SOLVED;
            cube.set_coord(c);
            assert_eq!(c, EOCoord::from_puzzle(&cube));
        }
    }
}
