use super::{Corner, CornerTwist, CubieCube, Edge, EdgeFlip};

#[derive(Debug, Default, PartialEq, Eq, Copy, Clone)]
struct COCoord(u16);
#[derive(Debug, Default, PartialEq, Eq, Copy, Clone)]
struct CPCoord(u16);
#[derive(Debug, Default, PartialEq, Eq, Copy, Clone)]
struct EOCoord(u16);
#[derive(Debug, Default, PartialEq, Eq, Copy, Clone)]
struct EPCoord(u32);

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

        let co = COCoord(to_o_coord::<8, 3>(&self.co.map(|n| n.into())));
        let cp = CPCoord(to_p_coord::<8>(&self.cp.map(|n| n.into())) as u16);
        let eo = EOCoord(to_o_coord::<12, 2>(&self.eo.map(|n| n.into())));
        let ep = EPCoord(to_p_coord::<12>(&self.ep.map(|n| n.into())));

        Ok(CoordCube { co, cp, eo, ep })
    }
}

#[cfg(test)]
mod tests {
    use crate::cube333::{
        coordcube::{CoordCube, CubieToCoordError},
        moves::{Move333, Move333Type},
        Corner, CornerTwist, CubieCube, Edge, EdgeFlip, StickerCube,
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
}
