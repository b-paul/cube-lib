use super::{Corner, Edge};

/// An element of the group of symmetries of a cube.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CubeSymmetry {
    bitfield: u8,
}

impl CubeSymmetry {
    fn diag3(self) -> u8 {
        self.bitfield >> 4
    }
    fn u4(self) -> u8 {
        (self.bitfield >> 2) & 3
    }
    fn f2(self) -> u8 {
        (self.bitfield >> 1) & 1
    }
    fn rl2(self) -> u8 {
        self.bitfield & 1
    }

    /// An iterator over all symmetries of a cube.
    pub fn all() -> impl Iterator<Item = Self> {
        (0..48).map(|bitfield| CubeSymmetry { bitfield })
    }

    /// Apply a symmetry to an edge position.
    pub fn transform_ep(self, e: Edge) -> Edge {
        let diag = (0..self.diag3()).fold(e, |e, _| e.apply_diag());
        let u4 = (0..self.u4()).fold(diag, |e, _| e.apply_y());
        let f2 = (0..self.f2()).fold(u4, |e, _| e.apply_z2());
        let rl2 = (0..self.rl2()).fold(f2, |e, _| e.apply_rl2());
        rl2
    }

    /// Apply a symmetry to a corner position.
    pub fn transform_cp(self, c: Corner) -> Corner {
        let diag = (0..self.diag3()).fold(c, |c, _| c.apply_diag());
        let u4 = (0..self.u4()).fold(diag, |c, _| c.apply_y());
        let f2 = (0..self.f2()).fold(u4, |c, _| c.apply_z2());
        let rl2 = (0..self.rl2()).fold(f2, |c, _| c.apply_rl2());
        rl2
    }
}

// TODO write tests
