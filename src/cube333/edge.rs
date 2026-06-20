use super::{Face, StickerToPieceError, axis::Axis};
use crate::error::TryFromIntToEnumError;

// NOTE: these enum discriminants are assumed in unsafe code!
/// An enum for every edge piece location.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
#[repr(u8)]
pub enum Edge {
    UF = 0,
    UL = 1,
    UB = 2,
    UR = 3,
    DF = 4,
    DL = 5,
    DB = 6,
    DR = 7,
    FR = 8,
    FL = 9,
    BL = 10,
    BR = 11,
}

use Edge as E;

impl std::fmt::Display for Edge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            E::UF => write!(f, "UF"),
            E::UL => write!(f, "UL"),
            E::UB => write!(f, "UB"),
            E::UR => write!(f, "UR"),
            E::DF => write!(f, "DF"),
            E::DL => write!(f, "DL"),
            E::DB => write!(f, "DB"),
            E::DR => write!(f, "DR"),
            E::FR => write!(f, "FR"),
            E::FL => write!(f, "FL"),
            E::BL => write!(f, "BL"),
            E::BR => write!(f, "BR"),
        }
    }
}

impl Edge {
    pub(crate) const ARRAY: [Edge; 12] = [
        E::UF,
        E::UL,
        E::UB,
        E::UR,
        E::DF,
        E::DL,
        E::DB,
        E::DR,
        E::FR,
        E::FL,
        E::BL,
        E::BR,
    ];

    /// Determines whether this edge sits on the E slice.
    pub fn e_slice(&self) -> bool {
        matches!(self, E::FR | E::FL | E::BL | E::BR)
    }

    /// Determines whether this edge sits on the M slice.
    pub fn m_slice(&self) -> bool {
        matches!(self, E::UF | E::UB | E::DF | E::DB)
    }

    /// Determines whether this edge sits on the S slice.
    pub fn s_slice(&self) -> bool {
        matches!(self, E::UL | E::UR | E::DL | E::DR)
    }

    /// Apply a 120 degree clockwise rotation through the UFR and DBL corners to an edge
    pub fn apply_diag(self) -> Self {
        match self {
            Edge::UF => Edge::UR,
            Edge::UL => Edge::BR,
            Edge::UB => Edge::DR,
            Edge::UR => Edge::FR,
            Edge::DF => Edge::UL,
            Edge::DL => Edge::BL,
            Edge::DB => Edge::DL,
            Edge::DR => Edge::FL,
            Edge::FR => Edge::UF,
            Edge::FL => Edge::UB,
            Edge::BL => Edge::DB,
            Edge::BR => Edge::DF,
        }
    }

    /// Apply a y rotation to an edge
    pub fn apply_y(self) -> Self {
        match self {
            Edge::UF => Edge::UL,
            Edge::UL => Edge::UB,
            Edge::UB => Edge::UR,
            Edge::UR => Edge::UF,
            Edge::DF => Edge::DL,
            Edge::DL => Edge::DB,
            Edge::DB => Edge::DR,
            Edge::DR => Edge::DF,
            Edge::FR => Edge::FL,
            Edge::FL => Edge::BL,
            Edge::BL => Edge::BR,
            Edge::BR => Edge::FR,
        }
    }

    /// Apply a z2 to an edge
    pub fn apply_z2(self) -> Self {
        match self {
            Edge::UF => Edge::DF,
            Edge::UL => Edge::DR,
            Edge::UB => Edge::DB,
            Edge::UR => Edge::DL,
            Edge::DF => Edge::UF,
            Edge::DL => Edge::UR,
            Edge::DB => Edge::UB,
            Edge::DR => Edge::UL,
            Edge::FR => Edge::FL,
            Edge::FL => Edge::FR,
            Edge::BL => Edge::BR,
            Edge::BR => Edge::BL,
        }
    }

    /// Apply a reflection along the m slice to an edge
    pub fn apply_rl2(self) -> Self {
        match self {
            Edge::UF => Edge::UF,
            Edge::UL => Edge::UR,
            Edge::UB => Edge::UB,
            Edge::UR => Edge::UL,
            Edge::DF => Edge::DF,
            Edge::DL => Edge::DR,
            Edge::DB => Edge::DB,
            Edge::DR => Edge::DL,
            Edge::FR => Edge::FL,
            Edge::FL => Edge::FR,
            Edge::BL => Edge::BR,
            Edge::BR => Edge::BL,
        }
    }
}

impl From<Edge> for u8 {
    fn from(value: Edge) -> Self {
        value as u8
    }
}

impl TryFrom<u8> for Edge {
    type Error = TryFromIntToEnumError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(E::UF),
            1 => Ok(E::UL),
            2 => Ok(E::UB),
            3 => Ok(E::UR),
            4 => Ok(E::DF),
            5 => Ok(E::DL),
            6 => Ok(E::DB),
            7 => Ok(E::DR),
            8 => Ok(E::FR),
            9 => Ok(E::FL),
            10 => Ok(E::BL),
            11 => Ok(E::BR),
            _ => Err(TryFromIntToEnumError::OutOfBounds),
        }
    }
}

/// An enum to tell if an edge is flipped or not.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
#[repr(u8)]
pub enum EdgeFlip {
    Oriented = 0,
    Flipped = 1,
}

use EdgeFlip as EF;

impl From<EdgeFlip> for u8 {
    fn from(value: EdgeFlip) -> Self {
        value as u8
    }
}

impl TryFrom<u8> for EdgeFlip {
    type Error = TryFromIntToEnumError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(EF::Oriented),
            1 => Ok(EF::Flipped),
            _ => Err(TryFromIntToEnumError::OutOfBounds),
        }
    }
}

impl EdgeFlip {
    /// Flip an edge's orientation.
    #[inline]
    pub fn flip(self) -> EdgeFlip {
        match self {
            EdgeFlip::Oriented => EdgeFlip::Flipped,
            EdgeFlip::Flipped => EdgeFlip::Oriented,
        }
    }

    /// Flip an edge's orientation by some value.
    /// If `flip == EdgeFlip::Oriented`, do nothing to self.
    /// If `flip == EdgeFlip::Flipped`, flip self.
    #[inline]
    pub fn flip_by(self, flip: EdgeFlip) -> EdgeFlip {
        match flip {
            EdgeFlip::Oriented => self,
            EdgeFlip::Flipped => self.flip(),
        }
    }
}

/// An enum to represent every edge sticker position.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum EdgePos {
    UB,
    UR,
    UF,
    UL,
    LU,
    LF,
    LD,
    LB,
    FU,
    FR,
    FD,
    FL,
    RU,
    RB,
    RD,
    RF,
    BU,
    BL,
    BD,
    BR,
    DF,
    DR,
    DB,
    DL,
}

use EdgePos as EP;

impl EdgePos {
    pub(crate) fn flip(self) -> EdgePos {
        let (f1, f2) = self.into();
        (f2, f1).try_into().unwrap()
    }

    pub(crate) fn piece(self) -> Edge {
        match self {
            EP::UB => E::UB,
            EP::UR => E::UR,
            EP::UF => E::UF,
            EP::UL => E::UL,
            EP::LU => E::UL,
            EP::LF => E::FL,
            EP::LD => E::DL,
            EP::LB => E::BL,
            EP::FU => E::UF,
            EP::FR => E::FR,
            EP::FD => E::DF,
            EP::FL => E::FL,
            EP::RU => E::UR,
            EP::RB => E::BR,
            EP::RD => E::DR,
            EP::RF => E::FR,
            EP::BU => E::UB,
            EP::BL => E::BL,
            EP::BD => E::DB,
            EP::BR => E::BR,
            EP::DF => E::DF,
            EP::DR => E::DR,
            EP::DB => E::DB,
            EP::DL => E::DL,
        }
    }

    /// Returns the orientation of a position with respect to the F/B axis.
    pub fn fb_orientation(self) -> EdgeFlip {
        match self {
            EP::UB => EF::Oriented,
            EP::UR => EF::Oriented,
            EP::UF => EF::Oriented,
            EP::UL => EF::Oriented,
            EP::LU => EF::Flipped,
            EP::LF => EF::Flipped,
            EP::LD => EF::Flipped,
            EP::LB => EF::Flipped,
            EP::FU => EF::Flipped,
            EP::FR => EF::Oriented,
            EP::FD => EF::Flipped,
            EP::FL => EF::Oriented,
            EP::RU => EF::Flipped,
            EP::RB => EF::Flipped,
            EP::RD => EF::Flipped,
            EP::RF => EF::Flipped,
            EP::BU => EF::Flipped,
            EP::BL => EF::Oriented,
            EP::BD => EF::Flipped,
            EP::BR => EF::Oriented,
            EP::DF => EF::Oriented,
            EP::DR => EF::Oriented,
            EP::DB => EF::Oriented,
            EP::DL => EF::Oriented,
        }
    }

    /// Returns the orientation of a position with respect to the L/R axis.
    pub fn lr_orientation(self) -> EdgeFlip {
        match self {
            EdgePos::UB => EF::Oriented,
            EdgePos::UR => EF::Oriented,
            EdgePos::UF => EF::Oriented,
            EdgePos::UL => EF::Oriented,
            EdgePos::LU => EF::Flipped,
            EdgePos::LF => EF::Oriented,
            EdgePos::LD => EF::Flipped,
            EdgePos::LB => EF::Oriented,
            EdgePos::FU => EF::Flipped,
            EdgePos::FR => EF::Flipped,
            EdgePos::FD => EF::Flipped,
            EdgePos::FL => EF::Flipped,
            EdgePos::RU => EF::Flipped,
            EdgePos::RB => EF::Oriented,
            EdgePos::RD => EF::Flipped,
            EdgePos::RF => EF::Oriented,
            EdgePos::BU => EF::Flipped,
            EdgePos::BL => EF::Flipped,
            EdgePos::BD => EF::Flipped,
            EdgePos::BR => EF::Flipped,
            EdgePos::DF => EF::Oriented,
            EdgePos::DR => EF::Oriented,
            EdgePos::DB => EF::Oriented,
            EdgePos::DL => EF::Oriented,
        }
    }

    /// Returns the orientation of a position with respect to the F/B axis.
    pub fn ud_orientation(self) -> EdgeFlip {
        match self {
            EdgePos::UB => EF::Flipped,
            EdgePos::UR => EF::Oriented,
            EdgePos::UF => EF::Flipped,
            EdgePos::UL => EF::Oriented,
            EdgePos::LU => EF::Flipped,
            EdgePos::LF => EF::Flipped,
            EdgePos::LD => EF::Flipped,
            EdgePos::LB => EF::Flipped,
            EdgePos::FU => EF::Oriented,
            EdgePos::FR => EF::Oriented,
            EdgePos::FD => EF::Oriented,
            EdgePos::FL => EF::Oriented,
            EdgePos::RU => EF::Flipped,
            EdgePos::RB => EF::Flipped,
            EdgePos::RD => EF::Flipped,
            EdgePos::RF => EF::Flipped,
            EdgePos::BU => EF::Oriented,
            EdgePos::BL => EF::Oriented,
            EdgePos::BD => EF::Oriented,
            EdgePos::BR => EF::Oriented,
            EdgePos::DF => EF::Flipped,
            EdgePos::DR => EF::Oriented,
            EdgePos::DB => EF::Flipped,
            EdgePos::DL => EF::Oriented,
        }
    }

    /// Returns the orientation of a position with respect to the given axis.
    pub fn axis_orientation(self, axis: Axis) -> EdgeFlip {
        match axis {
            Axis::FB => self.fb_orientation(),
            Axis::LR => self.lr_orientation(),
            Axis::UD => self.ud_orientation(),
        }
    }
}

impl From<Edge> for EdgePos {
    fn from(value: Edge) -> Self {
        match value {
            Edge::UF => EP::UF,
            Edge::UL => EP::UL,
            Edge::UB => EP::UB,
            Edge::UR => EP::UR,
            Edge::DF => EP::DF,
            Edge::DL => EP::DL,
            Edge::DB => EP::DB,
            Edge::DR => EP::DR,
            Edge::FR => EP::FR,
            Edge::FL => EP::FL,
            Edge::BL => EP::BL,
            Edge::BR => EP::BR,
        }
    }
}

impl From<(Edge, EdgeFlip)> for EdgePos {
    fn from(value: (Edge, EdgeFlip)) -> Self {
        match value {
            (E::UF, EF::Oriented) => EP::UF,
            (E::UF, EF::Flipped) => EP::FU,
            (E::UL, EF::Oriented) => EP::UL,
            (E::UL, EF::Flipped) => EP::LU,
            (E::UB, EF::Oriented) => EP::UB,
            (E::UB, EF::Flipped) => EP::BU,
            (E::UR, EF::Oriented) => EP::UR,
            (E::UR, EF::Flipped) => EP::RU,
            (E::DF, EF::Oriented) => EP::DF,
            (E::DF, EF::Flipped) => EP::FD,
            (E::DL, EF::Oriented) => EP::DL,
            (E::DL, EF::Flipped) => EP::LD,
            (E::DB, EF::Oriented) => EP::DB,
            (E::DB, EF::Flipped) => EP::BD,
            (E::DR, EF::Oriented) => EP::DR,
            (E::DR, EF::Flipped) => EP::RD,
            (E::FR, EF::Oriented) => EP::FR,
            (E::FR, EF::Flipped) => EP::RF,
            (E::FL, EF::Oriented) => EP::FL,
            (E::FL, EF::Flipped) => EP::LF,
            (E::BL, EF::Oriented) => EP::BL,
            (E::BL, EF::Flipped) => EP::LB,
            (E::BR, EF::Oriented) => EP::BR,
            (E::BR, EF::Flipped) => EP::RB,
        }
    }
}

impl TryFrom<(Face, Face)> for EdgePos {
    type Error = StickerToPieceError;

    fn try_from(value: (Face, Face)) -> Result<EdgePos, Self::Error> {
        use Face as F;
        match value {
            (F::U, F::L) => Ok(EP::UL),
            (F::U, F::F) => Ok(EP::UF),
            (F::U, F::R) => Ok(EP::UR),
            (F::U, F::B) => Ok(EP::UB),
            (F::L, F::U) => Ok(EP::LU),
            (F::L, F::F) => Ok(EP::LF),
            (F::L, F::B) => Ok(EP::LB),
            (F::L, F::D) => Ok(EP::LD),
            (F::F, F::U) => Ok(EP::FU),
            (F::F, F::L) => Ok(EP::FL),
            (F::F, F::R) => Ok(EP::FR),
            (F::F, F::D) => Ok(EP::FD),
            (F::R, F::U) => Ok(EP::RU),
            (F::R, F::F) => Ok(EP::RF),
            (F::R, F::B) => Ok(EP::RB),
            (F::R, F::D) => Ok(EP::RD),
            (F::B, F::U) => Ok(EP::BU),
            (F::B, F::L) => Ok(EP::BL),
            (F::B, F::R) => Ok(EP::BR),
            (F::B, F::D) => Ok(EP::BD),
            (F::D, F::L) => Ok(EP::DL),
            (F::D, F::F) => Ok(EP::DF),
            (F::D, F::R) => Ok(EP::DR),
            (F::D, F::B) => Ok(EP::DB),
            _ => Err(StickerToPieceError::InvalidPiece),
        }
    }
}

impl From<EdgePos> for (Face, Face) {
    fn from(value: EdgePos) -> Self {
        use Face as F;
        match value {
            EP::UB => (F::U, F::B),
            EP::UR => (F::U, F::R),
            EP::UF => (F::U, F::F),
            EP::UL => (F::U, F::L),
            EP::LU => (F::L, F::U),
            EP::LF => (F::L, F::F),
            EP::LD => (F::L, F::D),
            EP::LB => (F::L, F::B),
            EP::FU => (F::F, F::U),
            EP::FR => (F::F, F::R),
            EP::FD => (F::F, F::D),
            EP::FL => (F::F, F::L),
            EP::RU => (F::R, F::U),
            EP::RB => (F::R, F::B),
            EP::RD => (F::R, F::D),
            EP::RF => (F::R, F::F),
            EP::BU => (F::B, F::U),
            EP::BL => (F::B, F::L),
            EP::BD => (F::B, F::D),
            EP::BR => (F::B, F::R),
            EP::DF => (F::D, F::F),
            EP::DR => (F::D, F::R),
            EP::DB => (F::D, F::B),
            EP::DL => (F::D, F::L),
        }
    }
}

impl From<EdgePos> for usize {
    fn from(value: EdgePos) -> Self {
        match value {
            EP::UB => 0,
            EP::UR => 1,
            EP::UF => 2,
            EP::UL => 3,
            EP::LU => 4,
            EP::LF => 5,
            EP::LD => 6,
            EP::LB => 7,
            EP::FU => 8,
            EP::FR => 9,
            EP::FD => 10,
            EP::FL => 11,
            EP::RU => 12,
            EP::RB => 13,
            EP::RD => 14,
            EP::RF => 15,
            EP::BU => 16,
            EP::BL => 17,
            EP::BD => 18,
            EP::BR => 19,
            EP::DF => 20,
            EP::DR => 21,
            EP::DB => 22,
            EP::DL => 23,
        }
    }
}

impl From<EdgePos> for Face {
    fn from(value: EdgePos) -> Self {
        use Face as F;
        match value {
            EP::UB => F::U,
            EP::UR => F::U,
            EP::UF => F::U,
            EP::UL => F::U,
            EP::LU => F::L,
            EP::LF => F::L,
            EP::LD => F::L,
            EP::LB => F::L,
            EP::FU => F::F,
            EP::FR => F::F,
            EP::FD => F::F,
            EP::FL => F::F,
            EP::RU => F::R,
            EP::RB => F::R,
            EP::RD => F::R,
            EP::RF => F::R,
            EP::BU => F::B,
            EP::BL => F::B,
            EP::BD => F::B,
            EP::BR => F::B,
            EP::DF => F::D,
            EP::DR => F::D,
            EP::DB => F::D,
            EP::DL => F::D,
        }
    }
}
