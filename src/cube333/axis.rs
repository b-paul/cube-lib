//! Interpret properties of a cube relative to given axes (U/D, L/R, F/B).

// TODO proptest this properly after having nice rotation logic on the sticker cube

use super::{CornerTwist, CubieCube, EdgeFlip};

/// An axis of the cube.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Axis {
    /// Front-Back axis
    FB,
    /// Left-Right axis
    LR,
    /// Up-Down axis
    UD,
}

impl Axis {
    /// A list of all axes.
    pub const AXES: [Axis; 3] = [Axis::FB, Axis::LR, Axis::UD];
}

impl CubieCube {
    /// Get the corner orientation of this puzzle relative to a given axis i.e. treating that axis
    /// as the U/D faces. Orientations are still indexed by `Corner`.
    #[inline]
    pub fn axis_co(&self, axis: Axis) -> [CornerTwist; 8] {
        use std::mem::transmute;
        use std::simd::{Select, prelude::*};
        let co = u8x8::from_array(self.co.map(|o| o as u8));
        let cp = u8x8::from_array(self.cp.map(|p| p as u8));
        let orbs = u8x8::from_array([0, 1, 0, 1, 0, 1, 0, 1]);
        let same_orbits = orbs.simd_eq(cp & u8x8::splat(1));
        match axis {
            Axis::FB => {
                // if a corner is in its htr orbit, its FB orientation will be its UD orientation.
                // else, it will be an anticlockwise rotation away if its in the UFR orbit, or a
                // clockwise rotation away if its in the UFL orbit. We compute this rotation by
                // adding 1 or 2 mod 3
                let a = co + u8x8::splat(2) - orbs;
                let m = a.simd_ge(u8x8::splat(3));
                let rotated = m.select(a - u8x8::splat(3), a);

                // SAFETY: Each u8 will be one of 0, 1 or 2, which are all explicit variants of the
                // CornerTwist enum.
                unsafe {
                    transmute::<[u8; 8], [CornerTwist; 8]>(
                        *same_orbits.select(co, rotated).as_array(),
                    )
                }
            }
            Axis::LR => {
                // we rotate by the opposite of what is rotated by in the FB case
                let a = co + u8x8::splat(1) + orbs;
                let m = a.simd_ge(u8x8::splat(3));
                let rotated = m.select(a - u8x8::splat(3), a);

                // SAFETY: Same as the FB branch
                unsafe {
                    transmute::<[u8; 8], [CornerTwist; 8]>(
                        *same_orbits.select(co, rotated).as_array(),
                    )
                }
            }
            Axis::UD => self.co,
        }
    }

    /// Get the edge orientation of this puzzle relative to the given axis (so quarter turns on
    /// that axis flip orientation). Orientations are still indexed by `Edge`.
    #[inline]
    pub fn axis_eo(&self, axis: Axis) -> [EdgeFlip; 12] {
        // L/R: The orientation of E slice edges out of the E slice and U/D edges in the E slice
        //      will flip
        // U/D: The orientation of M slice edges out of the M slice and R/L edges in the M slice
        //      will flip
        use std::mem::transmute;
        use std::simd::{Select, prelude::*};
        // WHAAAT you can do this?!?! Simd infers Simd<12, u8> and 12 isn't a power of 2!!
        // It's also faster than I can get it to be with 16 lanes (simd 12 doesn't optimise well
        // sometimes, but here it does yay)
        let eo = Simd::from_array(self.eo.map(|o| o as u8));
        let ep = Simd::from_array(self.ep.map(|p| p as u8));
        match axis {
            Axis::FB => self.eo,
            Axis::LR => {
                /*
                std::array::from_fn(|i| {
                    // Edge is in e slice iff >= 8
                    let (o, p) = (self.eo[i], self.ep[i] as u8);
                    if (i >= 8) == (p >= 8) { o.flip() } else { o }
                }) */
                // wait this is even better to simd
                let is = Simd::from_array([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1]);
                // >= 8 iff 8s bit is set since edge positions are <= 12
                let f = (ep >> Simd::splat(3)) ^ is;
                let r = eo ^ f;
                // SAFETY: eo contains only values 0 or 1, and f is bitwise and with is and so also
                // only has values 0 or 1. EdgeFlip has 0 and 1 as its explicit variants.
                unsafe { transmute::<[u8; 12], [EdgeFlip; 12]>(*r.as_array()) }
            }
            Axis::UD => {
                /*
                std::array::from_fn(|i| {
                    // Edge is in M slice iff < 8 and %2 == 0
                    let (o, p) = (self.eo[i], self.ep[i] as u8);
                    if (i < 8 && i.is_multiple_of(2)) == (p < 8 && p.is_multiple_of(2)) {
                        o.flip()
                    } else {
                        o
                    }
                }) */
                let is = Simd::from_array([1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]);
                // M slice edge iff 8s bit and 1s bit are unset i.e. iff &9 == 0
                let f = (ep & Simd::splat(9))
                    .simd_eq(Simd::splat(0))
                    .select(Simd::splat(1u8), Simd::splat(0))
                    ^ is;
                let r = eo ^ f;
                // SAFETY: Same argument as with LR.
                unsafe { transmute::<[u8; 12], [EdgeFlip; 12]>(*r.as_array()) }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    fn costr(s: &str) -> [CornerTwist; 8] {
        let bs = s.as_bytes().as_array().unwrap();
        bs.map(|b| match b {
            b's' => CornerTwist::Oriented,
            b'c' => CornerTwist::Clockwise,
            b'a' => CornerTwist::AntiClockwise,
            _ => panic!(),
        })
    }

    #[test]
    fn co() {
        let c = CubieCube::SOLVED.make_moves(
            "B' L' F R2 L' U' L' U D' R2 U2 R' D2 L2 F2 R B2 L' F2 R' B2"
                .parse()
                .unwrap(),
        );
        assert_eq!(c.axis_co(Axis::UD), costr("cscaaccc"));
        assert_eq!(c.axis_co(Axis::FB), costr("ccsacasa"));
        assert_eq!(c.axis_co(Axis::LR), costr("caaassas"));
    }

    fn eostr(s: &str) -> [EdgeFlip; 12] {
        let bs = s.as_bytes().as_array().unwrap();
        bs.map(|b| match b {
            b's' => EdgeFlip::Oriented,
            b'f' => EdgeFlip::Flipped,
            _ => panic!(),
        })
    }

    #[test]
    fn eo() {
        let c = CubieCube::SOLVED.make_moves(
            "B' L' F R2 L' U' L' U D' R2 U2 R' D2 L2 F2 R B2 L' F2 R' B2"
                .parse()
                .unwrap(),
        );
        assert_eq!(c.axis_eo(Axis::FB), eostr("fffssfsfffsf"));
        assert_eq!(c.axis_eo(Axis::LR), eostr("fffsffssfffs"));
        assert_eq!(c.axis_eo(Axis::UD), eostr("fsssfsffffss"));
    }

    use crate::{
        cube333::{CornerPos as CP, CubieCube, EdgePos as EP, StickerCube, moves::Move333},
        moves::MoveSequence,
    };
    use proptest::collection::vec;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn prop_co(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence)) {
            let c = CubieCube::SOLVED.make_moves(mvs);
            let s: StickerCube = c.clone().into();
            const UD_I: [CP; 8] = [CP::UFR, CP::UFL, CP::UBL, CP::UBR, CP::DFL, CP::DFR, CP::DBR, CP::DBL];
            const FB_I: [CP; 8] = [CP::FUR, CP::FUL, CP::BUL, CP::BUR, CP::FDL, CP::FDR, CP::BDR, CP::BDL];
            const LR_I: [CP; 8] = [CP::RUF, CP::LUF, CP::LUB, CP::RUB, CP::LDF, CP::RDF, CP::RDB, CP::LDB];
            assert_eq!(c.axis_co(Axis::UD), UD_I.map(|p| s.corner_at(p).unwrap().ud_orientation().inverse()));
            assert_eq!(c.axis_co(Axis::FB), FB_I.map(|p| s.corner_at(p).unwrap().fb_orientation().inverse()));
            assert_eq!(c.axis_co(Axis::LR), LR_I.map(|p| s.corner_at(p).unwrap().lr_orientation().inverse()));
        }

        #[test]
        fn prop_eo(mvs in vec(any::<Move333>(), 0..20).prop_map(MoveSequence)) {
            let c = CubieCube::SOLVED.make_moves(mvs);
            let s: StickerCube = c.clone().into();
            const FB_I: [EP; 12] = [EP::UF, EP::UL, EP::UB, EP::UR, EP::DF, EP::DL, EP::DB, EP::DR, EP::FR, EP::FL, EP::BL, EP::BR];
            const LR_I: [EP; 12] = [EP::UF, EP::UL, EP::UB, EP::UR, EP::DF, EP::DL, EP::DB, EP::DR, EP::RF, EP::LF, EP::LB, EP::RB];
            const UD_I: [EP; 12] = [EP::FU, EP::UL, EP::BU, EP::UR, EP::FD, EP::DL, EP::BD, EP::DR, EP::FR, EP::FL, EP::BL, EP::BR];
            assert_eq!(c.axis_eo(Axis::FB), FB_I.map(|p| s.edge_at(p).unwrap().fb_orientation()));
            assert_eq!(c.axis_eo(Axis::LR), LR_I.map(|p| s.edge_at(p).unwrap().lr_orientation()));
            assert_eq!(c.axis_eo(Axis::UD), UD_I.map(|p| s.edge_at(p).unwrap().ud_orientation()));
        }
    }
}
