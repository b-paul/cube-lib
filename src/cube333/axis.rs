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

impl CubieCube {
    /// Get the corner orientation of this puzzle relative to a given axis i.e. treating that axis
    /// as the U/D faces. Orientations are still indexed by `Corner`.
    pub fn axis_co(&self, axis: Axis) -> [CornerTwist; 8] {
        /*
        std::array::from_fn(|i| {
            // It seems that if a corner is in its htr orbit, the co is the same as the U/D co,
            // else it's a clockwise off if F/B and anticlockwise off if R/L (idk i just messed
            // around on a cube and it seems true).
            let o = self.co[i];
            // We can compute the orbit as the index of the corner position mod 2 OR we could use
            // funny bit hackery yayyy!! The mod 2 value is the 1s bit, and the xor is a neq.
            let diff_orbit = (i ^ (self.cp[i] as usize)) & 1;

            match (axis, diff_orbit) {
                (Axis::FB, 1) => o.clockwise(),
                (Axis::LR, 1) => o.anticlockwise(),
                _ => o,
            }
        })
        */
        // wait this could be simded lol
        use std::mem::transmute;
        use std::simd::{Select, prelude::*};
        let co = u8x8::from_array(self.co.map(|o| o as u8));
        let cp = u8x8::from_array(self.cp.map(|p| p as u8));
        let orbs = u8x8::from_array([0, 1, 0, 1, 0, 1, 0, 1]);
        let same_orbits = orbs.simd_eq(cp & u8x8::splat(1));
        match axis {
            Axis::FB => {
                // add 1 mod 3
                let a = co + u8x8::splat(1);
                let m = a.simd_eq(u8x8::splat(3));
                let clockwise = m.select(u8x8::splat(0), a);

                // SAFETY: Each u8 will be one of 0, 1 or 2, which are all explicit variants of the
                // CornerTwist enum.
                unsafe {
                    transmute::<[u8; 8], [CornerTwist; 8]>(
                        *same_orbits.select(co, clockwise).as_array(),
                    )
                }
            }
            Axis::LR => {
                // subtract 1 mod 3
                let m = co.simd_eq(u8x8::splat(0));
                let a = m.select(u8x8::splat(3), co);
                let anticlockwise = a - u8x8::splat(1);

                // SAFETY: Same as the FB branch
                unsafe {
                    transmute::<[u8; 8], [CornerTwist; 8]>(
                        *same_orbits.select(co, anticlockwise).as_array(),
                    )
                }
            }
            Axis::UD => self.co,
        }
    }

    /// Get the edge orientation of this puzzle relative to the given axis (so quarter turns on
    /// that axis flip orientation). Orientations are still indexed by `Edge`.
    pub fn axis_eo(&self, axis: Axis) -> [EdgeFlip; 12] {
        // L/R: The orientation of E slice edges out of the E slice and U/D edges in the E slice
        //      will flip
        // U/D: The orientation of M slice edges out of the M slice and R/L edges in the M slice
        //      will flip
        use std::mem::transmute;
        use std::simd::prelude::*;
        // WHAAAT you can do this?!?! Simd infers Simd<12, u8> and 12 isn't a power of 2!!
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
                let f = (ep >> Simd::splat(3)) & is;
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
                // M slice edge iff 8s bit and 1s bit are unset
                let f = (!((ep >> Simd::splat(3)) & ep) & Simd::splat(1)) ^ is;
                let r = eo ^ f;
                // SAFETY: Same argument as with LR.
                unsafe { transmute::<[u8; 12], [EdgeFlip; 12]>(*r.as_array()) }
            }
        }
    }
}
