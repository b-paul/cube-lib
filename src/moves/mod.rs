//! Module for puzzle move generics and related functionality

use thiserror::Error;

use std::str::FromStr;

/// Enum for representing the cancellation of two moves.
/// See [`cancel`](Move::cancel).
#[derive(Eq, PartialEq)]
pub enum Cancellation<M: Move> {
    /// The moves cancelled completely.
    ///
    /// e.g. `R R'` cancels completely
    NoMove,
    /// The moves cancelled into one move.
    ///
    /// e.g. `R R` cancels into `R2`
    OneMove(M),
    /// The moves didn't cancel
    ///
    /// e.g. `R U` stays as `R U` when cancelling
    TwoMove(M, M),
}

/// A move, for use in writing expressions or algorithms. It is intended that a term of this trait
/// is a power of a symbol in some group presentation, satisfying law allowing simplification.
///
/// The relations moves satisfy should include an order for each term (e.g. R4 is the identity on a
/// 3x3x3) and that some terms commute (e.g. R and L commute on a 3x3x3). Commutativity relations
/// are encoded in the `commutes_with` method and order relations are encoded in the `cancel`
/// method. These relations are all that are assumed for the general `MoveSequence::cancel`, so any
/// additional relations will not be used for optimal cancellation.
pub trait Move: Eq + Clone + Sized {
    /// Take the inverse of a move. These inverses must satisfy the invertibility conditions of
    /// a group, i.e. that `X X^{-1} = X^{-1} X = e` where `e` is the empty sequence.
    fn inverse(self) -> Self;

    /// Returns whether the two moves commute, i.e. can be swapped when adjacent. It is required
    /// that this property is transitive.
    ///
    /// If A and B are moves, then `A.commutes_with(B)` iff
    /// `A B = B A`
    /// moreover, if `B.commutes_with(C)`, then it must be true that `A.commutes_with(C)`
    fn commutes_with(&self, b: &Self) -> bool;

    /// Return the cancellation of two moves.
    ///
    /// It is assumed that group axioms hold when applying cancellations.
    ///
    /// ```rust
    /// # fn main() {
    /// use cube_lib::mv;
    /// use cube_lib::cube333::moves::{Move333, Move333Type};
    /// use cube_lib::moves::{Cancellation, Move};
    ///
    /// // In the context of a 3x3x3 Rubik's cube
    /// assert!(mv!(R, 1).cancel(mv!(U, 3)) == Cancellation::TwoMove(mv!(R, 1), mv!(U, 3)));
    /// assert!(mv!(R, 1).cancel(mv!(R, 1)) == Cancellation::OneMove(mv!(R, 2)));
    /// assert!(mv!(R, 1).cancel(mv!(R, 3)) == Cancellation::NoMove);
    /// # }
    /// ```
    fn cancel(self, b: Self) -> Cancellation<Self>;
}

/// A sequence of moves (also known as an algorithm) for some specific type of move.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct MoveSequence<M: Move>(pub Vec<M>);

impl<M: Move> MoveSequence<M> {
    /// Invert a sequence of moves.
    ///
    /// If `X` is a sequence of moves and `X^{-1}` is its inverse and `o` is composition, then
    /// `X o X^{-1} = X^{-1} o X = e` where `e` is the empty sequence.
    pub fn inverse(self) -> Self {
        Self(self.0.into_iter().rev().map(|m| m.inverse()).collect())
    }

    /// Cancel an alg completely, including rearrangement of commutative moves. This guarantees
    /// optimal move count from cancellations (I THINK! TODO: PROVE THIS CLAIM!!).
    pub fn cancel(mut self) -> Self {
        let mut cancellation: Vec<M> = Vec::new();

        for next_mv in self.0.drain(..) {
            // We work from the back of our fully reduced sub-expression, checking each move that
            // we can commute with in sequence. We move the term we cancel with to the back, then
            // cancel with it. Because our expression was previously fully reduced, moving this old
            // term to the back will not create any new cancellations.
            let mut cancelled = false;

            for i in (0..cancellation.len()).rev() {
                match cancellation[i].clone().cancel(next_mv.clone()) {
                    Cancellation::NoMove => {
                        cancellation.remove(i);
                        cancelled = true;
                        continue;
                    }
                    Cancellation::OneMove(m) => {
                        cancellation.remove(i);
                        cancellation.push(m);
                        cancelled = true;
                        continue;
                    }
                    Cancellation::TwoMove(_, _) => {}
                }

                if !next_mv.commutes_with(&cancellation[i]) {
                    break;
                }
            }

            if !cancelled {
                cancellation.push(next_mv);
            }
        }

        Self(cancellation)
    }

    /// The length of this sequence.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Determines if this sequence is the empty sequence.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Add another sequence of moves to the end of this one.
    pub fn append(self, mut other: Self) -> Self {
        let mut seq = self.0;
        seq.append(&mut other.0);
        MoveSequence(seq)
    }
}

impl<T: Move + FromStr> FromStr for MoveSequence<T> {
    type Err = T::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.split_whitespace()
            .map(|s| s.parse::<T>())
            .collect::<Result<_, _>>()
            .map(MoveSequence)
    }
}

/// A "sequence" of moves, some of which are applied on the inverse of the puzzle. See the NISS
/// fmc solving technique.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct NissSequence<T: Move> {
    /// The normal part of the sequence
    pub normal: MoveSequence<T>,
    /// The inverse part of the sequence
    pub inverse: MoveSequence<T>,
}

/// Error for parsing `NissSequence`s.
#[derive(Debug, PartialEq, Eq, Error)]
pub enum NissParseError<T: Move + FromStr> {
    /// Invalid niss bracketing was provided.
    #[error("Invalid niss bracketing was provided")]
    InvalidBracketing,
    /// Failed to read a move
    #[error("{0}")]
    InvalidMove(T::Err),
}

impl<T: Move + FromStr> FromStr for NissSequence<T> {
    type Err = NissParseError<T>;

    fn from_str(mut s: &str) -> Result<Self, Self::Err> {
        let mut normal = Vec::new();
        let mut inverse = Vec::new();

        while !s.is_empty() {
            match s.split_once('(') {
                Some((l, r)) => {
                    let (r, s2) = r.split_once(')').ok_or(NissParseError::InvalidBracketing)?;
                    s = s2;
                    if r.contains('(') {
                        return Err(NissParseError::InvalidBracketing);
                    }
                    let mut n = l
                        .parse::<MoveSequence<T>>()
                        .map_err(NissParseError::InvalidMove)?;
                    let mut i = r
                        .parse::<MoveSequence<T>>()
                        .map_err(NissParseError::InvalidMove)?;
                    normal.append(&mut n.0);
                    inverse.append(&mut i.0);
                }
                None => {
                    if s.contains(')') {
                        return Err(NissParseError::InvalidBracketing);
                    }
                    let mut n = s
                        .parse::<MoveSequence<T>>()
                        .map_err(NissParseError::InvalidMove)?;
                    normal.append(&mut n.0);
                    break;
                }
            }
        }

        Ok(NissSequence {
            normal: MoveSequence(normal),
            inverse: MoveSequence(inverse),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::cube333::moves::{Move333, Move333ParseError, Move333Type};
    use super::*;
    use crate::mv;

    #[test]
    fn parse() {
        assert_eq!(
            "R U R3".parse::<MoveSequence<Move333>>(),
            Err(Move333ParseError("R3".to_owned()))
        );
        assert_eq!(
            "R U R3".parse::<NissSequence<Move333>>(),
            Err(NissParseError::InvalidMove(Move333ParseError(
                "R3".to_owned()
            )))
        );
        assert_eq!(
            "R U R2".parse::<MoveSequence<Move333>>(),
            Ok(MoveSequence(vec![mv!(R, 1), mv!(U, 1), mv!(R, 2)]))
        );
        assert_eq!(
            "R U R2".parse::<NissSequence<Move333>>(),
            Ok(NissSequence {
                normal: MoveSequence(vec![mv!(R, 1), mv!(U, 1), mv!(R, 2)]),
                inverse: MoveSequence(vec![])
            })
        );
        assert_eq!(
            "R (U) F (B')".parse::<NissSequence<Move333>>(),
            Ok(NissSequence {
                normal: MoveSequence(vec![mv!(R, 1), mv!(F, 1)]),
                inverse: MoveSequence(vec![mv!(U, 1), mv!(B, 3)])
            })
        );
        assert_eq!(
            "R U (R()".parse::<NissSequence<Move333>>(),
            Err(NissParseError::InvalidBracketing)
        );
        assert_eq!(
            "R U )".parse::<NissSequence<Move333>>(),
            Err(NissParseError::InvalidBracketing)
        );
        assert_eq!(
            "R U (".parse::<NissSequence<Move333>>(),
            Err(NissParseError::InvalidBracketing)
        );
        assert_ne!(
            "R U ()".parse::<NissSequence<Move333>>(),
            Err(NissParseError::InvalidBracketing)
        );
    }
}
