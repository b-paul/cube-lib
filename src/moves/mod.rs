//! Module for puzzle move generics and related functionality

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
pub trait Move: Eq + Clone {
    /// Take the inverse of a move. These inverses must satisfy the invertibility conditions of
    /// a group, i.e. that `X X^{-1} = X^{-1} X = e` where `e` is the empty sequence.
    fn inverse(self) -> Self
    where
        Self: Sized;

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
    fn cancel(self, b: Self) -> Cancellation<Self>
    where
        Self: Sized;
}

/// A sequence of moves (also known as an algorithm) for some specific type of move.
#[derive(Eq, PartialEq)]
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
                    }
                    Cancellation::OneMove(_) => {
                        let new = cancellation.remove(i);
                        cancellation.push(new);
                        cancelled = true;
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
}
