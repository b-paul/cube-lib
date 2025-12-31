//! This module defines general error types used throughout the crate.

use thiserror::Error;

/// Error type for converting integers to (C like) enums using TryFrom
#[derive(Debug, Error)]
pub enum TryFromIntToEnumError {
    /// attempted to convert integer into enum value, but integer was out of bounds
    #[error("attempted to convert integer into enum value, but integer was out of bounds")]
    OutOfBounds,
}
