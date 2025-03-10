//! Encoding for MIR types, organised by type kind.

pub mod adt;
pub mod closure;
pub mod immref;
pub mod mutref;
pub mod never;
pub mod param;
pub mod primitive;
pub mod str;
pub mod tuple;
mod structlike;
