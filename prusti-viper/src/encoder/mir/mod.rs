//! Part of the encoder that converts from MIR level into `vir-high` that does
//! not depend anymore on the compiler internals.

pub(crate) mod casts;
pub(crate) mod constants;
pub(crate) mod generics;
pub(crate) mod places;
pub(crate) mod pure;
pub(crate) mod types;
