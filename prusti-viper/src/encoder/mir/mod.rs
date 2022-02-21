//! Part of the encoder that converts from MIR level into `vir-high` that does
//! not depend anymore on the compiler internals.

pub(crate) mod casts;
pub(crate) mod constants;
pub(crate) mod errors;
pub(crate) mod generics;
pub(crate) mod panics;
pub(crate) mod places;
pub(crate) mod predicates;
pub(crate) mod procedures;
pub(crate) mod pure;
pub(crate) mod spans;
pub(crate) mod specifications;
pub(crate) mod type_layouts;
pub(crate) mod types;
