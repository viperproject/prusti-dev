//! Encoding from `vir::high` to lower layers.
//!
//! Note: This module must not depend on MIR directly. In other words, no type
//! in this module can have the `'tcx` bound.

pub(crate) mod builtin_functions;
pub(crate) mod expressions;
pub(crate) mod generics;
pub(crate) mod lower;
pub(crate) mod procedures;
pub(crate) mod pure_functions;
mod to_middle;
pub(crate) mod type_layouts;
pub(crate) mod types;
