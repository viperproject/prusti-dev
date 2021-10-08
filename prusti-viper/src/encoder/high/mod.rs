//! Encoding from `vir::high` to lower layers.
//!
//! Note: This module must not depend on MIR directly. In other words, no type
//! in this module can have the `'tcx` bound.

pub(crate) mod types;
