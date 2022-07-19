//! The traits for converting expressions into snapshots:
//!
//! + `procedure` contains the traits for converting in procedure contexts where
//!   we need to use SSA form and `caller_for` for calling pure functions.
//! + `pure` contains the traits for converting in pure contexts such as axioms
//!   and pure function definitions where we do not use neither SSA nor
//!   `caller_for`.
//! + `builtin_methods` contains the traits for converting in builtin-method
//!   contexts where we do not use SSA, but use `caller_for`.

mod builtin_methods;
mod common;
mod context_independent;
mod procedure;
mod pure;

pub(in super::super) use self::{
    builtin_methods::IntoBuiltinMethodSnapshot,
    context_independent::IntoSnapshot,
    procedure::{IntoProcedureBoolExpression, IntoProcedureFinalSnapshot, IntoProcedureSnapshot},
    pure::{IntoPureBoolExpression, IntoPureSnapshot},
};
