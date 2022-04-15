//! The traits for converting expressions into snapshots:
//!
//! + `procedure` contains the traits for converting in procedure contains where
//!   we need to use SSA form
//! + `pure` contanins the traits for converting in pure contexts such as axioms
//!   and pure function definitions where we do not use SSA.

mod common;
mod procedure;
mod pure;

pub(in super::super) use self::{
    procedure::{IntoProcedureBoolExpression, IntoProcedureSnapshot},
    pure::{IntoPureBoolExpression, IntoPureSnapshot},
};
