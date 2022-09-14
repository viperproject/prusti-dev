//! The traits for converting expressions into snapshots.

/// Contains the traits for converting in builtin-method contexts where we do
/// not use SSA, but use `caller_for`.
///
/// FIXME: This probably should be removed.
mod builtin_methods;
/// The trait that provides the general skeleton for converting expressions into
/// snapshots.
mod common;
/// Contains the traits for converting elements into the snapshots where the
/// context does not matter. Currently, the only example is types.
mod context_independent;
/// Contains the traits for converting in procedure contexts where we need to
/// use SSA form and `caller_for` for calling pure functions.
///
/// FIXME: This probably should be removed.
mod procedure;
/// Contains the traits for converting in pure contexts such as axioms and pure
/// function definitions where we do not use neither SSA nor `caller_for`.
///
/// FIXME: This probably should be removed.
mod pure;
/// Contains structs for converting assertions (potentially containing
/// accessibility predicates) to snapshots. Both SSA and non-SSA forms are
/// supported.
mod assertions;
/// Contains structs for converting expressions to snapshots.
mod expressions;
mod utils;

pub(in super::super) use self::{
    assertions::{
        AssertionToSnapshotConstructor, PredicateKind, SelfFramingAssertionEncoderState,
        SelfFramingAssertionToSnapshot, ValidityAssertionToSnapshot,
    },
    builtin_methods::IntoBuiltinMethodSnapshot,
    common::IntoSnapshotLowerer,
    context_independent::IntoSnapshot,
    expressions::{FramedExpressionToSnapshot, PlaceToSnapshot},
    procedure::{
        IntoProcedureAssertion, IntoProcedureBoolExpression, IntoProcedureFinalSnapshot,
        IntoProcedureSnapshot,
    },
    pure::{IntoPureBoolExpression, IntoPureSnapshot},
};
