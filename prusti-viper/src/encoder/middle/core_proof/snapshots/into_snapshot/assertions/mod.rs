use vir_crate::low::{self as vir_low};

/// Assertions that are self-framing: each dereference of a pointer needs to be
/// behind `own`.
mod self_framing;
/// Assertions where the places (leaves) are translated to `snap` calls.
mod snap;
/// Assertions where the places are translated by using `heap$` pure variable.
mod pure_heap;
/// The snapshot validity assertion.
mod validity;
/// Structural invariant that needs to be translated into a snapshot
/// constructor.
mod constructor;

#[derive(Debug, Clone)]
pub(in super::super::super::super) enum PredicateKind {
    Owned,
    FracRef {
        lifetime: vir_low::Expression,
    },
    UniqueRef {
        lifetime: vir_low::Expression,
        is_final: bool,
    },
}

pub(in super::super::super) use self::{
    constructor::AssertionToSnapshotConstructor,
    self_framing::{SelfFramingAssertionEncoderState, SelfFramingAssertionToSnapshot},
    validity::ValidityAssertionToSnapshot,
};
