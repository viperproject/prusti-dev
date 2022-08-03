use vir_crate::typed as vir_typed;

#[derive(Debug, Clone, derive_more::Display)]
pub(in super::super) enum Permission {
    /// Raw, untyped memory to which we have full permission.
    MemoryBlock(vir_typed::Expression),
    /// Place to which we have access permission. Note: depending on the type,
    /// in the final encoding the place can be represented not only with
    /// `Owned`, but also with `UniqueRef` and `FracRef` predicates.
    Owned(vir_typed::Expression),
    /// TODO: Rename MutBorrowed into `Blocked`.
    MutBorrowed(MutBorrowed),
}

#[derive(Debug, Clone, derive_more::Display, PartialEq, Eq, PartialOrd, Ord)]
#[display(fmt = "MutBorrowed({}, {})", lifetime, place)]
pub(in super::super) struct MutBorrowed {
    pub(in super::super) lifetime: vir_typed::ty::LifetimeConst,
    pub(in super::super) place: vir_typed::Expression,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in super::super) enum PermissionKind {
    MemoryBlock,
    Owned,
}
