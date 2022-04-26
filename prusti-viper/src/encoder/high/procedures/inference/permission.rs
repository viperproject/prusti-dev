use vir_crate::high as vir_high;

#[derive(Debug, Clone, derive_more::Display)]
pub(in super::super) enum Permission {
    MemoryBlock(vir_high::Expression),
    Owned(vir_high::Expression),
    MutBorrowed(MutBorrowed),
}

#[derive(Debug, Clone, derive_more::Display, PartialEq, Eq, PartialOrd, Ord)]
#[display(fmt = "MutBorrowed({}, {})", lifetime, place)]
pub(in super::super) struct MutBorrowed {
    pub(in super::super) lifetime: vir_high::ty::LifetimeConst,
    pub(in super::super) place: vir_high::Expression,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in super::super) enum PermissionKind {
    MemoryBlock,
    Owned,
}
