use vir_crate::high as vir_high;

#[derive(Debug, Clone, derive_more::Display)]
pub(in super::super) enum Permission {
    MemoryBlock(vir_high::Expression),
    Owned(vir_high::Expression),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in super::super) enum PermissionKind {
    MemoryBlock,
    Owned,
}
