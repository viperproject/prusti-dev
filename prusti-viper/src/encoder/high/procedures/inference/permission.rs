use vir_crate::high as vir_high;

#[derive(Debug, Clone)]
pub(in super::super) enum Permission {
    MemoryBlock(vir_high::Expression),
    Owned(vir_high::Expression),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in super::super) enum PermissionKind {
    MemoryBlock,
    Owned,
}

impl Permission {
    pub(in super::super) fn new(kind: PermissionKind, place: vir_high::Expression) -> Permission {
        match kind {
            PermissionKind::MemoryBlock => Permission::MemoryBlock(place),
            PermissionKind::Owned => Permission::Owned(place),
        }
    }
}
