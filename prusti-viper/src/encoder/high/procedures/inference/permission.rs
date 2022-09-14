use vir_crate::typed as vir_typed;

#[derive(Debug, Clone, derive_more::Display)]
pub(in super::super) enum Permission {
    /// Raw, untyped memory to which we have full permission.
    MemoryBlock(vir_typed::Expression),
    /// Place to which we have access permission. Note: depending on the type,
    /// in the final encoding the place can be represented not only with
    /// `Owned`, but also with `UniqueRef` and `FracRef` predicates.
    Owned(vir_typed::Expression),
    Blocked(Blocked),
}

impl Permission {
    pub(in super::super) fn new(
        place: vir_typed::Expression,
        permission_kind: PermissionKind,
    ) -> Self {
        match permission_kind {
            PermissionKind::Owned => Self::Owned(place),
            PermissionKind::MemoryBlock => Self::MemoryBlock(place),
        }
    }

    pub(in super::super) fn get_place(&self) -> &vir_typed::Expression {
        match self {
            Self::MemoryBlock(place) => place,
            Self::Owned(place) => place,
            Self::Blocked(Blocked { place, .. }) => place,
        }
    }
}

#[derive(Debug, Clone, derive_more::Display, PartialEq, Eq, PartialOrd, Ord)]
#[display(fmt = "Blocked({lifetime}, {place})")]
pub(in super::super) struct Blocked {
    pub(in super::super) lifetime: vir_typed::ty::LifetimeConst,
    pub(in super::super) place: vir_typed::Expression,
    pub(in super::super) is_reborrow: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in super::super) enum PermissionKind {
    MemoryBlock,
    Owned,
}

impl Permission {
    pub(in super::super) fn place(&self) -> &vir_typed::Expression {
        match self {
            Permission::MemoryBlock(place) => place,
            Permission::Owned(place) => place,
            Permission::Blocked(Blocked { place, .. }) => place,
        }
    }
}
