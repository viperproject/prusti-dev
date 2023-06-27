use super::permission::PermissionKind;
use vir_crate::{
    middle::{self as vir_mid, BlockMarkerCondition},
    typed as vir_typed,
};

#[derive(Debug)]
pub(in super::super) enum Action {
    Unfold(FoldingActionState),
    Fold(FoldingActionState),
    /// Convert the specified `Owned(place)` into `MemoryBlock(place)`.
    OwnedIntoMemoryBlock(ConversionState),
    RestoreMutBorrowed(RestorationState),
    Unreachable(UnreachableState),
}

impl std::fmt::Display for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Action::Unfold(FoldingActionState { kind, place, .. }) => {
                write!(f, "Unfold({kind:?}, {place})")
            }
            Action::Fold(FoldingActionState { kind, place, .. }) => {
                write!(f, "Fold({kind:?}, {place})")
            }
            Action::OwnedIntoMemoryBlock(ConversionState { place, .. }) => {
                write!(f, "OwnedIntoMemoryBlock({place})")
            }
            Action::RestoreMutBorrowed(RestorationState { place, .. }) => {
                write!(f, "RestoreMutBorrowed({place})")
            }
            Action::Unreachable(_) => write!(f, "Unreachable"),
        }
    }
}

#[derive(Debug)]
pub(in super::super) struct FoldingActionState {
    pub(in super::super) kind: PermissionKind,
    pub(in super::super) place: vir_typed::Expression,
    pub(in super::super) condition: Option<vir_mid::BlockMarkerCondition>,
    /// If un/folding an enum, which of its variants.
    pub(in super::super) enum_variant: Option<vir_typed::ty::VariantIndex>,
}

#[derive(Debug)]
pub(in super::super) struct ConversionState {
    pub(in super::super) place: vir_typed::Expression,
    pub(in super::super) condition: Option<vir_mid::BlockMarkerCondition>,
}

#[derive(Debug)]
pub(in super::super) struct RestorationState {
    pub(in super::super) lifetime: vir_typed::ty::LifetimeConst,
    pub(in super::super) place: vir_typed::Expression,
    pub(in super::super) is_reborrow: bool,
    pub(in super::super) condition: Option<vir_mid::BlockMarkerCondition>,
}

#[derive(Debug)]
pub(in super::super) struct UnreachableState {
    pub(in super::super) position: vir_typed::Position,
    pub(in super::super) condition: Option<vir_mid::BlockMarkerCondition>,
}

impl Action {
    pub(in super::super) fn set_condition(self, condition: &BlockMarkerCondition) -> Self {
        match self {
            Self::Unfold(state) => Self::Unfold(FoldingActionState {
                condition: Some(condition.clone()),
                ..state
            }),
            Self::Fold(state) => Self::Fold(FoldingActionState {
                condition: Some(condition.clone()),
                ..state
            }),
            Self::OwnedIntoMemoryBlock(state) => Self::OwnedIntoMemoryBlock(ConversionState {
                condition: Some(condition.clone()),
                ..state
            }),
            Self::RestoreMutBorrowed(state) => Self::RestoreMutBorrowed(RestorationState {
                condition: Some(condition.clone()),
                ..state
            }),
            Self::Unreachable(state) => Self::Unreachable(UnreachableState {
                condition: Some(condition.clone()),
                ..state
            }),
        }
    }

    pub(in super::super) fn unfold(
        kind: PermissionKind,
        place: vir_typed::Expression,
        enum_variant: Option<vir_typed::ty::VariantIndex>,
    ) -> Self {
        Self::Unfold(FoldingActionState {
            kind,
            place,
            enum_variant,
            condition: None,
        })
    }

    pub(in super::super) fn fold(
        kind: PermissionKind,
        place: vir_typed::Expression,
        enum_variant: Option<vir_typed::ty::VariantIndex>,
    ) -> Self {
        Self::Fold(FoldingActionState {
            kind,
            place,
            enum_variant,
            condition: None,
        })
    }

    pub(in super::super) fn owned_into_memory_block(place: vir_typed::Expression) -> Self {
        Self::OwnedIntoMemoryBlock(ConversionState {
            place,
            condition: None,
        })
    }

    pub(in super::super) fn restore_mut_borrowed(
        lifetime: vir_typed::ty::LifetimeConst,
        place: vir_typed::Expression,
        is_reborrow: bool,
    ) -> Self {
        Self::RestoreMutBorrowed(RestorationState {
            lifetime,
            place,
            is_reborrow,
            condition: None,
        })
    }

    pub(in super::super) fn unreachable(position: vir_typed::Position) -> Self {
        Self::Unreachable(UnreachableState {
            position,
            condition: None,
        })
    }
}
