use super::permission::PermissionKind;
use vir_crate::{
    high as vir_high,
    middle::{self as vir_mid, BlockMarkerCondition},
};

pub(in super::super) enum Action {
    Unfold(FoldingActionState),
    Fold(FoldingActionState),
    /// Convert the specified `Owned(place)` into `MemoryBlock(place)`.
    OwnedIntoMemoryBlock(ConversionState),
    RestoreMutBorrowed(RestorationState),
    Unreachable(UnreachableState),
}

pub(in super::super) struct FoldingActionState {
    pub(in super::super) kind: PermissionKind,
    pub(in super::super) place: vir_high::Expression,
    pub(in super::super) condition: Option<vir_mid::BlockMarkerCondition>,
    /// If un/folding an enum, which of its variants.
    pub(in super::super) enum_variant: Option<vir_high::ty::VariantIndex>,
}

pub(in super::super) struct ConversionState {
    pub(in super::super) place: vir_high::Expression,
    pub(in super::super) condition: Option<vir_mid::BlockMarkerCondition>,
}

pub(in super::super) struct RestorationState {
    pub(in super::super) lifetime: vir_high::ty::LifetimeConst,
    pub(in super::super) place: vir_high::Expression,
    pub(in super::super) condition: Option<vir_mid::BlockMarkerCondition>,
}

pub(in super::super) struct UnreachableState {
    pub(in super::super) position: vir_high::Position,
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
        place: vir_high::Expression,
        enum_variant: Option<vir_high::ty::VariantIndex>,
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
        place: vir_high::Expression,
        enum_variant: Option<vir_high::ty::VariantIndex>,
    ) -> Self {
        Self::Fold(FoldingActionState {
            kind,
            place,
            enum_variant,
            condition: None,
        })
    }

    pub(in super::super) fn owned_into_memory_block(place: vir_high::Expression) -> Self {
        Self::OwnedIntoMemoryBlock(ConversionState {
            place,
            condition: None,
        })
    }

    pub(in super::super) fn restore_mut_borrowed(
        lifetime: vir_high::ty::LifetimeConst,
        place: vir_high::Expression,
    ) -> Self {
        Self::RestoreMutBorrowed(RestorationState {
            lifetime,
            place,
            condition: None,
        })
    }

    pub(in super::super) fn unreachable(position: vir_high::Position) -> Self {
        Self::Unreachable(UnreachableState {
            position,
            condition: None,
        })
    }
}
