use super::permission::PermissionKind;
use vir_crate::{high as vir_high, middle as vir_mid};

pub(in super::super) enum Action {
    Unfold(FoldingActionState),
    Fold(FoldingActionState),
    /// Convert the specified `Owned(place)` into `MemoryBlock(place)`.
    OwnedIntoMemoryBlock(ConversionState),
    RestoreMutBorrowed(RestorationState),
}

pub(in super::super) struct FoldingActionState {
    pub(in super::super) kind: PermissionKind,
    pub(in super::super) place: vir_high::Expression,
    pub(in super::super) condition: Option<Vec<vir_mid::BasicBlockId>>,
    /// If un/folding an enum, which of its variants.
    pub(in super::super) enum_variant: Option<vir_high::ty::VariantIndex>,
}

pub(in super::super) struct ConversionState {
    pub(in super::super) place: vir_high::Expression,
    pub(in super::super) condition: Option<Vec<vir_mid::BasicBlockId>>,
}

pub(in super::super) struct RestorationState {
    pub(in super::super) lifetime: vir_high::ty::LifetimeConst,
    pub(in super::super) place: vir_high::Expression,
    pub(in super::super) condition: Option<Vec<vir_mid::BasicBlockId>>,
}

impl Action {
    pub(in super::super) fn set_condition(self, condition: &[vir_mid::BasicBlockId]) -> Self {
        match self {
            Self::Unfold(state) => Self::Unfold(FoldingActionState {
                condition: Some(condition.to_vec()),
                ..state
            }),
            Self::Fold(state) => Self::Fold(FoldingActionState {
                condition: Some(condition.to_vec()),
                ..state
            }),
            Self::OwnedIntoMemoryBlock(state) => Self::OwnedIntoMemoryBlock(ConversionState {
                condition: Some(condition.to_vec()),
                ..state
            }),
            Self::RestoreMutBorrowed(state) => Self::RestoreMutBorrowed(RestorationState {
                condition: Some(condition.to_vec()),
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
}
