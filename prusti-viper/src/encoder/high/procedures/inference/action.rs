use super::permission::PermissionKind;
use vir_crate::{high as vir_high, middle as vir_mid};

pub(in super::super) enum Action {
    Unfold(ActionState),
    Fold(ActionState),
}

pub(in super::super) struct ActionState {
    pub(in super::super) kind: PermissionKind,
    pub(in super::super) place: vir_high::Expression,
    pub(in super::super) condition: Option<Vec<vir_mid::BasicBlockId>>,
}

impl Action {
    pub(in super::super) fn set_condition(self, condition: &[vir_mid::BasicBlockId]) -> Self {
        match self {
            Self::Unfold(state) => Self::Unfold(ActionState {
                condition: Some(condition.to_vec()),
                ..state
            }),
            Self::Fold(state) => Self::Fold(ActionState {
                condition: Some(condition.to_vec()),
                ..state
            }),
        }
    }

    pub(in super::super) fn unfold(kind: PermissionKind, place: vir_high::Expression) -> Self {
        Self::Unfold(ActionState {
            kind,
            place,
            condition: None,
        })
    }

    pub(in super::super) fn fold(kind: PermissionKind, place: vir_high::Expression) -> Self {
        Self::Fold(ActionState {
            kind,
            place,
            condition: None,
        })
    }
}
