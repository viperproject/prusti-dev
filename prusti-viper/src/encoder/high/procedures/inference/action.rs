use super::permission::PermissionKind;
use vir_crate::high as vir_high;

pub(in super::super) enum Action {
    Unfold(PermissionKind, vir_high::Expression),
    Fold(PermissionKind, vir_high::Expression),
}
