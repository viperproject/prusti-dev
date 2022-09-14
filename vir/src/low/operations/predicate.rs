use crate::low::ast::predicate::PredicateKind;

impl PredicateKind {
    pub fn is_non_aliased(&self) -> bool {
        matches!(
            self,
            PredicateKind::WithoutSnapshotWholeNonAliased | PredicateKind::EndBorrowViewShift
        )
    }
}
