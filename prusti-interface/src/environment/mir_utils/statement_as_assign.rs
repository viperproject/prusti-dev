use prusti_rustc_interface::middle::mir;

pub trait StatementAsAssign<'tcx> {
    /// If this statement is an assignment, returns the LHS and RHS. If not, returns `None`.
    fn as_assign(&self) -> Option<(mir::Place<'tcx>, &mir::Rvalue<'tcx>)>;
}

impl<'tcx> StatementAsAssign<'tcx> for mir::Statement<'tcx> {
    fn as_assign(&self) -> Option<(mir::Place<'tcx>, &mir::Rvalue<'tcx>)> {
        if let mir::StatementKind::Assign(box (lhs, ref rhs)) = self.kind {
            Some((lhs, rhs))
        } else {
            None
        }
    }
}
