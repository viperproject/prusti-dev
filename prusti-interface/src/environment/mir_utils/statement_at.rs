use rustc_middle::mir;

pub trait StatementAt<'tcx> {
    fn statement_at(&self, location: mir::Location) -> Option<&mir::Statement<'tcx>>;
}

impl<'tcx> StatementAt<'tcx> for mir::Body<'tcx> {
    fn statement_at(&self, location: mir::Location) -> Option<&mir::Statement<'tcx>> {
        let block = &self[location.block];
        if location.statement_index < block.statements.len() {
            Some(&block.statements[location.statement_index])
        } else if location.statement_index == block.statements.len() {
            None
        } else {
            unreachable!(
                "cannot retrieve statement at {:?}, because the basic block is too short",
                location
            );
        }
    }
}

