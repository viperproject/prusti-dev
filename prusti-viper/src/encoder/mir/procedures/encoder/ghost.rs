use super::ProcedureEncoder;
use crate::encoder::{
    errors::{SpannedEncodingError, SpannedEncodingResult},
    mir::specifications::SpecificationsInterface,
};
use prusti_rustc_interface::middle::{
    mir::{
        self,
        visit::{PlaceContext, Visitor},
    },
    ty,
};
use rustc_hash::FxHashSet;

impl<'p, 'v: 'p, 'tcx: 'v> super::ProcedureEncoder<'p, 'v, 'tcx> {
    pub(super) fn encode_ghost_blocks(&mut self) -> SpannedEncodingResult<()> {
        let ghost_blocks = self.specification_blocks.ghost_blocks();

        if ghost_blocks.is_empty() {
            return Ok(());
        }

        // Check that ghost blocks don't transfer control flow outside
        for &bb in ghost_blocks {
            let data = &self.mir.basic_blocks()[bb];
            if let mir::TerminatorKind::Return = data.terminator().kind {
                unreachable!("Control Flow reached outside the ghost block.\nThis should be prevented by the `ghost!` macro.");
            }
        }

        let violations = GhostChecker::find_violations(self);
        for violation in violations {
            Err(violation)?;
        }

        Ok(())
    }
}

struct GhostChecker<'a, 'p: 'a, 'v: 'p, 'tcx: 'v> {
    p: &'a ProcedureEncoder<'p, 'v, 'tcx>,
    normal_vars: FxHashSet<mir::Local>,
    violations: Vec<SpannedEncodingError>,
}

impl<'a, 'p, 'v, 'tcx> GhostChecker<'a, 'p, 'v, 'tcx> {
    fn is_ghost_place(&self, location: mir::Location) -> bool {
        self.p.specification_blocks.is_ghost_block(location.block)
    }
    fn is_ghost_local(&self, local: &mir::Local) -> bool {
        let ty = &self.p.mir.local_decls[*local].ty;
        let ty_str = format!("{:?}", ty);

        let ghost_tys = ["Ghost", "Int", "Seq", "Map"];

        for ghost in ghost_tys {
            if ty_str.starts_with(&format!("prusti_contracts::{ghost}")) {
                return true;
            }
        }

        // unit types get generated all over, and carry no information, thus okay to leak outside the ghost block
        ty.is_unit()
    }
    fn find_violations(p: &ProcedureEncoder<'p, 'v, 'tcx>) -> Vec<SpannedEncodingError> {
        let mut checker = GhostChecker {
            p,
            normal_vars: Default::default(),
            violations: Default::default(),
        };

        // first visit is to find all the normal variables
        checker.visit_body(p.mir);
        // second visit is to find all the mutations to the normal variables within ghost code
        checker.visit_body(p.mir);

        checker.violations
    }
}

impl<'a, 'p, 'v, 'tcx> Visitor<'tcx> for GhostChecker<'a, 'p, 'v, 'tcx> {
    fn visit_local(&mut self, local: mir::Local, context: PlaceContext, location: mir::Location) {
        let is_ghost = self.is_ghost_place(location) || self.is_ghost_local(&local);
        if !is_ghost && context.is_use() {
            self.normal_vars.insert(local);
        }
        if is_ghost && context.is_mutating_use() && self.normal_vars.contains(&local) {
            let stmt =
                &self.p.mir.basic_blocks()[location.block].statements[location.statement_index];
            let span = stmt.source_info.span;
            log::debug!("violating statement: {:?}", stmt);
            self.violations.push(SpannedEncodingError::incorrect(
                "mutating non-ghost variable within ghost block",
                span,
            ));
        }
    }
    fn visit_terminator(&mut self, term: &mir::Terminator<'tcx>, location: mir::Location) {
        if self.is_ghost_place(location) {
            match &term.kind {
                mir::TerminatorKind::Call {
                    func: mir::Operand::Constant(box mir::Constant { literal, .. }),
                    ..
                } => {
                    if let ty::TyKind::FnDef(def_id, _call_substs) = literal.ty().kind() {
                        if !self.p.encoder.is_pure(*def_id, None) {
                            self.violations.push(SpannedEncodingError::incorrect(
                                "Only pure function calls are allowed in ghost blocks.",
                                term.source_info.span,
                            ));
                        }
                    } else {
                        unimplemented!();
                    }
                }
                mir::TerminatorKind::Call { .. } => {
                    unimplemented!();
                }
                _ => (),
            }
        }
        self.super_terminator(term, location);
    }
}
