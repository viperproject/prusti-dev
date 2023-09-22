use super::super::{mir_helper::*, mir_info_collector::MirInfo, mir_modifications::MirModifier};

use prusti_rustc_interface::{
    index::IndexVec,
    middle::{
        mir::{self, patch::MirPatch, visit::MutVisitor},
        ty::{self, TyCtxt},
    },
    span::{def_id::DefId, DUMMY_SP},
};
use rustc_hash::FxHashMap;
use std::cell::{RefCell, RefMut};

pub struct CloneOldArgs<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body_info: &'a MirInfo<'tcx>,
    patch_opt: Option<RefCell<MirPatch<'tcx>>>,
    def_id: DefId,
    local_decls: &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
    stored_arguments: FxHashMap<mir::Local, mir::Local>,
}

impl<'tcx, 'a> CloneOldArgs<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body_info: &'a MirInfo<'tcx>,
        def_id: DefId,
        local_decls: &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
    ) -> Self {
        Self {
            tcx,
            body_info,
            patch_opt: None,
            def_id,
            local_decls,
            stored_arguments: Default::default(),
        }
    }

    /// Creates locals for the clones of arguments, and replaces them in
    /// the correct places such that old behaves correctly. This function
    /// relies on the locations in `stmts_to_substitue_rhs` to be accurate, so it
    /// needs to be executed before any of the modifications that alter block indeces
    /// happen. It does not modify any block indeces itself.
    pub fn create_and_replace_variables(&mut self, body: &mut mir::Body<'tcx>) {
        let mut patcher = MirPatch::new(body);
        // create the temporary variables
        for arg in &self.body_info.args_to_be_cloned {
            let ty = self.local_decls.get(*arg).unwrap().ty;
            let new_var = patcher.new_temp(ty, DUMMY_SP);
            self.stored_arguments.insert(*arg, new_var);
        }
        // replace the function arguments with the new temporary variables
        // according to information we collected earlier
        let mut replacer = ArgumentReplacer::new(self.tcx, &self.stored_arguments);
        for (block, bb_data) in body.basic_blocks_mut().iter_enumerated_mut() {
            for (statement_index, stmt) in bb_data.statements.iter_mut().enumerate() {
                let loc = mir::Location {
                    block,
                    statement_index,
                };
                if self.body_info.stmts_to_substitute_rhs.contains(&loc) {
                    replacer.visit_statement(stmt, loc);
                }
            }
        }
        patcher.apply(body);
    }

    /// For variables that need to be cloned at the beginning of a function
    /// (opposed to in front of a function call as for postconditions for example)
    /// this function inserts a chain of clone calls at the beginning of the function
    /// and makes sure these values are dropped again before the function returns.
    pub fn clone_and_drop_variables(&mut self, body: &mut mir::Body<'tcx>) {
        let patch = MirPatch::new(body);
        self.patch_opt = Some(patch.into());
        let mut drop_on_return = Vec::new();
        // clone the arguments:
        let mut current_target = get_goto_block_target(body, mir::START_BLOCK)
            .expect("Bug: Body must start with a Goto block at this stage");
        for local in self.body_info.args_to_be_cloned.iter() {
            let place: mir::Place = (*local).into();
            let destination = *self.stored_arguments.get(local).unwrap();
            let (new_target, _, to_drop) = self
                .insert_clone_argument(place, current_target, Some(destination), None, false)
                .unwrap();
            current_target = new_target;
            if let Some(to_drop) = to_drop {
                drop_on_return.push(to_drop);
            }
        }
        let terminator_kind = mir::TerminatorKind::Goto {
            target: current_target,
        };
        self.patcher()
            .patch_terminator(mir::START_BLOCK, terminator_kind);

        let (drop_chain_start, drop_chain_end) = self.create_drop_chain(drop_on_return, None);

        let patch_ref = self.patch_opt.take().unwrap();
        patch_ref.into_inner().apply(body);

        // insert jumps to drop chain wherever function returns:
        let mut visitor = DropBeforeReturnVisitor {
            drop_chain_start,
            drop_chain_end,
            tcx: self.tcx,
        };
        visitor.visit_body(body);
    }
}

impl<'tcx, 'a> MutVisitor<'tcx> for CloneOldArgs<'tcx, 'a> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_local(
        &mut self,
        local: &mut mir::Local,
        context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) {
        if let Some(replace) = self.stored_arguments.get(local) {
            assert!(!matches!(context, mir::visit::PlaceContext::NonUse(_)));
            *local = *replace;
        }
    }
}

struct DropBeforeReturnVisitor<'tcx> {
    drop_chain_start: mir::BasicBlock,
    drop_chain_end: mir::BasicBlock,
    tcx: ty::TyCtxt<'tcx>,
}

impl<'tcx> MutVisitor<'tcx> for DropBeforeReturnVisitor<'tcx> {
    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }
    fn visit_terminator(
        &mut self,
        terminator: &mut mir::Terminator<'tcx>,
        location: mir::Location,
    ) {
        MutVisitor::super_terminator(self, terminator, location);
        if location.block == self.drop_chain_end {
            // The end of the drop chain also contains a return, so we need
            // to skip this one
            return;
        }
        // Replace return terminator with a goto to our drop chain
        if matches!(terminator.kind, mir::TerminatorKind::Return) {
            terminator.kind = mir::TerminatorKind::Goto {
                target: self.drop_chain_start,
            };
        }
    }
}

impl<'tcx, 'a> MirModifier<'tcx> for CloneOldArgs<'tcx, 'a> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn patcher(&self) -> RefMut<MirPatch<'tcx>> {
        self.patch_opt
            .as_ref()
            .expect("Bug: MirPatch for inserting preconditions was not initialized")
            .borrow_mut()
    }

    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn local_decls(&self) -> &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>> {
        self.local_decls
    }
}
