use super::super::{mir_helper::*, mir_info_collector::MirInfo, mir_modifications::MirModifier};
use prusti_rustc_interface::{
    index::IndexVec,
    middle::{
        mir::{self, patch::MirPatch, visit::MutVisitor},
        ty::{self, TyCtxt},
    },
    span::{def_id::DefId, DUMMY_SP},
};
use std::cell::{RefCell, RefMut};

/// This pass inserts precondition checks at the beginning of the
/// body, and also in front of each function that is called
/// (in case they have them)
pub struct PreconditionInserter<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body_info: &'a MirInfo<'tcx>,
    /// making modifications from a Visitor often requires access
    /// to a patcher! But from the visiting methods we don't have
    /// direct access to a mutable body
    patch_opt: Option<RefCell<MirPatch<'tcx>>>,
    def_id: DefId,
    local_decls: &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
}

impl<'tcx, 'a> PreconditionInserter<'tcx, 'a> {
    pub fn run(
        tcx: TyCtxt<'tcx>,
        body_info: &'a MirInfo<'tcx>,
        def_id: DefId,
        local_decls: &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
        body: &mut mir::Body<'tcx>,
    ) {
        let mut inserter = Self {
            tcx,
            body_info,
            patch_opt: None,
            def_id,
            local_decls,
        };
        inserter.modify(body);
    }

    fn modify(&mut self, body: &mut mir::Body<'tcx>) {
        let mut current_target = get_block_target(body, mir::START_BLOCK)
            .expect("Bug: Body must start with a Goto block at this stage");
        let patch = MirPatch::new(body);
        self.patch_opt = Some(patch.into());
        let generics = ty::GenericArgs::identity_for_item(self.tcx, self.body_info.def_id);
        let args = args_from_body(body);
        for check_id in self.body_info.specs.get_pre_checks(&self.body_info.def_id) {
            (current_target, _) = self
                .create_call_block(check_id, args.clone(), generics, None, Some(current_target))
                .unwrap();
        }
        // make the starting block (which should already be a dummy)
        // point to the first precondition check
        self.patcher().patch_terminator(
            mir::START_BLOCK,
            mir::TerminatorKind::Goto {
                target: current_target,
            },
        );
        // apply patch first
        let patch_ref = self.patch_opt.take().unwrap();
        patch_ref.into_inner().apply(body);
        // new patch for other modifications:
        self.patch_opt = Some(RefCell::new(MirPatch::new(body)));
        self.visit_body(body);
        let patch_ref = self.patch_opt.take().unwrap();
        patch_ref.into_inner().apply(body);
    }
}

impl<'tcx, 'a> MutVisitor<'tcx> for PreconditionInserter<'tcx, 'a> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_terminator(
        &mut self,
        terminator: &mut mir::Terminator<'tcx>,
        location: mir::Location,
    ) {
        if let mir::TerminatorKind::Call {
            func, target, args, ..
        } = &terminator.kind
        {
            if let Some((call_id, generics)) = func.const_fn_def() {
                let mut caller_block = location.block;
                let _current_target = target;
                if call_id.is_local() {
                    // If the call is local, we modify its body anyways
                    return;
                }
                for check_id in self.body_info.specs.get_pre_checks(&call_id) {
                    let return_ty = fn_return_ty(self.tcx, check_id, Some(generics));
                    assert!(return_ty.is_unit());
                    let res = self.patcher().new_temp(return_ty, DUMMY_SP);
                    caller_block = self.prepend_call(
                        check_id,
                        caller_block,
                        args.clone(),
                        generics,
                        terminator.clone(),
                        res.into(),
                    );
                }
            }
        }
    }
}

impl<'tcx, 'a> MirModifier<'tcx> for PreconditionInserter<'tcx, 'a> {
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
