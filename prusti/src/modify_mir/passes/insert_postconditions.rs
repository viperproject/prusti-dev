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

pub struct PostconditionInserter<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body_info: &'a MirInfo,
    patch_opt: Option<RefCell<MirPatch<'tcx>>>,
    def_id: DefId,
    local_decls: &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
}

impl<'tcx, 'a> PostconditionInserter<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body_info: &'a MirInfo,
        def_id: DefId,
        local_decls: &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
    ) -> Self {
        Self {
            tcx,
            body_info,
            patch_opt: None,
            def_id,
            local_decls,
        }
    }

    pub fn run(&mut self, body: &mut mir::Body<'tcx>) {
        let patch = MirPatch::new(body);
        self.patch_opt = Some(patch.into());
        self.visit_body(body);
        let patch_ref = self.patch_opt.take().unwrap();
        patch_ref.into_inner().apply(body);
    }

    fn surround_call_with_store_and_check(
        &self,
        check_id: DefId,
        caller_block: mir::BasicBlock,
        target: Option<mir::BasicBlock>,
        result_operand: mir::Place<'tcx>,
        args: Vec<mir::Operand<'tcx>>,
        substs: ty::subst::SubstsRef<'tcx>,
        original_terminator: mir::Terminator<'tcx>,
    ) -> (mir::BasicBlock, Option<mir::BasicBlock>) {
        // find the type of that local
        let check_sig = self.tcx.fn_sig(check_id).subst(self.tcx, substs);
        let param_env = self.tcx.param_env(self.def_id);
        let check_sig = self
            .tcx
            .normalize_erasing_late_bound_regions(param_env, check_sig);

        let old_ty = *check_sig.inputs().last().unwrap();
        assert!(matches!(old_ty.kind(), ty::Tuple(_)));

        let old_dest_place = mir::Place::from(self.patcher().new_temp(old_ty, DUMMY_SP));

        let drop_block_data = mir::BasicBlockData::new(Some(mir::Terminator {
            source_info: dummy_source_info(),
            kind: mir::TerminatorKind::Goto {
                target: mir::BasicBlock::MAX,
            },
        }));
        let drop_start = self.patcher().new_block(drop_block_data);
        // construct arguments: first the arguments the function is called with, then the result of
        // that call, then the old values:
        let mut new_args = args.clone();
        new_args.push(mir::Operand::Move(result_operand));
        new_args.push(mir::Operand::Move(old_dest_place));

        // we store the target, create a new block per check function
        // chain these with the final call having the original target,
        // change the target of the call to the first block of our chain.
        let (check_block, _) = self
            .create_call_block(check_id, new_args, substs, None, Some(drop_start))
            .unwrap();

        // the terminator that calls the original function, but in this case jumps to
        // a check function after instead of original target
        // for now we just construct it, this does not modify the terminator
        // in the CFG yet
        let mut call_terminator = original_terminator;
        replace_target(&mut call_terminator, check_block);

        let (chain_start, new_caller, locals_to_drop) =
            self.prepend_old_cloning(call_terminator, old_dest_place, old_ty, args, true);

        // TODO: create testcases for calls that have no target.
        // Make sure they behave correctly in case of panic
        let (drop_chain_start, _) = self.create_drop_chain(locals_to_drop, target);
        // make drop_start point to this chain:
        self.patcher().patch_terminator(
            drop_start,
            mir::TerminatorKind::Goto {
                target: drop_chain_start,
            },
        );

        println!("chain starting at: {:?}", chain_start);
        // make the original caller_block point to the first clone block
        // after separate_terminator_from_block this is a goto so we don't break
        // anything
        self.patcher().patch_terminator(
            caller_block,
            mir::TerminatorKind::Goto {
                target: chain_start,
            },
        );
        (new_caller, Some(check_block))
    }
}

impl<'tcx, 'a> MutVisitor<'tcx> for PostconditionInserter<'tcx, 'a> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_terminator(
        &mut self,
        terminator: &mut mir::Terminator<'tcx>,
        location: mir::Location,
    ) {
        if let mir::TerminatorKind::Call {
            func,
            target,
            destination,
            args,
            ..
        } = &terminator.kind
        {
            if let Some((call_id, substs)) = func.const_fn_def() {
                let mut caller_block = location.block;
                let mut current_target = *target;
                let mut call_fn_terminator = terminator.clone();
                for check_id in self.body_info.specs.get_post_checks(&call_id) {
                    (caller_block, current_target) = self.surround_call_with_store_and_check(
                        check_id,
                        caller_block,
                        current_target,
                        *destination,
                        args.clone(),
                        substs,
                        terminator.clone(),
                    );
                    replace_target(&mut call_fn_terminator, current_target.unwrap());
                }
            }
        }
    }
}

impl<'tcx, 'a> MirModifier<'tcx> for PostconditionInserter<'tcx, 'a> {
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
