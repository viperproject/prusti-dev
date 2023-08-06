use crate::modify_mir::mir_helper::dummy_source_info;

use super::super::{
    mir_info_collector::{CheckBlockKind, MirInfo},
    mir_modifications::MirModifier,
};
use prusti_interface::specs::typed::CheckKind;
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

pub struct PledgeInserter<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body_info: &'a MirInfo<'tcx>,
    patch_opt: Option<RefCell<MirPatch<'tcx>>>,
    pledges_to_process: FxHashMap<mir::Local, PledgeToProcess<'tcx>>,
    body_copy: Option<mir::Body<'tcx>>,
    def_id: DefId,
    local_decls: &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
}

#[derive(Debug, Clone)]
pub struct PledgeToProcess<'tcx> {
    pub check: DefId,
    pub check_before_expiry: Option<DefId>,
    pub old_values_place: mir::Place<'tcx>,
    pub before_expiry_place: mir::Place<'tcx>,
    pub before_expiry_ty: ty::Ty<'tcx>,
    pub destination: mir::Place<'tcx>,
    // the args the function was called with
    pub args: Vec<mir::Operand<'tcx>>,
    pub substs: ty::subst::SubstsRef<'tcx>,
    pub locals_to_drop: Vec<mir::Local>,
    // a local that is set when a function with a pledge is called
    // and then checked before a runtime check at an expiration location
    // is performed.
    pub guard_place: mir::Place<'tcx>,
}

impl<'tcx, 'a> PledgeInserter<'tcx, 'a> {
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
            pledges_to_process: Default::default(),
            body_copy: None,
            def_id,
            local_decls,
        }
    }

    pub fn run(&mut self, body: &mut mir::Body<'tcx>) {
        self.body_copy = Some(body.clone());
        self.patch_opt = Some(MirPatch::new(body).into());
        // find all calls to functions with pledges, and create local variables
        // to store: old_values, before_expiry_place,
        self.visit_body(body);
        // apply the patch generated during visitation
        let patcher_ref = self.patch_opt.take().unwrap();
        patcher_ref.into_inner().apply(body);
    }

    pub fn set_guard_true_block(
        &self,
        destination: mir::Place<'tcx>,
        target: mir::BasicBlock,
    ) -> mir::BasicBlock {
        let stmt_kind = self.set_bool_stmt(destination, true);
        let stmt = mir::Statement {
            source_info: dummy_source_info(),
            kind: stmt_kind,
        };
        let terminator = mir::Terminator {
            source_info: dummy_source_info(),
            kind: mir::TerminatorKind::Goto { target },
        };
        let mut new_block = mir::BasicBlockData::new(Some(terminator));
        new_block.statements.push(stmt);
        self.patcher().new_block(new_block)
    }
}

impl<'tcx, 'a> MutVisitor<'tcx> for PledgeInserter<'tcx, 'a> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_terminator(
        &mut self,
        terminator: &mut mir::Terminator<'tcx>,
        location: mir::Location,
    ) {
        match &terminator.kind {
            mir::TerminatorKind::Call {
                func,
                destination,
                args,
                ..
            } => {
                // is a visit of the underlying things even necesary?
                if let Some((call_id, substs)) = func.const_fn_def() {
                    // a.t.m there can only be one pledge, we ignore that
                    let mut caller_block = location.block;
                    for check_kind in self.body_info.specs.get_runtime_checks(&call_id) {
                        if let CheckKind::Pledge {
                            check,
                            check_before_expiry,
                        } = check_kind
                        {
                            // TODO: pack that into a function, use correct param_env
                            let check_sig = self.tcx.fn_sig(check).subst(self.tcx, substs);
                            let check_sig = self.tcx.normalize_erasing_late_bound_regions(
                                ty::ParamEnv::reveal_all(),
                                check_sig,
                            );
                            let inputs = check_sig.inputs();
                            let old_values_ty = inputs[inputs.len() - 2];
                            let before_expiry_ty = inputs[inputs.len() - 1];
                            let old_values_place =
                                mir::Place::from(self.patcher().new_temp(old_values_ty, DUMMY_SP));
                            let before_expiry_place = mir::Place::from(
                                self.patcher().new_temp(before_expiry_ty, DUMMY_SP),
                            );

                            let bool_ty = self.tcx.mk_ty_from_kind(ty::TyKind::Bool);
                            let local_guard = self.patcher().new_temp(bool_ty, DUMMY_SP).into();

                            // create the clones of old that will be passed to
                            // the check function. Make the chain end with the
                            // original function call
                            let (chain_start, new_caller, locals_to_drop) = self
                                .prepend_old_cloning(
                                    terminator.clone(),
                                    old_values_place,
                                    old_values_ty,
                                    args.clone(),
                                    true,
                                );
                            let set_guard_block =
                                self.set_guard_true_block(local_guard, chain_start);
                            // of our function
                            self.patcher().patch_terminator(
                                caller_block,
                                mir::TerminatorKind::Goto {
                                    target: set_guard_block,
                                },
                            );
                            // update the call_location (just in case there are
                            // ever multiple pleges in the future)
                            caller_block = new_caller;
                            let pledge_to_process = PledgeToProcess {
                                check,
                                check_before_expiry,
                                old_values_place,
                                before_expiry_place,
                                before_expiry_ty,
                                destination: *destination,
                                args: args.clone(),
                                substs,
                                locals_to_drop,
                                guard_place: local_guard,
                            };
                            // TODO: create a test where the result is assigned
                            // to the field of a tuple
                            self.pledges_to_process
                                .insert(destination.local, pledge_to_process);
                        }
                    }
                }
            }
            mir::TerminatorKind::SwitchInt { targets, .. } => {
                // find switchInts with a check_only target.
                let switch_iter = targets.iter();
                if switch_iter.len() == 1 {
                    // let (value, target) = switch_iter.next().unwrap();
                    let otherwise = targets.otherwise();
                    // check if target is a check_block:
                    if let Some(kind) = self.body_info.check_blocks.get(&otherwise) {
                        match kind {
                            CheckBlockKind::PledgeExpires(local) => {
                                // this check_block should terminate with a goto always!
                                if let mir::TerminatorKind::Goto { ref target } =
                                    self.body_copy.as_ref().unwrap()[otherwise]
                                        .terminator
                                        .clone()
                                        .unwrap()
                                        .kind
                                {
                                    let pledge = self.pledges_to_process.get(local).expect(
                                        "pledge expiration without an actual pledge,\
                                                seems like our assumption that calls of pledges are\
                                                always encountered before the expiration is wrong",
                                    );
                                    let start_block =
                                        self.create_pledge_call_chain(pledge, *target).unwrap();

                                    let new_terminator = mir::TerminatorKind::Goto {
                                        target: start_block,
                                    };
                                    // skip this check block and instead call checks-chain
                                    self.patcher().patch_terminator(otherwise, new_terminator);
                                }
                            }
                            // nothing to do..
                            CheckBlockKind::RuntimeAssertion => (),
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

impl<'tcx, 'a> MirModifier<'tcx> for PledgeInserter<'tcx, 'a> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn patcher(&self) -> RefMut<MirPatch<'tcx>> {
        self.patch_opt
            .as_ref()
            .expect("Bug: MirPatch was not initialized for MirModifier")
            .borrow_mut()
    }

    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn local_decls(&self) -> &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>> {
        self.local_decls
    }
}
