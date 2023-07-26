use crate::modify_mir::{
    mir_helper::*,
    mir_info_collector::{collect_mir_info, CheckBlockKind, MirInfo},
};
use prusti_interface::specs::typed::{CheckKind, DefSpecificationMap};
use prusti_rustc_interface::{
    data_structures::steal::Steal,
    interface::DEFAULT_QUERY_PROVIDERS,
    middle::{
        mir::{
            self, patch::MirPatch, pretty, visit::MutVisitor, BasicBlock, BasicBlockData, Body,
            Constant, ConstantKind, Operand, Place, Terminator, TerminatorKind,
        },
        ty::{self, TyCtxt, TyKind},
    },
    span::{
        def_id::{DefId, LocalDefId},
        DUMMY_SP,
    },
};
use rustc_hash::FxHashMap;

use std::{env, fs, io};

fn folder_present(name: &str) -> io::Result<bool> {
    let mut path = env::current_dir()?;
    path.push(name);
    let metadata = fs::metadata(path)?;
    Ok(metadata.is_dir())
}

pub(crate) fn mir_checked(
    tcx: TyCtxt<'_>,
    def: ty::WithOptConstParam<LocalDefId>,
) -> &Steal<Body<'_>> {
    // let's get the specifications collected by prusti :)
    // SAFETY: Is definitely not safe at the moment
    let specs_opt = unsafe { super::SPECS.clone() };

    if let Some(specs) = specs_opt {
        // get mir body before invoking drops_elaborated query, otherwise it will
        // be stolen
        let steal = (DEFAULT_QUERY_PROVIDERS.mir_drops_elaborated_and_const_checked)(tcx, def);
        let mut stolen = steal.steal();
        let def_id = stolen.source.def_id();
        if def_id.is_local() {
            println!("modifying mir for defid: {:?}", def_id);
        }

        let mut visitor = InsertChecksVisitor::new(tcx, specs, stolen.clone());
        visitor.visit_body(&mut stolen);

        // print mir of body:
        if let Ok(true) = folder_present("dump") {
            let mut dump_file =
                fs::File::create(format!("dump/dump_mir_adjusted_{:?}.txt", def_id)).unwrap();
            pretty::write_mir_fn(tcx, &stolen, &mut |_, _| Ok(()), &mut dump_file).unwrap();
        }

        tcx.alloc_steal_mir(stolen)
    } else {
        println!("the specs could not be collected");
        (DEFAULT_QUERY_PROVIDERS.mir_drops_elaborated_and_const_checked)(tcx, def)
    }
}

#[derive(Debug, Clone)]
pub struct PledgeToProcess<'tcx> {
    check: DefId,
    check_before_expiry: Option<DefId>,
    old_values_place: Place<'tcx>,
    before_expiry_place: Place<'tcx>,
    before_expiry_ty: ty::Ty<'tcx>,
    destination: Place<'tcx>,
    // the args the function was called with
    args: Vec<Operand<'tcx>>,
    substs: ty::subst::SubstsRef<'tcx>,
}

pub struct InsertChecksVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    specs: DefSpecificationMap,
    // expiration locations are not computed correctly for this stage of the mir.
    // expiration_locations: FxHashMap<DefId, FxHashMap<mir::Local, mir::Location>>,
    current_patcher: Option<MirPatch<'tcx>>,
    pledges_to_process: FxHashMap<mir::Local, PledgeToProcess<'tcx>>,
    current_def_id: Option<DefId>,
    body_copy: Body<'tcx>,
    // maps from function arguments to their copies in old state
    stored_arguments: FxHashMap<mir::Local, mir::Local>,
    mir_info: MirInfo,
}

impl<'tcx> InsertChecksVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, specs: DefSpecificationMap, body_copy: Body<'tcx>) -> Self {
        let mir_info = collect_mir_info(tcx, body_copy.clone());
        Self {
            tcx,
            specs,
            current_patcher: None,
            pledges_to_process: Default::default(),
            current_def_id: None,
            body_copy,
            stored_arguments: Default::default(),
            mir_info,
        }
    }
}

impl<'tcx> MutVisitor<'tcx> for InsertChecksVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_body(&mut self, body: &mut Body<'tcx>) {
        // visit body, apply patches, possibly find pledges that need to be processed here:
        let def_id = body.source.def_id();
        self.current_def_id = Some(def_id);

        // create locals for the clones of old, and replace them where needed
        self.create_and_replace_arguments(body);

        self.current_patcher = Some(MirPatch::new(body));
        self.super_body(body);
        let mir_patch = self.current_patcher.take();
        mir_patch.unwrap().apply(body);

        // sort descending
        // this would insert the pledges correctly, if locations
        // were reported correctly. For now, we only insert
        // checks for pledges if there are manual
        // `prusti_pledge_expires` annotations
        // self.pledges_to_process
        //     .sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap().reverse());
        //
        // self.pledges_to_process
        //     .iter()
        //     .for_each(|(location, pledge)| {
        //         insert_pledge_call_chain(self.tcx, pledge.clone(), *location, body).unwrap();
        //     });

        // All the modifications that we do after this point, insert blocks
        // that have to be executed before anything else in this function.
        // Therefore we create one dummy block, make it goto the starting block
        // and swap these blocks locations.
        // While we will be prepending calls before the first block,
        // `current_target` will keep track of which block this dummy block
        // currently points to, so we can keep prepending new blocks
        let mut current_target = prepend_dummy_block(body);

        self.mir_info
            .args_to_be_cloned
            .clone()
            .iter()
            .for_each(|&local| {
                let mut patch = MirPatch::new(body);
                let place: mir::Place = local.into();
                let destination = *self.stored_arguments.get(&local).unwrap();
                (current_target, _) = self
                    .insert_clone_argument(place, current_target, Some(destination), &mut patch)
                    .unwrap();
                let terminator_kind = TerminatorKind::Goto {
                    target: current_target,
                };
                patch.patch_terminator(mir::START_BLOCK, terminator_kind);
                patch.apply(body);
            });

        // replace function arguments with their copies in all the locations
        // that we identified earlier:

        // insert preconditions at the beginning of the body:
        let substs = ty::subst::InternalSubsts::identity_for_item(self.tcx, def_id);
        let args = args_from_body(body);
        for check_id in self.specs.get_pre_checks(&def_id) {
            let mut patch = MirPatch::new(body);
            let (current_target, _) = create_call_block(
                self.tcx,
                &mut patch,
                check_id,
                args.clone(),
                substs,
                None, // create new destination, does not matter here
                Some(current_target),
            )
            .unwrap();
            // make dummy block at the very beginning go to this block now:

            let terminator_kind = TerminatorKind::Goto {
                target: current_target,
            };
            patch.patch_terminator(mir::START_BLOCK, terminator_kind);
            patch.apply(body);
        }
    }

    fn visit_terminator(&mut self, terminator: &mut Terminator<'tcx>, location: mir::Location) {
        self.super_terminator(terminator, location);
        if let TerminatorKind::SwitchInt { targets, .. } = &mut terminator.kind {
            // find switchInts with a check_only target.
            let switch_iter = targets.iter();
            if switch_iter.len() == 1 {
                // let (value, target) = switch_iter.next().unwrap();
                let otherwise = targets.otherwise();
                // check if target is a check_block:
                if let Some(kind) = self.mir_info.check_blocks.get(&otherwise) {
                    match kind {
                        CheckBlockKind::PledgeExpires(local) => {
                            // this check_block should terminate with a goto always!
                            if let TerminatorKind::Goto { target } =
                                self.body_copy[otherwise].terminator.clone().unwrap().kind
                            {
                                let pledge = self
                                    .pledges_to_process
                                    .get(local)
                                    .expect("pledge expiration without an actual pledge");
                                let mut patcher = self.current_patcher.take().unwrap();
                                let start_block = self.create_pledge_call_chain(
                                    pledge,
                                    target,
                                    &mut patcher,
                                )
                                .unwrap();

                                let new_terminator = TerminatorKind::Goto {
                                    target: start_block,
                                };
                                // skip this check block and instead call checks-chain
                                patcher.patch_terminator(otherwise, new_terminator);
                                self.current_patcher = Some(patcher)
                            }
                        }
                        // nothing to do..
                        CheckBlockKind::RuntimeAssertion => (),
                    }
                }
            }
        }
    }

    fn visit_basic_block_data(&mut self, block: BasicBlock, data: &mut BasicBlockData<'tcx>) {
        // our goal here is to find calls to functions where we want to check
        // their precondition afterwards
        self.super_basic_block_data(block, data);
        // we will be adding blocks and new blocks will be representing the
        // main block, this variable is used to update it.

        if let Some(Terminator {
            kind: terminator_kind,
            ..
        }) = &data.terminator
        {
            // the block that actually calls the annotated function. The terminator
            // that calls this function is potentially moved several times,
            // this variable keeps track of that.
            let mut caller_block = block;
            let mut call_fn_terminator = data.terminator.clone().unwrap().clone();

            if let TerminatorKind::Call {
                func,
                target,      // the block called afterwards
                destination, // local to receive result
                args,
                ..
            } = terminator_kind
            {
                // if it's a static function call, we start looking if there are
                // post-conditions we could check
                if let Some((call_id, substs)) = func.const_fn_def() {
                    // let item_name = self.tcx.def_path_str(call_id);
                    // make sure the call is local:

                    // The block that is executed after the annotated function
                    // is called. Mutable copy because after appending the first
                    // check function call, this is the new target
                    let mut current_target = *target;
                    // since there might be multiple blocks to be inserted,
                    for check_kind in self.specs.get_runtime_checks(&call_id) {
                        match check_kind {
                            CheckKind::Pre(check_id) => {
                                // only insert check if called method is not local!
                                if call_id.is_local() {
                                    continue;
                                } else {
                                    let mut patch = self.current_patcher.take().unwrap();
                                    let return_ty = fn_return_ty(self.tcx, check_id);
                                    assert!(return_ty.is_unit());
                                    let res = patch.new_temp(return_ty, DUMMY_SP);
                                    caller_block = self.prepend_call(
                                        &mut patch,
                                        check_id,
                                        caller_block,
                                        args.clone(),
                                        substs,
                                        call_fn_terminator.clone(),
                                        res.into(),
                                    );
                                    self.current_patcher = Some(patch);
                                }
                            }
                            CheckKind::Post { check: check_id } => {
                                // since here, we don't have mutable access to the body,
                                // we created a patcher beforehand which we can use here
                                // and apply later
                                let mut patch = self.current_patcher.take().unwrap();
                                (caller_block, current_target) = self
                                    .surround_call_with_store_and_check(
                                        &mut patch,
                                        check_id,
                                        caller_block,
                                        current_target,
                                        *destination,
                                        args.clone(),
                                        substs,
                                        call_fn_terminator.clone(),
                                    );
                                replace_target(&mut call_fn_terminator, current_target.unwrap());

                                // If there are multiple checks, this also should behave
                                // correctly, since on the second iteration this target
                                // is already the new block
                                self.current_patcher = Some(patch);
                            }
                            CheckKind::Pledge {
                                check,
                                check_before_expiry,
                            } => {
                                // get patcher:
                                let mut patch = self.current_patcher.take().unwrap();
                                // 1. store old values, create local:
                                let check_sig = self.tcx.fn_sig(check).subst(self.tcx, substs);
                                let check_sig = self.tcx.normalize_erasing_late_bound_regions(
                                    ty::ParamEnv::reveal_all(),
                                    check_sig,
                                );
                                let inputs = check_sig.inputs();
                                let old_values_ty = inputs[inputs.len() - 2];
                                let before_expiry_ty = inputs[inputs.len() - 1];

                                let old_values_place =
                                    Place::from(patch.new_temp(old_values_ty, DUMMY_SP));
                                // store_before_expiry has to always exist?
                                // if yes:
                                let before_expiry_place =
                                    Place::from(patch.new_temp(before_expiry_ty, DUMMY_SP));

                                let (chain_start, new_caller) = self.prepend_old_cloning(
                                    &mut patch,
                                    call_fn_terminator.clone(),
                                    old_values_place,
                                    old_values_ty,
                                    args.clone(),
                                );
                                patch.patch_terminator(
                                    caller_block,
                                    TerminatorKind::Goto {
                                        target: chain_start,
                                    },
                                );
                                caller_block = new_caller;

                                // *destination is the loan!
                                // figure out where it expires!
                                let pledge_to_process = PledgeToProcess {
                                    check,
                                    check_before_expiry,
                                    old_values_place,
                                    before_expiry_place,
                                    before_expiry_ty,
                                    destination: *destination,
                                    args: args.clone(),
                                    substs,
                                };
                                self.pledges_to_process
                                    .insert(destination.local, pledge_to_process);

                                self.current_patcher = Some(patch);
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
    }
}

impl<'tcx> InsertChecksVisitor<'tcx> {
    fn insert_clone_argument(
        &self,
        arg: mir::Place<'tcx>,
        target: BasicBlock,
        destination: Option<mir::Local>,
        patch: &mut MirPatch<'tcx>,
    ) -> Result<(BasicBlock, mir::Local), ()> {
        // if we deal with a reference, we can directly call clone on it
        // otherwise we have to create a reference first, to pass to the clone
        // function.
        let clone_defid = get_clone_defid(self.tcx).ok_or(())?;
        // let clone_trait_defid = self.tcx.lang_items().clone_trait().unwrap();
        let arg_ty = make_immutable(self.tcx, arg.ty(&self.body_copy.local_decls, self.tcx).ty);
        println!("arg type: {:?}", arg_ty);

        let dest = destination.unwrap_or_else(|| patch.new_temp(arg_ty, DUMMY_SP));
        println!(
            "trying to clone arg: {:?} into destination: {:?}",
            arg, dest
        );
        if !arg_ty.is_ref() {
            println!("handling a non-ref old arg");
            let ref_ty = create_reference_type(self.tcx, arg_ty);
            let ref_arg = patch.new_temp(ref_ty, DUMMY_SP);
            // add a statement to deref the old_argument
            let rvalue = rvalue_reference_to_local(self.tcx, arg, false);
            // the statement to be added to the block that has the call clone
            // terminator
            let ref_stmt = mir::StatementKind::Assign(box (mir::Place::from(ref_arg), rvalue));

            // create the substitution since clone is generic:
            let generic_ty = ty::subst::GenericArg::from(arg_ty);
            let substs = self.tcx.mk_substs(&[generic_ty]);
            // create the function operand:
            let clone_args = vec![Operand::Move(mir::Place::from(ref_arg))];
            // create a new basicblock:
            let (new_block, _) = create_call_block(
                self.tcx,
                patch,
                clone_defid,
                clone_args,
                substs,
                Some(dest.into()),
                Some(target),
            )?;
            patch.add_statement(
                mir::Location {
                    block: new_block,
                    statement_index: 0,
                },
                ref_stmt,
            );

            Ok((new_block, dest))
            // let block_data = BasicBlockData::new()
        } else {
            // create a new local to store the result of clone:
            let deref_ty = arg_ty.builtin_deref(false).ok_or(())?.ty;
            println!("dereferenced type: {:?}", deref_ty);
            let clone_dest = patch.new_temp(deref_ty, DUMMY_SP);
            let generic_ty = ty::subst::GenericArg::from(deref_ty);
            let substs = self.tcx.mk_substs(&[generic_ty]);
            let clone_args = vec![Operand::Move(arg)];
            // add an additional simple block afterwards, that dereferences
            // the the cloned value into the original receiver of old:
            // create it beforehand, so we can set the precedors target correctly
            let terminator = mir::Terminator {
                source_info: dummy_source_info(),
                kind: TerminatorKind::Goto { target },
            };
            let block_data = BasicBlockData::new(Some(terminator));
            let second_block = patch.new_block(block_data);

            // borrow the clone result
            let rvalue = rvalue_reference_to_local(self.tcx, clone_dest.into(), false);
            let ref_stmt = mir::StatementKind::Assign(box (dest.into(), rvalue));
            patch.add_statement(
                mir::Location {
                    block: second_block,
                    statement_index: 0,
                },
                ref_stmt,
            );

            let (new_block, _) = create_call_block(
                self.tcx,
                patch,
                clone_defid,
                clone_args,
                substs,
                Some(clone_dest.into()),
                Some(second_block),
            )?;

            Ok((new_block, dest))
        }
    }

    pub fn create_and_replace_arguments(&mut self, body: &mut Body<'tcx>) {
        let mut patcher = MirPatch::new(body);
        for arg in &self.mir_info.args_to_be_cloned {
            let ty = make_immutable(self.tcx, body.local_decls.get(*arg).unwrap().ty);
            let new_var = patcher.new_temp(ty, DUMMY_SP);
            self.stored_arguments.insert(*arg, new_var);
        }
        let mut replacer = ArgumentReplacer::new(self.tcx, &self.stored_arguments);
        for (block, bb_data) in body.basic_blocks_mut().iter_enumerated_mut() {
            for (statement_index, stmt) in bb_data.statements.iter_mut().enumerate() {
                let loc = mir::Location {
                    block,
                    statement_index,
                };
                if self.mir_info.stmts_to_substitute_rhs.contains(&loc) {
                    replacer.visit_statement(stmt, loc);
                }
            }
        }
        patcher.apply(body);
    }

    #[allow(clippy::too_many_arguments)]
    fn surround_call_with_store_and_check(
        &self,
        patch: &mut MirPatch<'tcx>,
        check_id: DefId,
        caller_block: BasicBlock,
        target: Option<BasicBlock>,
        result_operand: Place<'tcx>,
        args: Vec<Operand<'tcx>>,
        substs: ty::subst::SubstsRef<'tcx>,
        original_terminator: Terminator<'tcx>,
    ) -> (BasicBlock, Option<BasicBlock>) {
        // find the type of that local
        let check_sig = self.tcx.fn_sig(check_id).subst(self.tcx, substs);
        let check_sig = self
            .tcx
            .normalize_erasing_late_bound_regions(ty::ParamEnv::reveal_all(), check_sig);

        let old_ty = *check_sig.inputs().last().unwrap();
        assert!(matches!(old_ty.kind(), ty::Tuple(_)));

        let old_dest_place = Place::from(patch.new_temp(old_ty, DUMMY_SP));

        // construct arguments: first the arguments the function is called with, then the result of
        // that call, then the old values:
        let mut new_args = args.clone();
        new_args.push(Operand::Move(result_operand));
        new_args.push(Operand::Move(old_dest_place));

        // we store the target, create a new block per check function
        // chain these with the final call having the original target,
        // change the target of the call to the first block of our chain.
        let (check_block, _) =
            create_call_block(self.tcx, patch, check_id, new_args, substs, None, target).unwrap();

        // the terminator that calls the original function, but in this case jumps to
        // a check function after instead of original target
        // for now we just construct it, this does not modify the terminator
        // in the CFG yet
        let mut call_terminator = original_terminator;
        replace_target(&mut call_terminator, check_block);

        let (chain_start, new_caller) =
            self.prepend_old_cloning(patch, call_terminator, old_dest_place, old_ty, args);

        println!("chain starting at: {:?}", chain_start);
        // make the original caller_block point to the first clone block
        // after separate_terminator_from_block this is a goto so we don't break
        // anything
        patch.patch_terminator(
            caller_block,
            TerminatorKind::Goto {
                target: chain_start,
            },
        );
        (new_caller, Some(check_block))
    }

    fn prepend_old_cloning(
        &self,
        patch: &mut MirPatch<'tcx>,
        terminator: Terminator<'tcx>,
        old_dest_place: mir::Place<'tcx>,
        old_ty: ty::Ty<'tcx>,
        args: Vec<Operand<'tcx>>,
    ) -> (BasicBlock, BasicBlock) {
        let new_block_data = BasicBlockData::new(Some(terminator));
        let current_caller = patch.new_block(new_block_data);
        let mut current_target = current_caller;

        let mut old_tuple = Vec::new();
        let old_tuple_fields = old_ty.tuple_fields();
        for (id, operand) in args.iter().enumerate() {
            let old_values_ty = old_tuple_fields.get(id).unwrap();
            if old_values_ty.is_unit() {
                // we already know from ast, that this variable does not need
                // to be cloned
                let unit_const = unit_const(self.tcx);
                old_tuple.push(unit_const);
            } else {
                match operand {
                    mir::Operand::Constant(_) => {
                        old_tuple.push(operand.clone());
                    }
                    mir::Operand::Move(place) | mir::Operand::Copy(place) => {
                        // prepends clone blocks before the actual function is called
                        let (start_block, destination) = self
                            .insert_clone_argument(*place, current_target, None, patch)
                            .unwrap();
                        current_target = start_block;
                        // add the result to our tuple:
                        old_tuple.push(mir::Operand::Move(destination.into()));
                    }
                }
            }
        }
        let old_rvalue = mir::Rvalue::Aggregate(box mir::AggregateKind::Tuple, old_tuple);
        let stmt_kind = mir::StatementKind::Assign(box (old_dest_place, old_rvalue));
        let location = mir::Location {
            block: current_caller,
            statement_index: 0,
        };
        patch.add_statement(location, stmt_kind);

        // (start of clone-chain, block calling annotated function)
        (current_target, current_caller)
    }

    /// Given a function call, prepend another function call directly before
    /// it. Done by moving the existing call to a new block, replacing the
    /// terminator of the existing block with a new call jumping to the new block
    #[allow(clippy::too_many_arguments)]
    fn prepend_call(
        &self,
        patcher: &mut MirPatch<'tcx>,
        fn_id: DefId,
        caller_block: BasicBlock,
        args: Vec<Operand<'tcx>>,
        substs: ty::subst::SubstsRef<'tcx>,
        terminator: Terminator<'tcx>,
        dest_place: Place<'tcx>,
    ) -> BasicBlock {
        // get the bodies of the store and check function
        let new_block_data = BasicBlockData::new(Some(terminator));
        let new_block = patcher.new_block(new_block_data);

        let func_ty = self.tcx.mk_ty_from_kind(TyKind::FnDef(fn_id, substs));
        let func = Operand::Constant(Box::new(Constant {
            span: DUMMY_SP,
            user_ty: None,
            literal: ConstantKind::zero_sized(func_ty),
        }));

        let terminator = TerminatorKind::Call {
            func,
            args: args.clone(),
            destination: dest_place,
            target: Some(new_block),
            cleanup: None,
            from_hir_call: false,
            fn_span: DUMMY_SP,
        };
        // the block that initially calls the check function, now calls the store
        // function
        patcher.patch_terminator(caller_block, terminator);
        new_block
    }

    fn create_pledge_call_chain(
        &self,
        pledge: &PledgeToProcess<'tcx>,
        target: BasicBlock,
        patcher: &mut MirPatch<'tcx>,
    ) -> Result<BasicBlock, ()> {
        // given a location, insert the call chain to check a pledge:
        // since we need to know the targets for each call, the blocks need to be created
        // in reversed order.

        // Create call to check function:
        let mut check_args = pledge.args.clone();
        check_args.push(Operand::Move(pledge.destination)); //result arg
        check_args.push(Operand::Move(pledge.old_values_place));
        check_args.push(Operand::Move(pledge.before_expiry_place));
        let (check_after_block, _) = create_call_block(
            self.tcx,
            patcher,
            pledge.check,
            check_args,
            pledge.substs,
            None,
            Some(target),
        )?;

        // If there is a check_before_expiry block, creat it
        let next_target = if let Some(check_before_expiry) = pledge.check_before_expiry {
            let before_check_args = vec![
                Operand::Move(pledge.destination),
                Operand::Move(pledge.old_values_place),
            ];
            let (new_block, _) = create_call_block(
                self.tcx,
                patcher,
                check_before_expiry,
                before_check_args,
                pledge.substs,
                None,
                Some(check_after_block),
            )?;
            new_block
        } else {
            check_after_block
        };

        // 1. Call store_before_expiry, result of original call is pledge.destination
        let args = vec![Operand::Move(pledge.destination)];
        let terminator = mir::Terminator {
            source_info: dummy_source_info(),
            kind: mir::TerminatorKind::Goto {
                target: next_target,
            },
        };
        let (clone_chain_start, _) = self.prepend_old_cloning(patcher, terminator, pledge.before_expiry_place, pledge.before_expiry_ty, args);

        Ok(clone_chain_start)
    }
}
