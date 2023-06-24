use crate::{
    mir_helper::*,
    mir_info_collector::{collect_mir_info, CheckBlockKind, MirInfo},
};
use prusti_interface::{
    environment::{is_marked_check_block, EnvQuery},
    specs::typed::{CheckKind, DefSpecificationMap},
};
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
use rustc_hash::{FxHashMap, FxHashSet};

use std::{env, fs, io};

fn folder_present(name: &str) -> io::Result<bool> {
    let mut path = env::current_dir()?;
    path.push(name);
    let metadata = fs::metadata(path)?;
    Ok(metadata.is_dir())
}

pub static mut SPECS: Option<DefSpecificationMap> = None;
pub static mut EXPIRATION_LOCATIONS: Option<
    FxHashMap<DefId, FxHashMap<mir::Local, mir::Location>>,
> = None;

pub(crate) fn mir_checked(
    tcx: TyCtxt<'_>,
    def: ty::WithOptConstParam<LocalDefId>,
) -> &Steal<Body<'_>> {
    // let's get the specifications collected by prusti :)
    // SAFETY: Is definitely not safe at the moment
    let specs_opt = unsafe { SPECS.clone() };

    if let Some(specs) = specs_opt {
        let expiration_locations = unsafe { EXPIRATION_LOCATIONS.clone().unwrap() };
        // get mir body before invoking drops_elaborated query, otherwise it will
        // be stolen
        let steal = (DEFAULT_QUERY_PROVIDERS.mir_drops_elaborated_and_const_checked)(tcx, def);
        let mut stolen = steal.steal();
        let def_id = stolen.source.def_id();
        if def_id.is_local() {
            println!("modifying mir for defid: {:?}", def_id);
        }

        let mut visitor =
            InsertChecksVisitor::new(tcx, specs, expiration_locations, stolen.clone());
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

// #[derive(Debug, Clone)]
// pub enum ModificationToProcess<'tcx> {
//     Pledge(PledgeToProcess<'tcx>),
//     OldCall(OldCallToProcess),
// }

#[derive(Debug, Clone)]
pub struct PledgeToProcess<'tcx> {
    check: DefId,
    store_before_expiry: DefId,
    check_before_expiry: Option<DefId>,
    old_values_place: Place<'tcx>,
    before_expiry_place: Place<'tcx>,
    destination: Place<'tcx>,
    // the args the function was called with
    args: Vec<Operand<'tcx>>,
    substs: ty::subst::SubstsRef<'tcx>,
}

#[derive(Debug, Clone, Copy)]
pub struct OldCallToProcess<'tcx> {
    /// the local where the result of cloning should be stored in
    stored_local: mir::Local,
    /// the argument that should be stored
    arg_to_store: mir::Local,
    /// the type of the argument (and result) of the old call:
    ty: ty::Ty<'tcx>,
}

pub struct InsertChecksVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    specs: DefSpecificationMap,
    expiration_locations: FxHashMap<DefId, FxHashMap<mir::Local, mir::Location>>,
    current_patcher: Option<MirPatch<'tcx>>,
    pledges_to_process: FxHashMap<mir::Local, PledgeToProcess<'tcx>>,
    old_calls_to_process: Vec<OldCallToProcess<'tcx>>,
    current_def_id: Option<DefId>,
    body_copy: Body<'tcx>,
    stored_arguments: FxHashSet<mir::Local>,
    mir_info: MirInfo,
    env_query: EnvQuery<'tcx>,
}

impl<'tcx> InsertChecksVisitor<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        specs: DefSpecificationMap,
        expiration_locations: FxHashMap<DefId, FxHashMap<mir::Local, mir::Location>>,
        body_copy: Body<'tcx>,
    ) -> Self {
        let mir_info = collect_mir_info(tcx, body_copy.clone());
        let env_query = EnvQuery::new(tcx);
        Self {
            tcx,
            specs,
            current_patcher: None,
            pledges_to_process: Default::default(),
            old_calls_to_process: Vec::new(),
            expiration_locations,
            current_def_id: None,
            body_copy,
            stored_arguments: FxHashSet::default(),
            mir_info,
            env_query,
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

        self.old_calls_to_process.iter().for_each(|to_process| {
            let mut patch = MirPatch::new(body);
            current_target = self
                .process_old_call(*to_process, current_target, &mut patch)
                .unwrap();
            let terminator_kind = TerminatorKind::Goto {
                target: current_target,
            };
            patch.patch_terminator(mir::START_BLOCK, terminator_kind);
            patch.apply(body);
        });

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
        match &mut terminator.kind {
            // find switchInts with a check_only target.
            TerminatorKind::SwitchInt { targets, .. } => {
                let mut switch_iter = targets.iter();
                if switch_iter.len() == 1 {
                    let (value, target) = switch_iter.next().unwrap();
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
                                        .get(&local)
                                        .expect("pledge expiration without an actual pledge");
                                    let mut patcher = self.current_patcher.take().unwrap();
                                    let start_block = create_pledge_call_chain(
                                        self.tcx,
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
            _ => (),
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
                    let item_name = self.tcx.def_path_str(call_id);
                    // make sure the call is local:
                    if !call_id.is_local() {
                        // extern specs will need to be handled here.

                        if item_name == "prusti_contracts::old".to_string() {
                            // old calls can still exist here. Find them, replace
                            // with new locals
                            println!("found old call!");
                            let to_process_opt = self
                                .handle_old_call(destination.local, args.clone())
                                .unwrap();
                            if let Some(to_process) = to_process_opt {
                                self.old_calls_to_process.push(to_process);
                                // in this case we also need to replace the old call
                                let new_terminator_kind = mir::TerminatorKind::Goto {
                                    // target can only be none if the call diverges
                                    // TODO: discuss if this can ever happen here.
                                    // I don't think it should..
                                    target: target.unwrap(),
                                };
                                let mut patch = self.current_patcher.take().unwrap();
                                patch.patch_terminator(block, new_terminator_kind);
                                self.current_patcher = Some(patch);
                            }
                            return;
                        }
                    }

                    // The block that is executed after the annotated function
                    // is called. Mutable copy because after appending the first
                    // check function call, this is the new target
                    let mut current_target = *target;
                    // since there might be multiple blocks to be inserted,
                    for check_kind in self.specs.get_runtime_checks(&call_id) {
                        match check_kind {
                            CheckKind::Post {
                                check: check_id,
                                old_store: old_store_id,
                            } => {
                                // since here, we don't have mutable access to the body,
                                // we created a patcher beforehand which we can use here
                                // and apply later
                                let mut patch = self.current_patcher.take().unwrap();
                                (caller_block, current_target) = surround_call_with_store_and_check(
                                    self.tcx,
                                    &mut patch,
                                    check_id,
                                    old_store_id,
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
                                old_store,
                                check_before_expiry,
                                store_before_expiry,
                            } => {
                                // get patcher:
                                let mut patch = self.current_patcher.take().unwrap();
                                // 1. store old values, create local:
                                let old_values_ty = fn_return_ty(self.tcx, old_store);
                                let old_values_place =
                                    Place::from(patch.new_internal(old_values_ty, DUMMY_SP));
                                // store_before_expiry has to always exist?
                                // if yes:
                                let before_expiry_ty = fn_return_ty(self.tcx, store_before_expiry);
                                let before_expiry_place =
                                    Place::from(patch.new_internal(before_expiry_ty, DUMMY_SP));

                                caller_block = prepend_store(
                                    self.tcx,
                                    &mut patch,
                                    old_store,
                                    caller_block,
                                    args.clone(),
                                    substs,
                                    call_fn_terminator.clone(),
                                    old_values_place,
                                );

                                // *destination is the loan!
                                // figure out where it expires!
                                let pledge_to_process = PledgeToProcess {
                                    check,
                                    check_before_expiry,
                                    store_before_expiry,
                                    old_values_place,
                                    before_expiry_place,
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
    /// If we encounter an old call with an argument that is also a mutable
    /// argument of the original function, we need to replace it with a cloned
    /// value!
    /// If it's a reference, cloning it will dereference it, so we need an
    /// additional local!
    /// Returns Ok(None) if nothing went wrong, but there is no modification
    /// to be processed
    fn handle_old_call(
        &mut self,
        receiver: mir::Local,
        args: Vec<Operand<'tcx>>,
    ) -> Result<Option<OldCallToProcess<'tcx>>, ()> {
        // check if the argument given to old is a mutable argument:
        // (if interior mutability is supported in the future, this might have
        // to be extended, since even immutable references would have to be
        // "cloned", even though normal cloning is not enough anymore then.)
        // the argument should always be a single local:
        assert!(args.len() == 1, "old was given more than one argument??");
        let old_argument = local_from_operand(&args[0])?;
        // argument locals are never passed directly to the function,
        // so we have to look up if this argument to old is a copy / move
        // of a function argument.
        if let Some(original_argument) = self.mir_info.moved_args.get(&old_argument) {
            println!("found a copy of a function argument!");
            // also check that we have not yet created a variable storing this local
            if self.stored_arguments.get(original_argument).is_some() {
                return Ok(None);
            } else {
                self.stored_arguments.insert(*original_argument);
            }

            // this is already checked during creationg of moved_arguments
            // if is_mutable_arg(&self.body_copy, original_argument) {
            //     println!("We have to store an old_arg!");
            // }

            let arg_ty = get_locals_type(&self.body_copy, *original_argument)?;
            Ok(Some(OldCallToProcess {
                stored_local: receiver,
                arg_to_store: *original_argument,
                ty: arg_ty,
            }))
        } else {
            // this is not a local we need to store!
            Ok(None)
        }
    }

    fn process_old_call(
        &self,
        to_process: OldCallToProcess<'tcx>,
        target: BasicBlock,
        patch: &mut MirPatch<'tcx>,
    ) -> Result<BasicBlock, ()> {
        // if we deal with a reference, we can directly call clone on it
        // otherwise we have to create a reference first, to pass to the clone
        // function.
        let clone_defid = get_clone_defid(self.tcx).ok_or(())?;
        let clone_trait_defid = self.tcx.lang_items().clone_trait().unwrap();
        if !to_process.ty.is_ref() {
            println!("handling a non-ref old arg");
            let ref_ty = create_reference_type(self.tcx, to_process.ty);
            let ref_arg = patch.new_internal(ref_ty, DUMMY_SP);
            // add a statement to deref the old_argument
            let rvalue = rvalue_reference_to_local(self.tcx, to_process.arg_to_store, false);
            // the statement to be added to the block that has the call clone
            // terminator
            let ref_stmt = mir::StatementKind::Assign(box (mir::Place::from(ref_arg), rvalue));

            // create the substitution since clone is generic:
            let generic_ty = ty::subst::GenericArg::from(to_process.ty);
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
                Some(to_process.stored_local.into()),
                Some(target),
            )?;
            patch.add_statement(
                mir::Location {
                    block: new_block,
                    statement_index: 0,
                },
                ref_stmt,
            );

            Ok(new_block)
            // let block_data = BasicBlockData::new()
        } else {
            // create a new local to store the result of clone:
            let deref_ty = to_process.ty.builtin_deref(false).ok_or(())?.ty;
            println!("dereferenced type: {:?}", deref_ty);
            let destination = patch.new_internal(deref_ty, DUMMY_SP);
            let generic_ty = ty::subst::GenericArg::from(deref_ty);
            let substs = self.tcx.mk_substs(&[generic_ty]);
            let clone_args = vec![Operand::Move(mir::Place::from(to_process.arg_to_store))];
            // add an additional simple block afterwards, that dereferences
            // the the cloned value into the original receiver of old:
            // create it beforehand, so we can set the precedors target correctly
            let terminator = mir::Terminator {
                source_info: dummy_source_info(),
                kind: TerminatorKind::Goto { target },
            };
            let block_data = BasicBlockData::new(Some(terminator));
            let second_block = patch.new_block(block_data);

            // deref the clone result
            let rvalue = rvalue_reference_to_local(self.tcx, destination, true);
            let ref_stmt = mir::StatementKind::Assign(box (to_process.stored_local.into(), rvalue));
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
                Some(destination.into()),
                Some(second_block),
            )?;

            Ok(new_block)
        }
    }
}

/// caller_block is calling an annotated function. `prepend_store` creates
/// a new block (new_block), moves the call to the annotated function into
/// the new block, adjusts the original block to call a store function and sets
/// its target to this new block
#[allow(clippy::too_many_arguments)]
fn prepend_store<'tcx>(
    tcx: TyCtxt<'tcx>,
    patcher: &mut MirPatch<'tcx>,
    old_store_id: DefId,
    caller_block: BasicBlock,
    args: Vec<Operand<'tcx>>,
    substs: ty::subst::SubstsRef<'tcx>,
    terminator: Terminator<'tcx>,
    old_dest_place: Place<'tcx>,
) -> BasicBlock {
    // get the bodies of the store and check function
    let new_block_data = BasicBlockData::new(Some(terminator));
    let new_block = patcher.new_block(new_block_data);

    let store_func_ty = tcx.mk_ty_from_kind(TyKind::FnDef(old_store_id, substs));
    let store_func = Operand::Constant(Box::new(Constant {
        span: DUMMY_SP,
        user_ty: None,
        literal: ConstantKind::zero_sized(store_func_ty),
    }));

    let store_terminator = TerminatorKind::Call {
        func: store_func,
        args: args.clone(),
        destination: old_dest_place,
        target: Some(new_block),
        cleanup: None,
        from_hir_call: false,
        fn_span: DUMMY_SP,
    };
    // the block that initially calls the check function, now calls the store
    // function
    patcher.patch_terminator(caller_block, store_terminator);
    new_block
}

fn create_pledge_call_chain<'tcx>(
    tcx: TyCtxt<'tcx>,
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
        tcx,
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
            tcx,
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
    let (store_block, _) = create_call_block(
        tcx,
        patcher,
        pledge.store_before_expiry,
        args,
        pledge.substs,
        Some(pledge.before_expiry_place),
        Some(next_target),
    )?;

    Ok(store_block)
}

#[allow(clippy::too_many_arguments)]
fn surround_call_with_store_and_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    check_id: DefId,
    old_store_id: DefId,
    caller_block: BasicBlock,
    target: Option<BasicBlock>,
    result_operand: Place<'tcx>,
    args: Vec<Operand<'tcx>>,
    substs: ty::subst::SubstsRef<'tcx>,
    original_terminator: Terminator<'tcx>,
) -> (BasicBlock, Option<BasicBlock>) {
    // find the type of that local
    let old_ret_ty = fn_return_ty(tcx, old_store_id);
    let old_dest_place = Place::from(patch.new_internal(old_ret_ty, DUMMY_SP));

    // construct arguments: first the arguments the function is called with, then the result of
    // that call, then the old values:
    let mut new_args = args.clone();
    new_args.push(Operand::Move(result_operand));
    new_args.push(Operand::Move(old_dest_place));

    // we store the target, create a new block per check function
    // chain these with the final call having the original target,
    // change the target of the call to the first block of our chain.
    let (check_block, _) =
        create_call_block(tcx, patch, check_id, new_args, substs, None, target).unwrap();
    let next_target = Some(check_block);

    // the terminator that calls the original function, but in this case jumps to
    // a check function after instead of original target
    let mut call_fn_terminator = original_terminator;
    replace_target(&mut call_fn_terminator, check_block);

    let new_caller_block = prepend_store(
        tcx,
        patch,
        old_store_id,
        caller_block,
        args,
        substs,
        call_fn_terminator.clone(),
        old_dest_place,
    );

    // If there are multiple checks, this also should behave
    // correctly, since on the second iteration this target
    // is already the new block

    (new_caller_block, next_target)
}
