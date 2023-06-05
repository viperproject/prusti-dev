use crate::mir_helper::*;
use prusti_interface::{
    environment::{Environment, Procedure},
    specs::typed::{CheckKind, DefSpecificationMap},
};
use prusti_rustc_interface::{
    data_structures::steal::Steal,
    interface::DEFAULT_QUERY_PROVIDERS,
    middle::{
        mir::{
            self, patch::MirPatch, pretty, visit::MutVisitor, BasicBlock, BasicBlockData, Body,
            Constant, ConstantKind, Operand, Place, SourceInfo, SourceScope, Terminator,
            TerminatorKind,
        },
        ty::{self, TyCtxt, TyKind},
    },
    span::{
        def_id::{DefId, LocalDefId},
        DUMMY_SP,
    },
};
use prusti_viper::encoder::Encoder;

// debugging dependencies?
use std::{env, fs, io};

fn folder_present(name: &str) -> io::Result<bool> {
    let mut path = env::current_dir()?;
    path.push(name);
    let metadata = fs::metadata(path)?;
    Ok(metadata.is_dir())
}

pub static mut SPECS: Option<DefSpecificationMap> = None;

pub(crate) fn mir_checked(
    tcx: TyCtxt<'_>,
    def: ty::WithOptConstParam<LocalDefId>,
) -> &Steal<Body<'_>> {
    // is it our job to store it?
    println!("mir checked query is called");

    // let's get the specifications collected by prusti :)

    // SAFETY: Is definitely not safe at the moment
    let specs_opt = unsafe { SPECS.clone() };

    if let Some(specs) = specs_opt {
        // let def_id = def.def_id_for_type_of();
        // let env = Environment::new(tcx, env!("CARGO_PKG_VERSION"));
        // let encoder = Encoder::new(&env, specs.clone());
        // let procedure = Procedure::new(&env, def_id);
        let steal = (DEFAULT_QUERY_PROVIDERS.mir_drops_elaborated_and_const_checked)(tcx, def);
        let mut stolen = steal.steal();

        let mut visitor = InsertChecksVisitor::new(tcx, specs);
        visitor.visit_body(&mut stolen);
        println!("Custom modifications are done! Compiler back at work");

        // print mir of body:
        if let Ok(true) = folder_present("dump") {
            let def_id = stolen.source.def_id();
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

#[derive(Debug, Copy, Clone)]
pub struct PledgeToProcess<'tcx> {
    check: DefId,
    store_before_expiry: DefId,
    check_before_expiry: Option<DefId>,
    old_values_place: Place<'tcx>,
    before_expiry_place: Place<'tcx>,
}

pub struct InsertChecksVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    specs: DefSpecificationMap,
    current_patcher: Option<MirPatch<'tcx>>,
    pledges_to_process: Vec<PledgeToProcess<'tcx>>,
}

impl<'tcx> InsertChecksVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, specs: DefSpecificationMap) -> Self {
        Self {
            tcx,
            specs,
            current_patcher: None,
            pledges_to_process: Vec::new(),
        }
    }
}

impl<'tcx> MutVisitor<'tcx> for InsertChecksVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_body(&mut self, body: &mut Body<'tcx>) {
        // visit body, apply patches, possibly find pledges that need to be processed here:
        self.current_patcher = Some(MirPatch::new(body));
        self.super_body(body);
        let mir_patch = self.current_patcher.take();
        mir_patch.unwrap().apply(body);

        for pledge_to_process in &self.pledges_to_process {
            println!("found a pledge {:#?}, currently not processing it", pledge_to_process);
        }

        // do we have to make sure this is the body the query was called on?
        let def_id = body.source.def_id();
        // try to find specification function:
        let substs = ty::subst::InternalSubsts::identity_for_item(self.tcx, def_id);
        for check_id in self.specs.get_pre_checks(&def_id) {
            let mut patch = MirPatch::new(body);
            let start_node = BasicBlock::from_usize(0);
            let (new_block, _) = new_call_block(
                self.tcx,
                &mut patch,
                check_id,
                body,
                Some(start_node),
                None,
                None,
                None,
                substs,
            );
            patch.apply(body);
            // swap first and last node, so our new block is called on entry
            body.basic_blocks_mut().swap(start_node, new_block);

            // fix all terminators to point to correct block
            for b in body.basic_blocks.as_mut().iter_mut() {
                replace_outgoing_edges(b, start_node, BasicBlock::MAX);
                replace_outgoing_edges(b, new_block, start_node);
                replace_outgoing_edges(b, BasicBlock::MAX, new_block);
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
            let original_terminator = data.terminator.clone().unwrap().clone();

            if let TerminatorKind::Call {
                func:
                    func @ Operand::Constant(box Constant {
                        literal: ConstantKind::Val(_, ty),
                        ..
                    }),
                target,      // the block called afterwards
                destination, // local to receive result
                args,
                ..
            } = terminator_kind
            {
                println!("Call terminator: {:?}", ty);
                // if it's a static function call, we start looking if there are
                // post-conditions we could check
                if let Some((call_id, substs)) = func.const_fn_def() {
                    println!("we are dealing with call_id {:?}", call_id);
                    // make sure the call is local:
                    if !call_id.is_local() {
                        // not sure yet here, to get the body the method
                        // has to be local. The way we construct things
                        // we currently need it. For extern_specs this will
                        // be a problem.
                        return;
                    }

                    // The block that is executed after the annotated function
                    // is called. Mutable because after appending the first
                    // check function call, this is the new target
                    let mut current_target = *target;
                    // lookup if there is a check function:
                    let called_body: Body = self
                        .tcx
                        .mir_drops_elaborated_and_const_checked(ty::WithOptConstParam::unknown(
                            call_id.as_local().unwrap(),
                        ))
                        .borrow()
                        .clone();
                    // since there might be multiple blocks to be inserted,
                    for check_kind in self.specs.get_runtime_checks(&call_id) {
                        match check_kind {
                            CheckKind::Post {
                                check: check_id,
                                old_store: old_store_id,
                            } => {
                                println!("Now inserting a runtime check for a postcondition");
                                println!("Old store defid: {:?}", old_store_id);
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
                                    &called_body,
                                    original_terminator.clone(),
                                );
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
                                let before_expiry_ty =
                                    fn_return_ty(self.tcx, store_before_expiry);
                                let before_expiry_place =
                                    Place::from(patch.new_internal(before_expiry_ty, DUMMY_SP));

                                prepend_store(
                                    self.tcx,
                                    &mut patch,
                                    old_store,
                                    caller_block,
                                    args.clone(),
                                    substs,
                                    original_terminator.clone(),
                                    old_values_place,
                                );

                                // *destination is the loan!
                                // figure out where is expires!
                                let pledge_to_process = PledgeToProcess {
                                    check,
                                    check_before_expiry,
                                    store_before_expiry,
                                    old_values_place,
                                    before_expiry_place,
                                };
                                self.pledges_to_process.push(pledge_to_process);

                                // Insert the 3 functions (all but old_store)
                                // where the reference goes out of scope
                                // this can probably not be done here!
                                // Goal: Given a location, split that block into
                                // two, insert before_expiry_store and before_expiry_check,
                                // and then the check function
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

/// Block current_caller is calling an annotated function. This function creates
/// a new block (new_block), moves this call into that block, adjusts the original
/// block to call a store function and sets its target to this new block
fn prepend_store<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    old_store_id: DefId,
    caller_block: BasicBlock,
    args: Vec<Operand<'tcx>>,
    substs: ty::subst::SubstsRef<'tcx>,
    terminator: Terminator<'tcx>,
    old_dest_place: Place<'tcx>,
) -> BasicBlock {
    // get the bodies of the store and check function
    let old_store_body = tcx
        .mir_drops_elaborated_and_const_checked(ty::WithOptConstParam::unknown(
            old_store_id.as_local().unwrap(),
        ))
        .borrow();
    let new_block_data = BasicBlockData::new(Some(terminator));
    let new_block = patch.new_block(new_block_data);

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
        fn_span: old_store_body.span,
    };
    patch.patch_terminator(caller_block, store_terminator);
    new_block
}

fn surround_call_with_store_and_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    check_id: DefId,
    old_store_id: DefId,
    caller_block: BasicBlock,
    target: Option<BasicBlock>,
    call_destination: Place<'tcx>,
    args: Vec<Operand<'tcx>>,
    substs: ty::subst::SubstsRef<'tcx>,
    called_body: &Body,
    original_terminator: Terminator<'tcx>,
) -> (BasicBlock, Option<BasicBlock>) {
    println!("Now inserting a runtime check for a postcondition");
    println!("Old store defid: {:?}", old_store_id);

    let check_body = tcx
        .mir_drops_elaborated_and_const_checked(ty::WithOptConstParam::unknown(
            check_id.as_local().unwrap(),
        ))
        .borrow();

    // get the local index of the old_values argument to the
    // check function (where it's already a reference to this
    // tuple)
    let old_values_check_arg = get_local_from_name(&check_body, "old_values".to_string()).unwrap();
    // find the type of that local
    let old_value_arg_ty = check_body.local_decls.get(old_values_check_arg).unwrap().ty;
    let old_ret_ty = fn_return_ty(tcx, old_store_id);
    let old_dest_place = Place::from(patch.new_internal(old_ret_ty, DUMMY_SP));

    println!("found old_values arg type: {:?}", old_value_arg_ty);

    // we store the target, create a new block per check function
    // chain these with the final call having the original target,
    // change the target of the call to the first block of our chain.
    let (block, _) = new_call_block(
        tcx,
        patch,
        check_id,
        called_body,
        target,
        Some(call_destination), // destination is now result arg
        Some(old_dest_place),
        Some(args.clone()),
        substs,
    );
    // make deref the first statement in this block
    // let insert_deref_location = mir::Location {
    //     block,
    //     statement_index: 0,
    // };
    // patch.add_assign(insert_deref_location, old_arg_deref_place, rvalue);
    let next_target = Some(block);

    // the terminator that calls the original function, but in this case jumps to
    // a check function after instead of original target
    let mut call_fn_terminator = original_terminator;
    replace_target(&mut call_fn_terminator, block);

    let new_caller_block = prepend_store(
        tcx,
        patch,
        old_store_id,
        caller_block,
        args,
        substs,
        call_fn_terminator,
        old_dest_place,
    );

    // let generics = self.tcx.generics_of(def_id);

    // If there are multiple checks, this also should behave
    // correctly, since on the second iteration this target
    // is already the new block

    (new_caller_block, next_target)
}

fn new_call_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    terminator_call: DefId,
    attached_to_body: &Body,
    target: Option<BasicBlock>,
    result: Option<Place<'tcx>>,
    old_value: Option<Place<'tcx>>,
    args_opt: Option<Vec<Operand<'tcx>>>,
    substs: ty::subst::SubstsRef<'tcx>,
) -> (BasicBlock, Place<'tcx>) {
    let body_to_insert: Body = tcx
        .mir_drops_elaborated_and_const_checked(ty::WithOptConstParam::unknown(
            terminator_call.as_local().unwrap(),
        ))
        .borrow()
        .clone();

    let ret_ty = body_to_insert.return_ty();
    // assert!(ret_ty.is_bool() || ret_ty.is_unit());
    // for store functions it can absolutely have a return type
    // should always be block 0 but let's be certain..
    println!("Target node is {:?}", target);

    // variable to store result of function (altough we dont care about the result)
    let dest_place: Place = Place::from(patch.new_internal(ret_ty, DUMMY_SP));

    // find the substs that were used for the original call
    let func_ty = tcx.mk_ty_from_kind(TyKind::FnDef(terminator_call, substs)); // do I need substs?
    println!("Function type: {:?}", func_ty);
    let func = Operand::Constant(Box::new(Constant {
        span: DUMMY_SP,
        user_ty: None,
        literal: ConstantKind::zero_sized(func_ty),
    }));

    let mut args = Vec::new();
    if let Some(arguments) = args_opt {
        args = arguments;
    } else {
        // determine the arguments!
        // and make it less ugly.. But not sure how this is supposed to be done
        let caller_nr_args = attached_to_body.arg_count;
        // now the final mapping to operands:
        for (local, _decl) in attached_to_body.local_decls.iter_enumerated() {
            let index = local.index();
            if index != 0 && index <= caller_nr_args {
                args.push(Operand::Copy(Place {
                    local,
                    projection: ty::List::empty(),
                }));
            }
        }
    }
    if let Some(result_operand) = result {
        println!("Adding the result operand!");
        args.push(Operand::Move(result_operand));
    }
    if let Some(old_value_operand) = old_value {
        println!("Adding the old_value operand");
        args.push(Operand::Move(old_value_operand));
    }

    let terminator_kind = TerminatorKind::Call {
        func,
        args,
        destination: dest_place,
        target,
        cleanup: None,
        from_hir_call: false,
        fn_span: body_to_insert.span,
    };
    let terminator = Terminator {
        // todo: replace this with the span of the original contract?
        source_info: SourceInfo {
            span: DUMMY_SP,
            scope: SourceScope::from_usize(0),
        },
        kind: terminator_kind,
    };
    let blockdata = BasicBlockData::new(Some(terminator));
    (patch.new_block(blockdata), dest_place)
}
