use crate::mir_helper::*;
use prusti_interface::specs::typed::DefSpecificationMap;
use prusti_rustc_interface::{
    data_structures::steal::Steal,
    interface::DEFAULT_QUERY_PROVIDERS,
    middle::{
        mir::{
            self, patch::MirPatch, visit::MutVisitor, BasicBlock, BasicBlockData, Body, Constant,
            ConstantKind, Operand, Place, SourceInfo, SourceScope, Terminator, TerminatorKind,
        },
        ty::{self, TyCtxt, TyKind},
    },
    span::{
        def_id::{DefId, LocalDefId},
        DUMMY_SP,
    },
};

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
        let steal = (DEFAULT_QUERY_PROVIDERS.mir_drops_elaborated_and_const_checked)(tcx, def);
        let mut stolen = steal.steal();

        let mut visitor = InsertChecksVisitor::new(tcx, specs);
        visitor.visit_body(&mut stolen);
        println!("Custom modifications are done! Compiler back at work");

        tcx.alloc_steal_mir(stolen)
    } else {
        println!("the specs could not be collected");
        (DEFAULT_QUERY_PROVIDERS.mir_drops_elaborated_and_const_checked)(tcx, def)
    }
}

pub struct InsertChecksVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    specs: DefSpecificationMap,
    current_patcher: Option<MirPatch<'tcx>>,
}

impl<'tcx> InsertChecksVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, specs: DefSpecificationMap) -> Self {
        Self {
            tcx,
            specs,
            current_patcher: None,
        }
    }
}

impl<'tcx> MutVisitor<'tcx> for InsertChecksVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_body(&mut self, body: &mut Body<'tcx>) {
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

        self.current_patcher = Some(MirPatch::new(body));
        self.super_body(body);
        let mir_patch = self.current_patcher.take();
        mir_patch.unwrap().apply(body);
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
                target,
                destination,
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
                    for (check_id, old_store_id) in self.specs.get_post_checks(&call_id) {
                        println!("Now inserting a runtime check for a postcondition");
                        println!("Old store defid: {:?}", old_store_id);
                        // since here, we don't have mutable access to the body,
                        // we created a patcher beforehand which we can use here
                        // and apply later
                        let mut patch = self.current_patcher.take().unwrap();

                        // get the bodies of the store and check function
                        let old_store_body = self
                            .tcx
                            .mir_drops_elaborated_and_const_checked(ty::WithOptConstParam::unknown(
                                old_store_id.as_local().unwrap(),
                            ))
                            .borrow();
                        let check_body = self
                            .tcx
                            .mir_drops_elaborated_and_const_checked(ty::WithOptConstParam::unknown(
                                check_id.as_local().unwrap(),
                            ))
                            .borrow();

                        // get the local index of the old_values argument to the
                        // check function (where it's already a reference to this
                        // tuple)
                        let old_values_check_arg =
                            get_local_from_name(&check_body, "old_values".to_string()).unwrap();
                        // find the type of that local
                        let old_value_arg_ty =
                            check_body.local_decls.get(old_values_check_arg).unwrap().ty;

                        println!("found old_values arg type: {:?}", old_value_arg_ty);

                        // create a new internal to store result of old_store function
                        let old_ret_ty = old_store_body.return_ty();
                        println!(
                            "expecting return type {:?} for old_store function",
                            old_ret_ty
                        );
                        let old_dest_place = Place::from(patch.new_internal(old_ret_ty, DUMMY_SP));
                        let old_arg_deref_place =
                            Place::from(patch.new_internal(old_value_arg_ty, DUMMY_SP));

                        // dereference the old_values type
                        let rvalue = rvalue_reference_to_place(self.tcx, old_dest_place);

                        // we store the target, create a new block per check function
                        // chain these with the final call having the original target,
                        // change the target of the call to the first block of our chain.
                        let (block, _) = new_call_block(
                            self.tcx,
                            &mut patch,
                            check_id,
                            &called_body,
                            current_target,
                            Some(*destination), // destination is now result arg
                            Some(old_arg_deref_place),
                            Some(args.clone()),
                            substs,
                        );
                        // make deref the first statement in this block
                        let insert_deref_location = mir::Location {
                            block,
                            statement_index: 0,
                        };
                        patch.add_assign(insert_deref_location, old_arg_deref_place, rvalue);
                        current_target = Some(block);

                        let mut call_fn_terminator = original_terminator.clone();
                        replace_target(&mut call_fn_terminator, block);
                        let new_block_data = BasicBlockData::new(Some(call_fn_terminator));
                        let new_block = patch.new_block(new_block_data);

                        // let generics = self.tcx.generics_of(def_id);
                        let store_func_ty = self
                            .tcx
                            .mk_ty_from_kind(TyKind::FnDef(old_store_id, substs));
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
                        caller_block = new_block;

                        // If there are multiple checks, this also should behave
                        // correctly, since on the second iteration this target
                        // is already the new block
                        self.current_patcher = Some(patch);
                    }
                }
            }
        }
    }
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
