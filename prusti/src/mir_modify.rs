use prusti_interface::specs::typed::DefSpecificationMap;
use prusti_rustc_interface::{
    data_structures::steal::Steal,
    interface::DEFAULT_QUERY_PROVIDERS,
    middle::{
        mir::{
            patch::MirPatch,
            visit::MutVisitor,
            BasicBlock, BasicBlockData, Body, Constant, ConstantKind,
            Operand, Place, SourceInfo, SourceScope, Terminator,
            TerminatorKind,
        },
        ty::{self, Ty, TyCtxt, TyKind},
    },
    span::{
        def_id::{DefId, LocalDefId},
        DUMMY_SP,
    },
};
use std::collections::HashMap;

pub static mut SPECS: Option<DefSpecificationMap> = None;

pub(crate) fn mir_checked(
    tcx: TyCtxt<'_>,
    def: ty::WithOptConstParam<LocalDefId>,
) -> &Steal<Body<'_>> {
    // is it our job to store it?
    println!("mir checked query is called");

    // let's get the specifications collected by prusti :)

    // SAFETY: Is definitely not safe at the moment
    let specs = unsafe { SPECS.clone().unwrap() };

    let steal = (DEFAULT_QUERY_PROVIDERS.mir_drops_elaborated_and_const_checked)(tcx, def);
    let mut stolen = steal.steal();

    let mut visitor = InsertChecksVisitor::new(tcx, specs);
    visitor.visit_body(&mut stolen);
    println!("Custom modifications are done! Compiler back at work");

    tcx.alloc_steal_mir(stolen)
}

pub struct InsertChecksVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    specs: DefSpecificationMap,
    post_check_types: HashMap<Ty<'tcx>, (DefId, Vec<(DefId, DefId)>)>,
    current_patcher: Option<MirPatch<'tcx>>,
}

impl<'tcx> InsertChecksVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, specs: DefSpecificationMap) -> Self {
        // when traversing the MIR and looking for function calls,
        // it appears to be difficult to get the DefId of a Call.
        // A `Ty` representing it does exist however.
        // That's why we transform the specification map in the following way
        let mut post_check_types = HashMap::new();
        // specs.checks contains all the ids of functions that are annotated with
        // some check_id
        for (id, _) in specs.checks.iter() {
            let checks = specs.get_post_checks(id);
            let subst = ty::List::empty();
            let func_ty = tcx.mk_ty_from_kind(TyKind::FnDef(*id, subst)); // do I need substs?
            post_check_types.insert(func_ty, (*id, checks.clone()));
        }

        Self {
            tcx,
            specs,
            post_check_types,
            current_patcher: None,
        }
    }
}

impl<'tcx> MutVisitor<'tcx> for InsertChecksVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_body(&mut self, body: &mut Body<'tcx>) {
        let def_id = body.source.def_id();
        // try to find specification function:
        let pre_check_ids = self.specs.get_pre_checks(&def_id);
        // todo: properly deal with multiple of them
        // does this already work? We just prepend new checks, so it should..
        for check_id in pre_check_ids {
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
            let mut original_block = block;
            let original_terminator = data.terminator.clone().unwrap().clone();
            if let TerminatorKind::Call {
                func:
                    Operand::Constant(box Constant {
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
                let mut current_target = *target;
                // lookup if there is a check function:
                if let Some((call_id, id_vec)) = self.post_check_types.get(ty) {
                    let called_body: Body = self
                        .tcx
                        .mir_drops_elaborated_and_const_checked(ty::WithOptConstParam::unknown(
                                call_id.as_local().unwrap(),
                                ))
                        .borrow()
                        .clone();
                    println!("inserting checks for {} specification items", id_vec.len());
                    // since there might be multiple blocks to be inserted,
                    for (check_id, old_store_id) in id_vec {
                        println!("Now inserting a runtime check for a postcondition");
                        println!("Old store defid: {:?}", old_store_id);
                        let mut patch = self.current_patcher.take().unwrap();

                        let old_store_body = self
                            .tcx
                            .mir_drops_elaborated_and_const_checked(ty::WithOptConstParam::unknown(
                                old_store_id.as_local().unwrap(),
                            ))
                            .borrow();

                        // create a new internal to store result of old_store function
                        let old_ret_ty = old_store_body.return_ty();
                        println!("expecting return type {:?} for old_store function", old_ret_ty);
                        let old_dest_place = Place::from(patch.new_internal(old_ret_ty, DUMMY_SP));
                        // we store the target, create a new block per check function
                        // chain these with the final call having the original target,
                        // change the target of the call to the first block of our chain.
                        let (block, _) = new_call_block(
                            self.tcx,
                            &mut patch,
                            *check_id,
                            &called_body,
                            current_target,
                            Some(*destination), // destination is now result arg
                            Some(old_dest_place),
                            Some(args.clone()),
                        );
                        current_target = Some(block);

                        let mut call_fn_terminator = original_terminator.clone();
                        replace_target(&mut call_fn_terminator, block);
                        let new_block_data = BasicBlockData::new(Some(call_fn_terminator));
                        let new_block = patch.new_block(new_block_data);

                        let subst = ty::List::empty(); // potentially bad?
                        let store_func_ty = self.tcx.mk_ty_from_kind(TyKind::FnDef(*old_store_id, subst));
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
                        patch.patch_terminator(original_block, store_terminator);
                        original_block = new_block;

                        // If there are multiple checks, this also should behave
                        // correctly, since on the second iteration this target
                        // is already the new block
                        self.current_patcher = Some(patch);
                    }
                }
            }
        }
    }

    // This was just a test to see if changes influence the generted executable
    // fn visit_operand(&mut self, operand: &mut Operand<'tcx>, location: Location) {
    //     match operand {
    //         Operand::Constant(box c) => {
    //             if let Constant{ literal, .. } = c {
    //                 if let ConstantKind::Val(value, ty) = literal {
    //                     if ty.is_bool() {
    //                         println!("found a boolean constant!");
    //                         *value = ConstValue::Scalar(Scalar::Int(ScalarInt::FALSE))
    //                     }
    //                 }
    //             }
    //         },
    //         _ => {}
    //     }
    //     self.super_operand(operand, location);
    // }
}

fn replace_target(terminator: &mut Terminator, new_target: BasicBlock) {
    if let TerminatorKind::Call {
        target,
        ..
    } = &mut terminator.kind {
        *target = Some(new_target);
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
    // let mut loc = Location {
    //     block: start_node,
    //     statement_index: 0,
    // };
    // while let Some(stmt) = body.stmt_at(loc).left() {
    //     if let Statement { kind: StatementKind::StorageLive(_x), .. } = stmt {
    //         println!("good :)");
    //         loc.statement_index += 1;
    //     } else {
    //         break;
    //     }
    // }

    // variable to store result of function (altough we dont care about the result)
    let dest_place: Place = Place::from(patch.new_internal(ret_ty, DUMMY_SP));

    let subst = ty::List::empty(); // potentially bad?
    let func_ty = tcx.mk_ty_from_kind(TyKind::FnDef(terminator_call, subst)); // do I need substs?
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
        // Todo: deal with result!
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

// If we re-order the IndexVec containing the basic blocks, we will need to adjust
// some the basic blocks that terminators point to. This is what this function does
fn replace_outgoing_edges(data: &mut BasicBlockData, from: BasicBlock, to: BasicBlock) {
    match &mut data.terminator_mut().kind {
        TerminatorKind::Goto { target } => update_if_equals(target, from, to),
        TerminatorKind::SwitchInt { targets, .. } => {
            for bb1 in &mut targets.all_targets_mut().iter_mut() {
                update_if_equals(bb1, from, to);
            }
        }
        TerminatorKind::Call {
            target, cleanup, ..
        } => {
            if let Some(target) = target {
                update_if_equals(target, from, to);
            }
            if let Some(cleanup) = cleanup {
                update_if_equals(cleanup, from, to);
            }
        }
        TerminatorKind::Assert {
            target: target_bb,
            cleanup: opt_bb,
            ..
        }
        | TerminatorKind::DropAndReplace {
            target: target_bb,
            unwind: opt_bb,
            ..
        }
        | TerminatorKind::Drop {
            target: target_bb,
            unwind: opt_bb,
            ..
        }
        | TerminatorKind::Yield {
            resume: target_bb,
            drop: opt_bb,
            ..
        }
        | TerminatorKind::FalseUnwind {
            real_target: target_bb,
            unwind: opt_bb,
        } => {
            update_if_equals(target_bb, from, to);
            if let Some(bb) = opt_bb {
                update_if_equals(bb, from, to);
            }
        }
        TerminatorKind::InlineAsm {
            destination,
            cleanup,
            ..
        } => {
            // is this prettier? does this even modify the blockdata?
            destination.map(|mut x| update_if_equals(&mut x, from, to));
            cleanup.map(|mut x| update_if_equals(&mut x, from, to));
        }
        TerminatorKind::FalseEdge {
            real_target,
            imaginary_target,
        } => {
            update_if_equals(real_target, from, to);
            update_if_equals(imaginary_target, from, to);
        }
        TerminatorKind::Resume
        | TerminatorKind::Abort
        | TerminatorKind::Return
        | TerminatorKind::Unreachable
        | TerminatorKind::GeneratorDrop => {}
    }
}

fn update_if_equals<T: PartialEq>(dest: &mut T, from: T, to: T) {
    if *dest == from {
        *dest = to;
    }
}
