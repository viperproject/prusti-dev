use prusti_rustc_interface::{
    data_structures::{
        steal::Steal,
        graph::WithStartNode,
    },
    interface::DEFAULT_QUERY_PROVIDERS,
    middle::{
        mir::{visit::MutVisitor, Body, Operand, Location, Constant,
        ConstantKind, BasicBlock, BasicBlocks, BasicBlockData, Statement,
        StatementKind, Place, Terminator, TerminatorKind,
        SourceScope, SourceInfo, terminator},
        mir::interpret::{Scalar, ConstValue},
        mir::patch::MirPatch,
        ty::{self, TyCtxt, ScalarInt, TyKind},
    },
    span::{
        def_id::LocalDefId,
        DUMMY_SP,
    },
    index::vec::IndexVec,
};
use prusti_interface::specs::typed::DefSpecificationMap;

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

    let steal = ((*DEFAULT_QUERY_PROVIDERS).mir_drops_elaborated_and_const_checked)(tcx, def);
    let mut stolen = steal.steal();

    let mut visitor = InsertChecksVisitor { tcx, specs };
    visitor.visit_body(&mut stolen);

    tcx.alloc_steal_mir(stolen)
}

pub struct InsertChecksVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    specs: DefSpecificationMap,
}

impl<'tcx> MutVisitor<'tcx> for InsertChecksVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_body(&mut self, body: &mut Body<'tcx>) {
        println!("Mir body: {:#?}", body);
        let def_id = body.source.def_id();
        // try to find specification function:
        let check_id_opt = self.specs.get_checks(&def_id);
        if let Some(check_id) = check_id_opt {
            let body_to_insert: Body = self.tcx.mir_drops_elaborated_and_const_checked(
                ty::WithOptConstParam::unknown(check_id.as_local().unwrap())
            ).borrow().clone();
            println!("Found body: {:#?}", body_to_insert);

            let ret_ty = body_to_insert.return_ty().clone();
            assert!(ret_ty.is_bool());

            let mut patch = MirPatch::new(body);
            let start_node = body.basic_blocks.start_node();
            println!("Start node is {:?}", start_node);
            let target = start_node;
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
            let dest_place: Place = Place::from(patch.new_internal(ret_ty, DUMMY_SP));

            let subst = ty::List::empty();
            let func_ty = self.tcx.mk_ty_from_kind(TyKind::FnDef(check_id, subst)); // do I need substs?
            let func = Operand::Constant(Box::new(Constant {
                span: DUMMY_SP,
                user_ty: None,
                literal: ConstantKind::zero_sized(func_ty),
            }));

            // determine the arguments!
            let caller_nr_args = body.arg_count;
            let nr_args = body_to_insert.arg_count;
            let mut arg_symbols = Vec::new();

            for i in 1..nr_args + 1 {
                'inner: for el in body_to_insert.var_debug_info.clone() {
                    if format!("{:?}", el.value) == format!("_{}", i) {
                        arg_symbols.push(el.name.to_string());
                        println!("found match for {}", el.name.to_string());
                        break 'inner
                    }
                }
            }

            let mut args_symbols = Vec::new();
            // now for the caller, find ids of names:
            for s in arg_symbols {
                'inner: for el in body.var_debug_info.clone() {
                    if el.name.to_string() == s {
                        args_symbols.push(format!("{:?}", el.value));
                        break 'inner
                    }
                }
            }

            let mut args = Vec::new();
            // now the final mapping to operands:
            for s in args_symbols {
                for (local, _decl) in body.local_decls.iter_enumerated() {
                    if format!("{:?}", local) == s {
                        args.push(Operand::Copy(Place {
                            local,
                            projection: ty::List::empty(),
                        }));
                    }
                }
            }




            let terminator_kind = TerminatorKind::Call {
                func,
                args,
                destination: dest_place,
                target: Some(target),
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
            let new_block = patch.new_block(blockdata);
            println!("block index: {:?}", new_block);

            patch.apply(body);
            let old_start_data = body.basic_blocks_mut().swap(start_node, new_block);


            for b in body.basic_blocks.as_mut().iter_mut() {
                replace_outgoing_edges(b, start_node, BasicBlock::MAX);
                replace_outgoing_edges(b, new_block, start_node);
                replace_outgoing_edges(b, BasicBlock::MAX, new_block);
            }

        }

        println!("Body afterwards: {:#?}", body);
        self.super_body(body);
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


// If we re-order the IndexVec containing the basic blocks, we will need to adjust
// some the basic blocks that terminators point to. This is what this function does
fn replace_outgoing_edges(data: &mut BasicBlockData, from: BasicBlock, to: BasicBlock) {
    match &mut data.terminator_mut().kind {
        TerminatorKind::Goto { target }
        => update_if_equals(target, from, to),
        TerminatorKind::SwitchInt { targets, .. } => {
            for bb1 in &mut targets.all_targets_mut().iter_mut() {
                update_if_equals(bb1, from, to);
            }
        },
        TerminatorKind::Call { target, cleanup, .. } => {
            if let Some(target) = target {
                update_if_equals(target, from, to);
            }
            if let Some(cleanup) = cleanup {
                update_if_equals(cleanup, from, to);
            }
        },
        TerminatorKind::Assert { target: target_bb, cleanup: opt_bb, .. } |
        TerminatorKind::DropAndReplace { target: target_bb, unwind: opt_bb, .. } |
        TerminatorKind::Drop { target: target_bb, unwind: opt_bb, .. } |
        TerminatorKind::Yield { resume: target_bb, drop: opt_bb, .. } |
        TerminatorKind::FalseUnwind { real_target: target_bb, unwind: opt_bb }=> {
            update_if_equals(target_bb, from, to);
            if let Some(bb) = opt_bb {
                update_if_equals(bb, from, to);
            }

        },
        TerminatorKind::InlineAsm { destination, cleanup, .. } => {
            // is this prettier? does this even modify the blockdata?
            destination.map(|mut x| update_if_equals(&mut x, from, to));
            cleanup.map(|mut x| update_if_equals(&mut x, from, to));
        }
        TerminatorKind::FalseEdge { real_target, imaginary_target } => {
            update_if_equals(real_target, from, to);
            update_if_equals(imaginary_target, from, to);
        },
        TerminatorKind::Resume | TerminatorKind::Abort |
        TerminatorKind::Return | TerminatorKind::Unreachable |
        TerminatorKind::GeneratorDrop => {}
    }
}

fn update_if_equals<T: PartialEq>(dest: &mut T, from: T, to: T) {
    if *dest == from {
        *dest = to;
    }
}
