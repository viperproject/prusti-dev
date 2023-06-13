use prusti_rustc_interface::{
    middle::{
        mir::{self, patch::MirPatch, Body, TerminatorKind},
        ty::{self, TyCtxt},
    },
    span::{self, def_id::DefId},
};

// derive the function's type from a def_id, and an optional set of
// substitutions. If no substitutions are present,
// the identity will be used
pub fn function_operand<'tcx>(
    def_id: DefId,
    tcx: TyCtxt<'tcx>,
    substs_opt: Option<ty::subst::SubstsRef<'tcx>>,
) -> mir::Operand<'tcx> {
    let substs = substs_opt.unwrap_or(ty::subst::InternalSubsts::identity_for_item(tcx, def_id));
    let func_ty = tcx.mk_ty_from_kind(ty::TyKind::FnDef(def_id, substs));
    mir::Operand::Constant(Box::new(mir::Constant {
        span: span::DUMMY_SP,
        user_ty: None,
        literal: mir::ConstantKind::zero_sized(func_ty),
    }))
}

/// Given the name of a variable in the original program, find the
/// corresponding mir local
pub fn get_local_from_name(body: &Body<'_>, name: String) -> Option<mir::Local> {
    for debug_info in &body.var_debug_info {
        // find the corresponding local in the var_debug_info
        if debug_info.name.to_string() == name {
            if let mir::VarDebugInfoContents::Place(place) = debug_info.value {
                return Some(place.local);
            }
        }
    }
    None
}

pub fn fn_return_ty<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> ty::Ty<'tcx> {
    let fn_sig = tcx.fn_sig(def_id).subst_identity();
    fn_sig.output().skip_binder()
}

/// Just creates an erased region. Needed to create a borrow statement
/// in the MIR
pub fn dummy_region(tcx: TyCtxt<'_>) -> ty::Region<'_> {
    let kind = ty::RegionKind::ReErased;
    tcx.mk_region_from_kind(kind)
}

pub fn dummy_source_info() -> mir::SourceInfo {
    mir::SourceInfo {
        span: span::DUMMY_SP,
        scope: mir::SourceScope::from_usize(0),
    }
}

pub fn rvalue_reference_to_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    place: mir::Place<'tcx>,
) -> mir::Rvalue<'tcx> {
    let dummy_region = dummy_region(tcx);
    mir::Rvalue::Ref(
        dummy_region,
        mir::BorrowKind::Shared,
        place, // the local to be dereferenced
    )
}

pub fn args_from_body<'tcx>(body: &Body<'tcx>) -> Vec<mir::Operand<'tcx>> {

    let mut args = Vec::new();
    let caller_nr_args = body.arg_count;
    // now the final mapping to operands:
    for (local, _decl) in body.local_decls.iter_enumerated() {
        let index = local.index();
        if index != 0 && index <= caller_nr_args {
            args.push(mir::Operand::Copy(mir::Place {
                local,
                projection: ty::List::empty(),
            }));
        }
    }
    args
}

pub fn create_call_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    call_id: DefId,
    args: Vec<mir::Operand<'tcx>>,
    substs: ty::subst::SubstsRef<'tcx>,
    destination: Option<mir::Place<'tcx>>,
    target: Option<mir::BasicBlock>,
) -> Result<(mir::BasicBlock, mir::Place<'tcx>),()> {
    let body_to_insert: Body<'tcx> = tcx
        .mir_drops_elaborated_and_const_checked(ty::WithOptConstParam::unknown(
            call_id.as_local().unwrap(),
        ))
        .borrow()
        .clone();

    let ret_ty = body_to_insert.return_ty();
    // construct the function call
    let func_ty = tcx.mk_ty_from_kind(ty::TyKind::FnDef(call_id, substs));
    let func = mir::Operand::Constant(Box::new(mir::Constant {
        span: span::DUMMY_SP,
        user_ty: None,
        literal: mir::ConstantKind::zero_sized(func_ty),
    }));
    // either use passed destination or create a new one
    let destination = if let Some(dest) = destination {
        dest
    } else {
        mir::Place::from(patch.new_internal(ret_ty, span::DUMMY_SP))
    };

    // args have to be constructed beforehand, including result or old_values
    let terminator_kind = mir::TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        cleanup: None,
        from_hir_call: false,
        fn_span: body_to_insert.span,
    };
    let terminator = mir::Terminator {
        source_info: dummy_source_info(),
        kind: terminator_kind,
    };
    let blockdata = mir::BasicBlockData::new(Some(terminator));
    let new_block_id = patch.new_block(blockdata);

    Ok((new_block_id, destination))
}

/// Creates one new block, moves all instructions following the passed location
/// and the terminator to the new block, and changes the current terminator
/// to point to this new block. If successful, returns index of the new block
pub fn split_block_at_location<'tcx>(
    body: &mut mir::Body<'tcx>,
    location: mir::Location,
) -> Result<mir::BasicBlock, ()> {
    // check validity of the location:
    let mut patch = MirPatch::new(body);
    let block1: &mut mir::BasicBlockData =
        body.basic_blocks_mut().get_mut(location.block).ok_or(())?;

    let nr_instructions = block1.statements.len();
    // check if the given location is valid
    if nr_instructions <= location.statement_index {
        return Err(())
    }
    // the statements that stay in the first block
    let stmts1: Vec<mir::Statement> = block1.statements[0..=location.statement_index].to_vec();

    let stmts2: Vec<mir::Statement> = if location.statement_index + 1 < nr_instructions {
        // location is not the last instruction of the block
        block1.statements[location.statement_index + 1..].to_vec()
    } else {
        vec![]
    };

    let new_block_data = mir::BasicBlockData {
        statements: stmts2,
        terminator: block1.terminator.clone(),
        is_cleanup: block1.is_cleanup,
    };
    // add the new block:
    let block2 = patch.new_block(new_block_data);
    patch.apply(body);

    // reborrow, because of patcher
    let block1: &mut mir::BasicBlockData =
        body.basic_blocks_mut().get_mut(location.block).ok_or(())?;
    let terminator_between = mir::Terminator {
        kind: mir::TerminatorKind::Goto { target: block2 },
        source_info: dummy_source_info(),
    };
    block1.terminator = Some(terminator_between);
    block1.statements = stmts1;

    Ok(block2)
}

// If we re-order the IndexVec containing the basic blocks, we will need to adjust
// some the basic blocks that terminators point to. This is what this function does
pub fn replace_outgoing_edges(
    data: &mut mir::BasicBlockData,
    from: mir::BasicBlock,
    to: mir::BasicBlock,
) {
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

/// Given a call terminator, change it's target (the target is the basic
/// block the execution will return to, once the function is finished)
pub fn replace_target(terminator: &mut mir::Terminator, new_target: mir::BasicBlock) {
    if let mir::TerminatorKind::Call { target, .. } = &mut terminator.kind {
        *target = Some(new_target);
    }
}
