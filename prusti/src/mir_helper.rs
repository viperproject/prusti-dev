use prusti_rustc_interface::{
    middle::{
        mir::{self, Body, TerminatorKind},
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

/// Just creates an erased region. Needed to create a borrow statement
/// in the MIR
pub fn dummy_region(tcx: TyCtxt<'_>) -> ty::Region<'_> {
    let kind = ty::RegionKind::ReErased;
    tcx.mk_region_from_kind(kind)
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
