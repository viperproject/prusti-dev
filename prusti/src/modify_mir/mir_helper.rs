use prusti_rustc_interface::{
    middle::{
        mir::{self, patch::MirPatch, visit::MutVisitor, Body, TerminatorKind},
        ty::{self, TyCtxt},
    },
    span::{self, def_id::DefId, DUMMY_SP},
};
use rustc_hash::FxHashMap;

/// Given the name of a variable in the original program, find the
/// corresponding mir local
// pub fn get_local_from_name(body: &Body<'_>, name: String) -> Option<mir::Local> {
//     for debug_info in &body.var_debug_info {
//         // find the corresponding local in the var_debug_info
//         if debug_info.name.to_string() == name {
//             if let mir::VarDebugInfoContents::Place(place) = debug_info.value {
//                 return Some(place.local);
//             }
//         }
//     }
//     None
// }

/// Check whether this variable is mutable, or a mutable reference
pub fn is_mutable_arg(body: &Body<'_>, local: mir::Local) -> bool {
    let args: Vec<mir::Local> = body.args_iter().collect();
    if args.contains(&local) {
        let local_decl = body.local_decls.get(local).unwrap();
        if local_decl.mutability == mir::Mutability::Mut {
            return true;
        }
        matches!(local_decl.ty.ref_mutability(), Some(mir::Mutability::Mut))
    } else {
        false
    }
}

// pub fn make_immutable<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
//     match *ty.kind() {
//         ty::Ref(region, inner_ty, mir::Mutability::Mut) => {
//             let new_inner_ty = make_immutable(tcx, inner_ty);
//             tcx.mk_imm_ref(region, new_inner_ty)
//         }
//         _ => ty,
//     }
// }

pub fn fn_return_ty(tcx: TyCtxt<'_>, def_id: DefId) -> ty::Ty<'_> {
    let fn_sig = tcx.fn_sig(def_id).subst_identity();
    fn_sig.output().skip_binder()
}

pub fn dummy_source_info() -> mir::SourceInfo {
    mir::SourceInfo {
        span: span::DUMMY_SP,
        scope: mir::SourceScope::from_usize(0),
    }
}

pub fn dummy_region(tcx: TyCtxt<'_>) -> ty::Region<'_> {
    let kind = ty::RegionKind::ReErased;
    tcx.mk_region_from_kind(kind)
}

pub fn unit_const(tcx: TyCtxt<'_>) -> mir::Operand<'_> {
    let unit_ty = tcx.mk_unit();
    let constant_kind = mir::ConstantKind::zero_sized(unit_ty);
    let constant = mir::Constant {
        span: DUMMY_SP,
        user_ty: None,
        literal: constant_kind,
    };
    mir::Operand::Constant(box constant)
}

pub fn rvalue_reference_to_local<'tcx>(
    tcx: TyCtxt<'tcx>,
    place: mir::Place<'tcx>,
    mutable: bool,
) -> mir::Rvalue<'tcx> {
    let dummy_region = dummy_region(tcx);
    let borrow_kind = if mutable {
        mir::BorrowKind::Mut {
            allow_two_phase_borrow: false,
        }
    } else {
        mir::BorrowKind::Shared
    };
    mir::Rvalue::Ref(
        dummy_region,
        borrow_kind,
        place, // the local to be borrowed
    )
}

pub fn create_reference_type<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
    let mutability = mir::Mutability::Not;
    let region = dummy_region(tcx);
    tcx.mk_ref(
        region,
        ty::TypeAndMut {
            ty,
            mutbl: mutability,
        },
    )
}

pub fn get_clone_defid(tcx: TyCtxt<'_>) -> Option<DefId> {
    let trait_defid = tcx.lang_items().clone_trait()?;
    tcx.associated_items(trait_defid)
        .find_by_name_and_kind(
            tcx,
            span::symbol::Ident::from_str("clone"),
            ty::AssocKind::Fn,
            trait_defid,
        )
        .map(|x| x.def_id)
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

pub fn prepend_dummy_block(body: &mut Body) -> mir::BasicBlock {
    let mut patch = MirPatch::new(body);
    let terminator_kind = mir::TerminatorKind::Goto {
        target: mir::START_BLOCK,
    };
    let terminator = mir::Terminator {
        source_info: dummy_source_info(),
        kind: terminator_kind,
    };
    let blockdata = mir::BasicBlockData::new(Some(terminator));
    let new_block_id = patch.new_block(blockdata);
    patch.apply(body);

    body.basic_blocks_mut().swap(mir::START_BLOCK, new_block_id);

    // fix all terminators to point to correct block
    for b in body.basic_blocks.as_mut().iter_mut() {
        replace_outgoing_edges(b, mir::START_BLOCK, mir::BasicBlock::MAX);
        replace_outgoing_edges(b, new_block_id, mir::START_BLOCK);
        replace_outgoing_edges(b, mir::BasicBlock::MAX, new_block_id);
    }
    new_block_id
}

pub fn create_call_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    call_id: DefId,
    args: Vec<mir::Operand<'tcx>>,
    substs: ty::subst::SubstsRef<'tcx>,
    destination: Option<mir::Place<'tcx>>,
    target: Option<mir::BasicBlock>,
) -> Result<(mir::BasicBlock, mir::Place<'tcx>), ()> {
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
        // find return type
        let ret_ty = tcx
            .fn_sig(call_id)
            .subst(tcx, substs)
            .output()
            .skip_binder();
        mir::Place::from(patch.new_temp(ret_ty, span::DUMMY_SP))
    };

    // args have to be constructed beforehand, including result or old_values
    let terminator_kind = mir::TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        cleanup: None,
        from_hir_call: false,
        fn_span: tcx.def_span(call_id),
    };
    let terminator = mir::Terminator {
        source_info: dummy_source_info(),
        kind: terminator_kind,
    };
    let blockdata = mir::BasicBlockData::new(Some(terminator));
    let new_block_id = patch.new_block(blockdata);

    Ok((new_block_id, destination))
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

pub struct ArgumentReplacer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    args_to_replace: &'a FxHashMap<mir::Local, mir::Local>,
}

impl<'a, 'tcx> ArgumentReplacer<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, args_to_replace: &'a FxHashMap<mir::Local, mir::Local>) -> Self {
        Self {
            tcx,
            args_to_replace,
        }
    }
}

impl<'tcx, 'a> MutVisitor<'tcx> for ArgumentReplacer<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_local(
        &mut self,
        local: &mut mir::Local,
        context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) {
        if let Some(replace) = self.args_to_replace.get(local) {
            assert!(!matches!(context, mir::visit::PlaceContext::NonUse(_)));
            *local = *replace;
        }
    }
}
