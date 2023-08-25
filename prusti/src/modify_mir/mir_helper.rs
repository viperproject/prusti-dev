use prusti_rustc_interface::{
    index::IndexVec,
    middle::{
        mir::{self, patch::MirPatch, visit::MutVisitor, Body, TerminatorKind},
        ty::{self, TyCtxt},
    },
    span::{self, def_id::DefId, DUMMY_SP},
};
use rustc_hash::FxHashMap;

// A set of functions that are often used during mir modifications

/// Check whether this variable is mutable, or a mutable reference
pub fn is_mutable_arg(
    body: &Body<'_>,
    local: mir::Local,
    local_decls: &IndexVec<mir::Local, mir::LocalDecl<'_>>,
) -> bool {
    let args: Vec<mir::Local> = body.args_iter().collect();
    if args.contains(&local) {
        let local_decl = local_decls.get(local).unwrap();
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

pub fn fn_return_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    generics_opt: Option<ty::GenericArgsRef<'tcx>>,
) -> ty::Ty<'tcx> {
    let fn_sig = if let Some(generics) = generics_opt {
        tcx.fn_sig(def_id).instantiate(tcx, generics)
    } else {
        tcx.fn_sig(def_id).instantiate_identity()
    };
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
    ty::Region::new_from_kind(tcx, kind)
}

pub fn unit_const(tcx: TyCtxt<'_>) -> mir::Operand<'_> {
    let unit_ty = ty::Ty::new_unit(tcx);
    let constant_kind = mir::ConstantKind::zero_sized(unit_ty);
    let constant = mir::Constant {
        span: DUMMY_SP,
        user_ty: None,
        literal: constant_kind,
    };
    mir::Operand::Constant(Box::new(constant))
}

pub fn rvalue_reference_to_local<'tcx>(
    tcx: TyCtxt<'tcx>,
    place: mir::Place<'tcx>,
    mutable: bool,
) -> mir::Rvalue<'tcx> {
    let dummy_region = dummy_region(tcx);
    let borrow_kind = if mutable {
        mir::BorrowKind::Mut {
            kind: mir::MutBorrowKind::Default,
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
    ty::Ty::new_ref(
        tcx,
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
    for local in body.args_iter() {
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
        TerminatorKind::Call { target, unwind, .. } => {
            if let Some(target) = target {
                update_if_equals(target, from, to);
            }
            if let mir::UnwindAction::Cleanup(cleanup) = unwind {
                update_if_equals(cleanup, from, to);
            }
        }
        TerminatorKind::Assert { target, unwind, .. }
        | TerminatorKind::Drop { target, unwind, .. }
        | TerminatorKind::FalseUnwind {
            real_target: target,
            unwind,
        } => {
            update_if_equals(target, from, to);
            if let mir::UnwindAction::Cleanup(bb) = unwind {
                update_if_equals(bb, from, to);
            }
        }
        TerminatorKind::InlineAsm {
            destination,
            unwind,
            ..
        } => {
            // is this prettier? does this even modify the blockdata?
            if let Some(bb) = destination {
                update_if_equals(bb, from, to);
            }
            if let mir::UnwindAction::Cleanup(bb) = unwind {
                update_if_equals(bb, from, to)
            }
        }
        TerminatorKind::FalseEdge {
            real_target,
            imaginary_target,
        } => {
            update_if_equals(real_target, from, to);
            update_if_equals(imaginary_target, from, to);
        }
        TerminatorKind::Yield { resume, drop, .. } => {
            update_if_equals(resume, from, to);
            if let Some(bb) = drop {
                update_if_equals(bb, from, to);
            }
        }
        TerminatorKind::Resume
        | TerminatorKind::Terminate
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

// If this block is a goto block, and if it is returns its current target
pub fn get_block_target(body: &Body<'_>, block: mir::BasicBlock) -> Option<mir::BasicBlock> {
    let terminator: &Option<mir::Terminator> = &body.basic_blocks.get(block)?.terminator;
    if let Some(mir::Terminator {
        kind: mir::TerminatorKind::Goto { target },
        ..
    }) = terminator
    {
        Some(*target)
    } else {
        None
    }
}

pub fn get_successors(body: &Body<'_>, location: mir::Location) -> Vec<mir::Location> {
    let statements_len = body[location.block].statements.len();
    if location.statement_index < statements_len {
        vec![mir::Location {
            statement_index: location.statement_index + 1,
            ..location
        }]
    } else {
        body[location.block]
            .terminator
            .as_ref()
            .unwrap()
            .successors()
            .map(|block| mir::Location {
                block,
                statement_index: 0,
            })
            .collect()
    }
}
