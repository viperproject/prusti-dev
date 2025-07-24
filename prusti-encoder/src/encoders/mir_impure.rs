use std::alloc::Global;

use pcg::{
    action::{BorrowPcgAction, PcgAction, PcgActions},
    borrow_pcg::{
        action::BorrowPcgActionKind,
        borrow_pcg_edge::BorrowPcgEdge,
        borrow_pcg_expansion::BorrowPcgExpansion,
        edge::{abstraction::AbstractionType, kind::BorrowPcgEdgeKind},
        state::BorrowsState,
        unblock_graph::BorrowPcgUnblockAction,
    },
    free_pcs::{CapabilityKind, PcgBasicBlock, RepackOp},
    pcg::{EvalStmtPhase, PCGNode, Pcg, PcgSuccessor},
    r#loop::LoopAnalysis,
    utils::{maybe_old::MaybeOldPlace, CompilerCtxt, HasPlace, Place},
    PcgOutput,
};
use prusti_interface::{specs::specifications::SpecQuery, PrustiError};
use prusti_rustc_interface::{
    data_structures::fx::FxHashMap,
    middle::{
        mir,
        ty::{self, GenericArgs, TyKind},
    },
    span::def_id::DefId,
    target::abi,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, CompType};

use crate::{
    encoder_traits::{
        impure_function_enc::{ImpureFunctionEncOutput, ImpureFunctionEncOutputRef},
        pure_func_app_enc::PureFuncAppEnc,
    },
    encoders::{
        self,
        lifted::{
            aggregate_cast::{AggregateSnapArgsCastEnc, AggregateSnapArgsCastEncTask},
            casters::CastTypePure,
            func_app_ty_params::LiftedFuncAppTyParamsEnc,
        },
        FunctionCallTaskDescription, MirBuiltinEnc, WandEnc, WandEncTask,
    },
};

use super::{
    lifted::{
        cast::{CastArgs, CastToEnc},
        casters::CastTypeImpure,
        rust_ty_cast::RustTyCastersEnc,
        ty::{EncodeGenericsAsLifted, LiftedTyEnc},
    },
    rust_ty_predicates::{RustTyPredicatesEnc, RustTyPredicatesEncOutputRef},
    ConstEnc, MirMonoImpureEnc, MirPolyImpureEnc, WandEncOutput,
};

pub struct MirImpureEnc;

#[derive(Clone, Debug)]
pub enum MirImpureEncError {
    // Unsupported,
}

const ENCODE_REACH_BB: bool = false;

impl MirImpureEnc {
    pub fn monomorphize() -> bool {
        cfg!(feature = "mono_function_encoding")
    }
}

impl TaskEncoder for MirImpureEnc {
    task_encoder::encoder_cache!(MirImpureEnc);

    type TaskDescription<'vir> = FunctionCallTaskDescription<'vir>;

    type OutputRef<'vir> = ImpureFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ImpureFunctionEncOutput<'vir>;

    type EncodingError = MirImpureEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let monomorphize = Self::monomorphize();
        let output_ref = if monomorphize {
            deps.require_ref::<MirMonoImpureEnc>(*task_key)?
        } else {
            deps.require_ref::<MirPolyImpureEnc>(task_key.def_id)?
        };
        deps.emit_output_ref(*task_key, output_ref)?;
        let output: ImpureFunctionEncOutput<'_> = if monomorphize {
            deps.require_local::<MirMonoImpureEnc>(*task_key)?
        } else {
            deps.require_local::<MirPolyImpureEnc>(task_key.def_id)?
        };
        Ok((output, ()))
    }
}

pub struct ImpureEncVisitor<'vir, 'enc, E: TaskEncoder>
where
    'vir: 'enc,
{
    pub vcx: &'vir vir::VirCtxt<'vir>,
    // Are we monomorphizing functions?
    pub monomorphize: bool,
    pub deps: &'enc mut TaskEncoderDependencies<'vir, E>,
    pub def_id: DefId,
    pub local_decls: &'enc mir::LocalDecls<'vir>,
    pub fpcs_analysis: PcgOutput<'enc, 'vir, Global>,
    pub local_defs: crate::encoders::MirLocalDefEncOutput<'vir>,
    pub body: &'enc mir::Body<'vir>,

    pub loop_analysis: LoopAnalysis,
    pub wands: WandEncOutput<'vir>,

    pub tmp_ctr: usize,
    pub label_ctr: usize,
    pub call_labels: FxHashMap<mir::BasicBlock, (&'vir str, &'vir str)>,
    pub from_to_vars: FxHashMap<mir::BasicBlock, Vec<(mir::BasicBlock, &'vir str)>>,

    // for the current basic block
    pub current_fpcs: Option<PcgBasicBlock<'vir>>,

    pub current_block_label: Option<vir::CfgBlockLabel<'vir>>,
    pub current_stmts: Option<Vec<vir::Stmt<'vir>>>,
    pub current_terminator: Option<vir::TerminatorStmt<'vir>>,

    pub encoded_blocks: Vec<vir::CfgBlock<'vir>>, // TODO: use IndexVec ?
}

impl<'vir, E: TaskEncoder> PureFuncAppEnc<'vir, E> for ImpureEncVisitor<'vir, '_, E> {
    type EncodeOperandArgs = ();
    type Curr = ();
    type Next = !;
    type LocalDeclsSrc = mir::LocalDecls<'vir>;
    fn vcx(&self) -> &'vir vir::VirCtxt<'vir> {
        self.vcx
    }

    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir, E> {
        self.deps
    }

    fn local_decls_src(&self) -> &Self::LocalDeclsSrc {
        self.local_decls
    }

    fn encode_operand(
        &mut self,
        _args: &Self::EncodeOperandArgs,
        operand: &mir::Operand<'vir>,
    ) -> vir::ExprGenSnap<'vir, Self::Curr, Self::Next> {
        self.encode_operand_snap(operand)
    }

    fn monomorphize(&self) -> bool {
        self.monomorphize
    }
}

pub(crate) struct EncodePlaceResult<'vir> {
    pub(crate) expr: vir::ExprRef<'vir>,
    pub(crate) ty: mir::tcx::PlaceTy<'vir>,
}

macro_rules! comment {
    ($self:tt, $($arg:tt)*) => { $self.comment(
        vir::vir_format!($self.vcx, $($arg)*),
    ) };
}

impl<'vir, 'enc, E: TaskEncoder> ImpureEncVisitor<'vir, 'enc, E> {
    pub(crate) fn pcg_ctxt(&self) -> CompilerCtxt<'enc, 'vir> {
        self.fpcs_analysis.ctxt()
    }

    // TODO: make `pub(super)`
    pub(crate) fn stmt(&mut self, stmt: vir::Stmt<'vir>) {
        self.current_stmts.as_mut().unwrap().push(stmt);
    }

    fn stmts(&mut self, stmts: impl IntoIterator<Item = vir::Stmt<'vir>>) {
        for stmt in stmts {
            self.stmt(stmt);
        }
    }

    fn comment(&mut self, msg: &'vir str) {
        self.stmt(self.vcx.mk_comment_stmt(msg));
    }

    /*
    fn project_fields(
        &mut self,
        mut ty_out: crate::encoders::PredicateEncOutputRef<'vir>,
        projection: &'vir ty::List<mir::PlaceElem<'vir>>
    ) -> &'vir [&'vir str] {
        let mut ret = vec![];
        for proj in projection {
            match proj {
                mir::ProjectionElem::Field(f, ty) => {
                    let ty_out_struct = ty_out.expect_structlike();
                    let field_ty_out = self.deps.require_ref::<crate::encoders::PredicateEnc>(
                        ty,
                    ).unwrap();
                    ret.push();
                    ty_out = field_ty_out;
                }
                _ => panic!("unsupported projection"),
            }
        }
        ret
        self.vcx.alloc_slice(&projection.iter()
            .map(|proj| match proj {
            }).collect::<Vec<_>>())

        projection.iter()
            .fold((base, ty_out), |(base, ty_out), proj| match proj {
                mir::ProjectionElem::Field(f, ty) => {
                    let ty_out_struct = ty_out.expect_structlike();
                    let field_ty_out = self.deps.require_ref::<crate::encoders::PredicateEnc>(
                        ty,
                    ).unwrap();
                    (self.vcx.mk_func_app(
                        ty_out_struct.field_projection_p[f.as_usize()],
                        &[base],
                    ), field_ty_out)
                }
                _ => panic!("unsupported projection"),
            }).0
    }
    */

    /// Do the same as [self.pcs_succ] but instead of adding the statements to [self.current_stmts] return them instead.
    /// TODO: clean this up
    fn collect_pcs_succ<'a>(
        &mut self,
        state: &Pcg<'vir>,
        pcs: &'a PcgSuccessor<'vir>,
    ) -> Vec<vir::Stmt<'vir>> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        self.pcs_succ(state, pcs);
        let new_stmts = self.current_stmts.take().unwrap();
        self.current_stmts = current_stmts;
        new_stmts
    }

    pub(crate) fn block(&mut self, f: impl FnOnce(&mut Self)) -> Vec<vir::Stmt<'vir>> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        f(self);
        let new_stmts = self.current_stmts.take().unwrap();
        self.current_stmts = current_stmts;
        new_stmts
    }

    pub(crate) fn pcs_borrow_expansion(
        &mut self,
        expansion: BorrowPcgExpansion<'vir>,
        unfold: bool,
        label: Option<&'vir str>,
    ) {
        // TODO: code duplication with pcs_reborrow_expands
        if expansion.base().place().is_owned(self.pcg_ctxt()) {
            return;
        }
        let base = expansion.base();
        let PCGNode::Place(base) = base else {
            // Ignore expansions of region projections
            return;
        };
        let (place, old) = match base {
            MaybeOldPlace::Current { place } => (place, None),
            MaybeOldPlace::OldPlace(snap) => {
                // We shouldn't be unfolding old places?
                debug_assert!(!unfold);
                (
                    snap.place(),
                    Some(Self::get_location_label(self.vcx, snap.at())),
                )
            }
        };
        let place_ty = (*place).ty(self.local_decls, self.vcx.tcx());
        if matches!(
            self.local_decls[place.local].ty.kind(),
            ty::TyKind::Ref(_, _, ty::Mutability::Not)
        ) {
            return; // TODO: does this make sense??? we don't want to unfold because for immut refs we only use snapshot read/writes
        }
        let place_ty_out = self
            .deps
            .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
            .unwrap();
        let ref_to_pred = place_ty_out
            .generic_predicate
            .expect_pred_variant_opt(place_ty.variant_index);

        let mut ref_p = self.encode_place(place);
        if let Some(label) = old {
            ref_p.expr = self.vcx.mk_old(ref_p.expr, label);
        } else if let Some(label) = label {
            ref_p.expr = self.vcx.mk_local_labelled_old_expr(ref_p.expr, label);
        }
        let casts = self.place_casts(&ref_p);
        let args = place_ty_out.ref_to_ty_args(self.vcx);
        let predicate = ref_to_pred(ref_p.expr, &args)(None);
        if unfold {
            self.stmt(self.vcx.mk_unfold_stmt(predicate));
            for (apply, _) in &casts {
                self.stmt(apply);
            }
        } else {
            for (_, undo) in &casts {
                self.stmt(undo);
            }
            self.stmt(self.vcx.mk_fold_stmt(predicate));
        }
    }

    fn pcs_handle_edge(
        &mut self,
        borrows_state: &BorrowsState<'vir>,
        edge: &BorrowPcgEdge<'vir>,
        add: bool,
        label: Option<&'vir str>,
        edge_to_loop: bool,
        to_skip: &mut Vec<mir::BasicBlock>,
    ) {
        let conditions = edge.conditions();

        // For each block `b` where the edge is only valid if control flow
        // continues from `b` to a specified subset of its successors, `cond`
        // contains the corresponding VIR expression.
        let cond = conditions.all_branch_choices().map(|choices| {
            let successors = choices.successors(self.body);
            let tos = &self.from_to_vars[&choices.from()];
            let candidates = tos.iter().filter(|(to, _)| successors.contains(to));
            let conj = candidates
                .map(|(_, var)| self.vcx.mk_local_ex(var, vir::TYPE_BOOL))
                .collect::<Vec<_>>();
            // Control flow must continue from `choices.from()` to any one of the `successors`
            self.vcx.mk_disj(self.vcx.alloc_slice(&conj))
        }).collect::<Vec<_>>();
        // For each block `b` where the edge validity depends on the successor taken from `b`,
        // every successor must be valid.
        let cond = self.vcx.mk_conj(self.vcx.alloc_slice(&cond));
        let stmts = self.block(|self_| {
            self_.pcs_handle_edge_conditionless(
                borrows_state,
                edge,
                add,
                label,
                edge_to_loop,
                to_skip,
            )
        });
        if stmts.is_empty()
            || stmts
                .iter()
                .all(|stmt| matches!(stmt.kind, vir::StmtKindData::Comment(_)))
        {
            self.stmts(stmts);
            return;
        }
        let stmts = self.vcx.alloc_slice(&stmts);
        self.stmt(self.vcx.mk_if_stmt(cond, stmts, &[]));
    }

    fn pcs_handle_edge_conditionless(
        &mut self,
        borrows_state: &BorrowsState<'vir>,
        edge: &BorrowPcgEdge<'vir>,
        add: bool,
        label: Option<&'vir str>,
        edge_to_loop: bool,
        to_skip: &mut Vec<mir::BasicBlock>,
    ) {
        match edge.kind() {
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                self.pcs_borrow_expansion(expansion.clone(), add, label);
            }
            BorrowPcgEdgeKind::Abstraction(AbstractionType::FunctionCall(call)) => {
                if add {
                    // The wand will be introduced by the method call itself.
                    return;
                }
                // We may be encoding multiple edges as a single wand, skip
                // further edge removals. This is a hack to get around the fact
                // that Viper doesn't support hyperwands.
                if to_skip.contains(&call.location().block) {
                    return;
                }
                to_skip.push(call.location().block);
                // TODO: this applies *all* the wands for the referenced
                //   function call; instead we should figure out which
                //   wand it is based on the edge info.
                // TODO: closures
                let wands = self
                    .deps
                    .require_local::<WandEnc>(WandEncTask {
                        def_id: call.def_id().unwrap(),
                    })
                    .unwrap();
                let bb = &self.body[call.location().block];
                let terminator = bb.terminator.as_ref().unwrap();
                match &terminator.kind {
                    mir::TerminatorKind::Call {
                        args, destination, ..
                    } => {
                        let (_, dest_snap, _, _) = self.encode_place_snap((*destination).into());
                        let wand_args =
                            std::iter::once(dest_snap)
                                .chain(args.iter().map(|operand| {
                                    self.encode_operand_snap_immediate(&operand.node)
                                }))
                                .collect::<Vec<_>>();
                        let (label_pre, label_post) = self.call_labels[&call.location().block];
                        wands.apply_wands(&wand_args, label_pre, label_post, self);
                    }
                    _ => unreachable!(),
                }
            }
            BorrowPcgEdgeKind::Abstraction(at @ AbstractionType::Loop(_)) => {
                self.pcs_handle_wand(borrows_state, add, at, label, edge_to_loop);
            }
            _ => comment!(self, "(ignoring)"),
        }
    }

    pub(crate) fn pcs_unblock_actions(
        &mut self,
        borrows_state: &BorrowsState<'vir>,
        actions: &[BorrowPcgUnblockAction<'vir>],
        label: Option<&'vir str>,
    ) {
        let mut to_skip = Vec::new();
        for action in actions {
            self.pcs_handle_edge(
                borrows_state,
                action.edge(),
                false,
                label,
                false,
                &mut to_skip,
            );
        }
    }

    fn pcg_actions(&mut self, pcg: &Pcg<'vir>, actions: &PcgActions<'vir>, edge_to_loop: bool) {
        for action in actions.iter() {
            match action {
                PcgAction::Borrow(action) => self.borrow_action(pcg, action, edge_to_loop),
                PcgAction::Owned(action) => self.pcg_repack(action.kind()),
            }
        }
    }
    fn borrow_action(
        &mut self,
        pcg: &Pcg<'vir>,
        action: &BorrowPcgAction<'vir>,
        edge_to_loop: bool,
    ) {
        let mut to_skip = Vec::new();
        match action.kind() {
            //Weaken(Weaken<'tcx>),
            //Restore(RestoreCapability<'tcx>),
            //MakePlaceOld(Place<'tcx>),
            //SetLatest(Place<'tcx>, Location),
            //AddRegionProjectionMember(RegionProjectionMember<'tcx>, PathConditions),
            BorrowPcgActionKind::RemoveEdge(edge) => self.pcs_handle_edge(
                pcg.borrow_pcg(),
                edge,
                false,
                None,
                edge_to_loop,
                &mut to_skip,
            ),
            BorrowPcgActionKind::AddEdge { edge } => self.pcs_handle_edge(
                pcg.borrow_pcg(),
                edge,
                true,
                None,
                edge_to_loop,
                &mut to_skip,
            ),
            //RenamePlace {
            //    old: MaybeOldPlace<'tcx>,
            //    new: MaybeOldPlace<'tcx>,
            //},
            _ => comment!(self, "(ignoring)"),
        }
    }

    fn pcg_repack(&mut self, repack_op: &RepackOp<'vir>) {
        match repack_op {
            RepackOp::Expand(_) | RepackOp::Collapse(_) => {
                let (place, capability_kind) = match repack_op {
                    RepackOp::Expand(expand) => (expand.from(), expand.capability()),
                    RepackOp::Collapse(collapse) => (collapse.to(), collapse.capability()),
                    _ => unreachable!(),
                };
                if matches!(capability_kind, CapabilityKind::Write) {
                    // Collapsing an already exhaled place is a no-op
                    // TODO: unless it's through a Ref I imagine?
                    assert!(matches!(repack_op, RepackOp::Collapse(..)));
                    return;
                }
                let place_ty = place.ty(self.pcg_ctxt());
                let place_ty_out = self
                    .deps
                    .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                    .unwrap();
                let ref_to_pred = place_ty_out
                    .generic_predicate
                    .expect_pred_variant_opt(place_ty.variant_index);

                let place_enc = self.encode_place(place);
                let casts = self.place_casts(&place_enc);
                let args = place_ty_out.ref_to_ty_args(self.vcx);
                let predicate = ref_to_pred(place_enc.expr, &args)(None);
                if matches!(repack_op, pcg::free_pcs::RepackOp::Expand(..)) {
                    comment!(self, "unfolding because of RepackOp::Expand in pcs_repacks");
                    /*
                    //let variant =
                    //    def.variant(place_ty.variant_index.unwrap_or(abi::FIRST_VARIANT));
                    //let generic_field_ty = variant.fields[field_idx].ty(
                    //    self.vcx.tcx(),
                    //    GenericArgs::identity_for_item(self.vcx.tcx(), def.did()),
                    //);
                    //let cast_args = CastArgs {
                    //    expected: ty,
                    //    actual: generic_field_ty,
                    //};
                    //self.stmts(self
                    //    .deps
                    //    .require_ref::<CastToEnc<CastTypeImpure>>(cast_args)
                    //    .unwrap()
                    //    .apply_cast_if_necessary(self.vcx, proj_app));
                    //    / *
                    if let Some(cast) =
                    {
                        proj_cast_stmts_apply = Some(cast);
                        proj_cast_stmts_unapply = self
                            .deps
                            .require_ref::<CastToEnc<CastTypeImpure>>(cast_args.reversed())
                            .unwrap()
                            .apply_cast_if_necessary(self.vcx, proj_app);
                    }*/
                    self.stmt(self.vcx.mk_unfold_stmt(predicate));
                    for (apply, _) in &casts {
                        self.stmt(apply);
                    }
                } else {
                    for (_, undo) in &casts {
                        self.stmt(undo);
                    }
                    self.stmt(self.vcx.mk_fold_stmt(predicate));
                }
            }
            RepackOp::Weaken(place, CapabilityKind::Exclusive, CapabilityKind::Write) => {
                let place_ty = (*place).ty(self.pcg_ctxt());
                assert!(place_ty.variant_index.is_none());

                let place_ty_out = self
                    .deps
                    .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                    .unwrap();

                let place_enc = self.encode_place(*place);
                comment!(self, "exhale due to Weaken(E, W)");
                self.stmt(self.vcx.mk_exhale_stmt(place_ty_out.ref_to_pred(
                    self.vcx,
                    place_enc.expr,
                    None,
                )));
            }
            ignored_op @ (RepackOp::RegainLoanedCapability(..)
            | RepackOp::Weaken(_, CapabilityKind::Exclusive, CapabilityKind::Read)) => {
                self.stmt(self.vcx.mk_comment_stmt(vir::vir_format!(
                    self.vcx,
                    "ignored repack op: {ignored_op:?}"
                )));
            }
            unsupported_op => {
                self.stmt(self.vcx.mk_comment_stmt(vir::vir_format!(
                    self.vcx,
                    "unsupported repack op: {unsupported_op:?}"
                )));
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
            }
        }
    }

    fn pcs_succ<'a>(&mut self, pcg_state: &Pcg<'vir>, succ: &'a PcgSuccessor<'vir>) {
        let edge_to_loop = self.loop_analysis.loop_head_of(succ.block()).is_some();
        self.pcg_actions(pcg_state, succ.actions(), edge_to_loop);
    }

    fn encode_operand_snap(&mut self, operand: &mir::Operand<'vir>) -> vir::ExprSnap<'vir> {
        match operand {
            &mir::Operand::Move(source) => {
                let (result, snap_val, _, ty_out) = self.encode_place_snap(Place::from(source));

                let tmp_exp = self.new_tmp(ty_out.snapshot()).1;
                self.stmt(self.vcx.mk_pure_assign_stmt(tmp_exp, snap_val));
                self.stmt(
                    self.vcx
                        .mk_exhale_stmt(ty_out.ref_to_pred(self.vcx, result.expr, None)),
                );
                tmp_exp
            }
            &mir::Operand::Copy(place) => {
                // When encoding a Copy, we proceed in two phases:
                // - "impure" heap accesses to walk through predicates which
                //   should be unfolded by the PCG at this point;
                // - "pure" snapshot accesses to access values as soon as we
                //   cross a shared reference.
                // The crossing point is marked with `crossed_ref` and either
                // coincides with taking a snapshot of the heap accesses we
                // have performed thus far, or, if the local variable itself is
                // a shared reference, it happens immediately.
                let mut place_ty = mir::tcx::PlaceTy::from_ty(self.local_decls[place.local].ty);
                let mut encoded_place = mir::Place::from(place.local);
                let (mut crossed_ref, mut result) =
                    if matches!(place_ty.ty.kind(), TyKind::Ref(_, _, ty::Mutability::Not)) {
                        let ty_out = self
                            .deps
                            .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                            .unwrap();
                        let snap_val = ty_out
                            .ref_to_snap(self.vcx, self.local_defs.locals[place.local].local_ex);
                        (true, snap_val.as_dyn())
                    } else {
                        (false, self.local_defs.locals[place.local].local_ex.as_dyn())
                    };
                for elem in place.projection {
                    if crossed_ref {
                        use vir::Reify;
                        let (expr, _) = crate::encoders::mir_pure::encode_place_element(
                            self.vcx,
                            self.deps,
                            place_ty,
                            elem,
                            result.lift().downcast_ty(),
                            None,
                        );
                        result = expr.reify(self.vcx, (self.def_id, &[])).as_dyn();
                    } else {
                        result = self
                            .encode_place_element(place_ty, elem, result.downcast_ty())
                            .as_dyn();
                    }
                    place_ty = place_ty.projection_ty(self.vcx.tcx(), elem);
                    encoded_place = encoded_place.project_deeper(&[elem], self.vcx.tcx());
                    if !crossed_ref
                        && matches!(place_ty.ty.kind(), TyKind::Ref(_, _, ty::Mutability::Not))
                    {
                        let ty_out = self
                            .deps
                            .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                            .unwrap();
                        result = ty_out.ref_to_snap(self.vcx, result.downcast_ty()).as_dyn();
                        crossed_ref = true;
                    }
                }
                if !crossed_ref {
                    let ty_out = self
                        .deps
                        .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                        .unwrap();
                    result = ty_out.ref_to_snap(self.vcx, result.downcast_ty()).as_dyn();
                }
                result.downcast_ty()
            }
            mir::Operand::Constant(box constant) => self.encode_constant(constant).upcast_ty(),
        }
    }

    fn encode_operand(&mut self, operand: &mir::Operand<'vir>) -> vir::ExprRef<'vir> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx());
        let (encode_place_result, ty_out) = match operand {
            &mir::Operand::Move(source) => return self.encode_place(Place::from(source)).expr,
            &mir::Operand::Copy(_source) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                (self.encode_operand_snap(operand), ty_out)
            }
            mir::Operand::Constant(box constant) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                let constant = self.encode_constant(constant);
                (constant.upcast_ty(), ty_out)
            }
        };
        let tmp_exp: vir::ExprRef<'vir> = self.new_tmp(vir::TYPE_REF).1;
        self.stmt(ty_out.apply_method_assign(self.vcx, tmp_exp, encode_place_result));
        tmp_exp
    }

    /// Encodes the snapshot of an operand. This should not be used for encoding
    /// regular mir statements/terminators as it doesn't match the semantics.
    fn encode_operand_snap_immediate(
        &mut self,
        operand: &mir::Operand<'vir>,
    ) -> vir::ExprSnap<'vir> {
        match operand {
            &mir::Operand::Move(source) => self.encode_place_snap(Place::from(source)).1,
            &mir::Operand::Copy(source) => self.encode_place_snap(Place::from(source)).1,
            mir::Operand::Constant(box constant) => self.encode_constant(constant).upcast_ty(),
        }
    }

    fn encode_constant(&mut self, constant: &mir::ConstOperand<'vir>) -> vir::ExprCSnap<'vir> {
        self.deps
            .require_local::<ConstEnc>((constant.const_, 0, self.def_id))
            .unwrap()
    }

    pub(crate) fn encode_place(&mut self, place: Place<'vir>) -> EncodePlaceResult<'vir> {
        let mut place_ty = mir::tcx::PlaceTy::from_ty(self.local_decls[place.local].ty);
        let mut encoded_place = mir::Place::from(place.local);
        let mut result = self.local_defs.locals[place.local].local_ex;
        // TODO: factor this out (duplication with pure encoder)?
        for &elem in place.projection {
            result = self.encode_place_element(place_ty, elem, result);
            place_ty = place_ty.projection_ty(self.vcx.tcx(), elem);
            encoded_place = encoded_place.project_deeper(&[elem], self.vcx.tcx());
        }
        EncodePlaceResult {
            expr: result,
            ty: place_ty,
        }
    }

    fn place_casts(
        &mut self,
        place: &EncodePlaceResult<'vir>,
    ) -> Vec<(vir::Stmt<'vir>, vir::Stmt<'vir>)> {
        match place.ty.ty.kind() {
            TyKind::Adt(def, _) if def.is_box() => {
                let proj_app =
                    self.encode_place_element(place.ty, mir::ProjectionElem::Deref, place.expr);
                self.deps
                    .require_local::<RustTyCastersEnc<CastTypeImpure>>(
                        place.ty.ty.expect_boxed_ty(),
                    )
                    .unwrap()
                    .cast_to_concrete_if_possible(self.vcx, proj_app)
                    .into_iter()
                    .map(|cs| (cs.apply_cast_stmt, cs.unapply_cast_stmt))
                    .collect()
            }
            TyKind::Adt(def, generics) => {
                let variant = match (def.adt_kind(), place.ty.variant_index) {
                    (ty::AdtKind::Enum, Some(idx)) => def.variant(idx),
                    (ty::AdtKind::Enum, None) => return Default::default(),
                    (_, Some(_)) => unreachable!(),
                    _ => def.non_enum_variant(),
                };
                variant
                    .fields
                    .iter_enumerated()
                    .filter_map(|(idx, f)| {
                        let ty = f.ty(self.vcx.tcx(), generics);
                        let elem = mir::ProjectionElem::Field(idx, ty);
                        let proj_app = self.encode_place_element(place.ty, elem, place.expr);
                        let generic_field_ty = f.ty(
                            self.vcx.tcx(),
                            GenericArgs::identity_for_item(self.vcx.tcx(), def.did()),
                        );
                        let cast_args = CastArgs {
                            expected: ty,
                            actual: generic_field_ty,
                        };
                        self.deps
                            .require_ref::<CastToEnc<CastTypeImpure>>(cast_args)
                            .unwrap()
                            .apply_cast_if_necessary(self.vcx, proj_app)
                            .map(|apply| {
                                let unapply = self
                                    .deps
                                    .require_ref::<CastToEnc<CastTypeImpure>>(cast_args.reversed())
                                    .unwrap()
                                    .apply_cast_if_necessary(self.vcx, proj_app)
                                    .unwrap();
                                (apply, unapply)
                            })
                    })
                    .collect()
            }
            TyKind::Tuple(ty) => ty
                .iter()
                .enumerate()
                .filter_map(|(idx, ty)| {
                    let elem = mir::ProjectionElem::Field(abi::FieldIdx::from_usize(idx), ty);
                    let proj_app = self.encode_place_element(place.ty, elem, place.expr);
                    self.deps
                        .require_local::<RustTyCastersEnc<CastTypeImpure>>(ty)
                        .unwrap()
                        .cast_to_concrete_if_possible(self.vcx, proj_app)
                        .map(|cs| (cs.apply_cast_stmt, cs.unapply_cast_stmt))
                })
                .collect(),
            _ => Vec::new(),
        }
    }

    pub(crate) fn encode_place_snap(
        &mut self,
        place: Place<'vir>,
    ) -> (
        EncodePlaceResult<'vir>,
        vir::ExprSnap<'vir>,
        mir::tcx::PlaceTy<'vir>,
        RustTyPredicatesEncOutputRef<'vir>,
    ) {
        let ty = (*place).ty(self.local_decls, self.vcx.tcx());
        assert!(ty.variant_index.is_none());

        let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty.ty).unwrap();
        let result = self.encode_place(place);
        let snap = ty_out.ref_to_snap(self.vcx, result.expr);
        (result, snap, ty, ty_out)
    }

    fn encode_place_element(
        &mut self,
        place_ty: mir::tcx::PlaceTy<'vir>,
        elem: mir::PlaceElem<'vir>,
        expr: vir::ExprRef<'vir>,
    ) -> vir::ExprRef<'vir> {
        match elem {
            mir::ProjectionElem::Field(field_idx, _) => {
                let e_ty = self
                    .deps
                    .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                    .unwrap();
                let field_access = e_ty
                    .generic_predicate
                    .expect_variant_opt(place_ty.variant_index)
                    .ref_to_field_refs;
                let projection_p = field_access[field_idx.as_usize()];
                let instantiated_ty = self
                    .deps
                    .require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(place_ty.ty)
                    .unwrap();
                let proj_args = e_ty
                    .generic_predicate
                    .ref_to_ty_args(self.vcx, instantiated_ty);
                projection_p(expr, &proj_args)
            }
            // TODO: should all variants start at the same `Ref`?
            mir::ProjectionElem::Downcast(..) => expr,
            mir::ProjectionElem::Deref => {
                assert!(place_ty.variant_index.is_none());
                let e_ty = self
                    .deps
                    .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                    .unwrap();
                // println!("  trying to deref place elem {elem:?}");
                // println!("    place_ty: {place_ty:?}");
                match place_ty.ty.kind() {
                    ty::TyKind::Adt(adt, _) if adt.is_box() => {
                        let field_access = e_ty
                            .generic_predicate
                            .expect_variant_opt(None)
                            .ref_to_field_refs;
                        let projection_p = field_access[0];
                        let instantiated_ty = self
                            .deps
                            .require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(place_ty.ty)
                            .unwrap();
                        let proj_args = e_ty
                            .generic_predicate
                            .ref_to_ty_args(self.vcx, instantiated_ty);
                        projection_p(expr, &proj_args)
                    }
                    ty::TyKind::Ref(_, _, ty::Mutability::Not) => {
                        // TODO: unfold? function? use snapshot?
                        let instantiated_ty = self
                            .deps
                            .require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(place_ty.ty)
                            .unwrap();
                        let deref_args = e_ty
                            .generic_predicate
                            .ref_to_ty_args(self.vcx, instantiated_ty);
                        (e_ty.generic_predicate.expect_immref().deref_func)(expr, &deref_args)
                    }
                    ty::TyKind::Ref(_, _, ty::Mutability::Mut) => {
                        // TODO: unfold? function? use snapshot?
                        let expr_deref = (e_ty.generic_predicate.expect_mutref().deref_func)(expr);
                        // TODO: we are writing directly to the deref; is a cast ever
                        //   needed?
                        /*
                        let inner_ty = place_ty.ty.builtin_deref(true).unwrap();
                        if let Some(cast_stmts) = self
                            .deps
                            .require_local::<RustTyCastersEnc<CastTypeImpure>>(inner_ty)
                            .unwrap()
                            .cast_to_concrete_if_possible(self.vcx, expr_deref)
                        {
                            self.stmt(cast_stmts.apply_cast_stmt);
                            return (expr_deref, Some(cast_stmts.unapply_cast_stmt));
                        }
                        */
                        expr_deref
                    }
                    _ => unreachable!(),
                }
            }
            _ => todo!("Unsupported ProjectionElem {:?}", elem),
        }
    }

    fn new_tmp<T: CompType>(
        &mut self,
        ty: vir::Type<'vir, T>,
    ) -> (vir::Local<'vir, T>, vir::Expr<'vir, T>) {
        let name = vir::vir_format!(self.vcx, "_tmp{}", self.tmp_ctr);
        let local = vir::vir_local_decl! { self.vcx; [name] : [ty] };
        self.tmp_ctr += 1;
        self.stmt(self.vcx.mk_local_decl_stmt(local, None));
        let tmp = self.vcx.mk_local(name, ty);
        (tmp, self.vcx.mk_local_ex_local(tmp))
    }

    pub(crate) fn new_label(&mut self, base: &str) -> &'vir str {
        let name = vir::vir_format!(self.vcx, "{base}{}", self.label_ctr);
        self.label_ctr += 1;
        self.stmt(self.vcx.mk_label_stmt(name));
        name
    }

    fn new_after_label(&mut self, location: mir::Location) {
        let name = vir::vir_format!(
            self.vcx,
            "_after_{}_{}",
            location.block.index(),
            location.statement_index
        );
        self.stmt(self.vcx.mk_label_stmt(name));
    }

    fn set_from_to_flag(&mut self, from: mir::BasicBlock, to: mir::BasicBlock) -> vir::Stmt<'vir> {
        let name = vir::vir_format!(self.vcx, "_from_bb{}_to_bb{}", from.index(), to.index());
        let tos = self.from_to_vars.entry(from).or_default();
        debug_assert!(!tos.contains(&(to, name)));
        tos.push((to, name));
        let local = self.vcx.mk_local_ex(name, vir::TYPE_BOOL);
        self.vcx
            .mk_pure_assign_stmt(local, self.vcx.mk_bool::<true>())
    }
}

impl<'vir, 'enc, E: TaskEncoder> mir::visit::Visitor<'vir> for ImpureEncVisitor<'vir, 'enc, E> {
    fn visit_basic_block_data(&mut self, block: mir::BasicBlock, data: &mir::BasicBlockData<'vir>) {
        // We are verifying the absence of panics, so cleanup block should never
        // be reached, or even referenced.
        if data.is_cleanup {
            self.encoded_blocks.push(
                self.vcx.mk_cfg_block(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(block.as_usize())),
                    &[],
                    &[],
                    self.vcx
                        .mk_dummy_stmt(vir::vir_format!(self.vcx, "cleanup block",)),
                ),
            );
            return;
        }
        if self.deps.check_cycle().is_err() {
            return;
        }

        self.current_stmts = Some(Vec::with_capacity(
            data.statements.len(), // TODO: not exact?
        ));
        self.current_block_label = Some(
            self.vcx
                .alloc(vir::CfgBlockLabelData::BasicBlock(block.as_usize())),
        );
        let cfpcs = self.fpcs_analysis.get_all_for_bb(block).unwrap().unwrap();

        // Calculate invariant at loop head
        let invariant = self
            .loop_analysis
            .loop_head_of(block)
            .map(|lh| self.get_loop_inv(lh, &cfpcs))
            .unwrap_or_default();

        self.current_fpcs = Some(cfpcs);

        if ENCODE_REACH_BB {
            self.stmt(self.vcx.mk_pure_assign_stmt(
                self.vcx.mk_local_ex(
                    vir::vir_format!(self.vcx, "_reach_bb{}", block.as_usize()),
                    vir::TYPE_BOOL,
                ),
                self.vcx.mk_bool::<true>(),
            ));
        }

        /*
        let mut phi_stmts = vec![];
        if let Some(phi_nodes) = self.ssa_analysis.phi.get(&block) {
            for phi_node in phi_nodes {
                assert!(!phi_node.sources.is_empty());
                let local_ty = &self.local_types[phi_node.local];
                let expr = phi_node.sources.iter()
                    .fold(self.vcx.mk_func_app(
                        local_ty.function_unreachable,
                        &[],
                    ), |prev, source| self.vcx.alloc(vir::ExprData::Ternary(self.vcx.alloc(vir::TernaryData {
                        cond: self.vcx.mk_local_ex(vir::vir_format_identifier!(self.vcx, "_reach_bb{}", source.0.as_usize())),
                        then: self.vcx.mk_local_ex(vir::vir_format_identifier!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), source.1)),
                        else_: prev,
                    }))));
                phi_stmts.push(vir::StmtData::LocalDecl(self.vcx.alloc(vir::LocalDeclData {
                    name: vir::vir_format_identifier!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), phi_node.new_version),
                    ty: self.local_types[phi_node.local].snapshot,
                    expr: Some(expr),
                })));
            }
        }
        for phi_stmt in phi_stmts {
            self.stmt(phi_stmt);
        }
        */

        assert!(self.current_terminator.is_none());
        self.super_basic_block_data(block, data);
        let stmts = self.current_stmts.take().unwrap();
        let terminator = self.current_terminator.take().unwrap();
        self.encoded_blocks.push(self.vcx.mk_cfg_block(
            self.current_block_label.take().unwrap(),
            invariant,
            self.vcx.alloc_slice(&stmts),
            terminator,
        ));
    }

    fn visit_statement(&mut self, statement: &mir::Statement<'vir>, location: mir::Location) {
        if self.deps.check_cycle().is_err() {
            return;
        }

        comment!(self, "[MIR] {location:?}: {statement:?}");

        let current_fpcs = self.current_fpcs.take().unwrap();
        let cfpcs = &current_fpcs.statements[location.statement_index];
        for phase in EvalStmtPhase::phases() {
            self.pcg_actions(&cfpcs.states[phase], cfpcs.actions(phase), false);
        }
        self.current_fpcs = Some(current_fpcs);

        // TODO: these should not be ignored, but should havoc the local instead
        // This clears up the noise a bit, making sure StorageLive and other
        // kinds do not show up in the comments.
        // TODO: also make sure we don't ignore PCG annotations for these,
        //   *if* the pcs calls for mid-statement are moved later.
        const IGNORE_NOP_STMTS: bool = true;
        if IGNORE_NOP_STMTS {
            match &statement.kind {
                mir::StatementKind::StorageLive(..) | mir::StatementKind::StorageDead(..) => {
                    return;
                }
                _ => {}
            }
        }

        match &statement.kind {
            mir::StatementKind::Assign(box (dest, rvalue)) => {
                // What are we assigning to?
                let proj_enc = self.encode_place(Place::from(*dest));

                let rvalue_ty = rvalue.ty(self.local_decls, self.vcx.tcx());

                // The snapshot of the value that we are assigning.
                let rval_enc = match rvalue {
                    mir::Rvalue::Use(op) => self.encode_operand_snap(op),

                    //mir::Rvalue::Repeat(Operand<'vir>, Const<'vir>) => {}
                    //mir::Rvalue::ThreadLocalRef(DefId) => {}
                    //mir::Rvalue::AddressOf(Mutability, Place<'vir>) => {}
                    //mir::Rvalue::Len(Place<'vir>) => {}
                    //mir::Rvalue::Cast(CastKind, Operand<'vir>, Ty<'vir>) => {}

                    mir::Rvalue::BinaryOp(op, box (l, r)) => {
                        let l_ty = l.ty(self.local_decls, self.vcx.tcx());
                        let r_ty = r.ty(self.local_decls, self.vcx.tcx());
                        use crate::encoders::MirBuiltinEncTask::{BinOp, CheckedBinOp};
                        let task = if op.is_overflowing() {
                            CheckedBinOp(rvalue_ty, *op, l_ty, r_ty)
                        } else {
                            BinOp(rvalue_ty, *op, l_ty, r_ty)
                        };
                        let binop_function = self.deps.require_ref::<MirBuiltinEnc>(
                            task
                        ).unwrap().bin_op().unwrap();
                        binop_function(
                            self.encode_operand_snap(l).downcast_ty(),
                            self.encode_operand_snap(r).downcast_ty(),
                        ).upcast_ty()
                    }

                    //mir::Rvalue::NullaryOp(NullOp, Ty<'vir>) => {}

                    mir::Rvalue::UnaryOp(unop, operand) => {
                        let operand_ty = operand.ty(self.local_decls, self.vcx.tcx());
                        let unop_function = self.deps.require_ref::<MirBuiltinEnc>(
                            crate::encoders::MirBuiltinEncTask::UnOp(
                                rvalue_ty,
                                *unop,
                                operand_ty,
                            ),
                        ).unwrap().un_op().unwrap();
                        unop_function(self.encode_operand_snap(operand).downcast_ty()).upcast_ty()
                        /*
                        assert!(source.projection.is_empty());
                        let source_version = self.ssa_analysis.version.get(&(location, source.local)).unwrap();
                        let source_name = vir::vir_format_identifier!(self.vcx, "_{}s_{}", source.local.index(), source_version);

                        let unop_function = self.deps.require_ref::<crate::encoders::MirBuiltinEnc>(
                            crate::encoders::MirBuiltinEncTask::UnOp(
                                *unop,
                                source.ty(self.local_decls, self.vcx.tcx()).ty,
                            ),
                        ).unwrap().name;
                        Some(self.vcx.mk_func_app(
                            unop_function,
                            &[self.vcx.mk_local_ex(source_name)],
                        ))*/
                    }

                    mir::Rvalue::Aggregate(
                        box kind @ (mir::AggregateKind::Adt(..) | mir::AggregateKind::Tuple),
                        fields,
                    ) => {
                        let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                        let sl = match kind {
                            mir::AggregateKind::Adt(_, vidx, _, _, _) =>
                                e_rvalue_ty.generic_predicate.get_variant_any(*vidx),
                            _ => e_rvalue_ty.generic_predicate.expect_structlike()
                        };
                        let field_tys = fields.iter()
                            .map(|field| field.ty(self.local_decls, self.vcx.tcx()))
                            .collect::<Vec<_>>();
                        let ty_caster = self.deps.require_local::<AggregateSnapArgsCastEnc>(
                            AggregateSnapArgsCastEncTask {
                                tys: field_tys,
                                aggregate_type: kind.into()
                            }
                        ).unwrap();
                        let field_snaps = fields.iter().map(|field| self.encode_operand_snap(field)).collect::<Vec<_>>();
                        let casted_args = ty_caster.apply_casts(self.vcx, field_snaps.into_iter());
                        (sl.snap_data.field_snaps_to_snap)(&casted_args).upcast_ty()
                    }
                    mir::Rvalue::Discriminant(place) => {
                        let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                        let place_ty = place.ty(self.local_decls, self.vcx.tcx());
                        let ty = self.deps.require_ref::<RustTyPredicatesEnc>(place_ty.ty).unwrap();
                        let place_expr = self.encode_place(Place::from(*place)).expr;

                        match ty.generic_predicate.get_enumlike().filter(|_| place_ty.variant_index.is_none()) {
                            Some(el) => {
                                let discr_ty = place_ty.ty.discriminant_ty(self.vcx.tcx());
                                let discr_ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(discr_ty).unwrap();
                                let discr_expr = discr_ty_out.ref_to_snap(self.vcx, (el.as_ref().unwrap().discr)(place_expr));
                                self.vcx.mk_unfolding_expr(ty.ref_to_pred_app(self.vcx, place_expr, Some(self.vcx.mk_wildcard())), discr_expr)
                            }
                            None => {
                                // mir::Rvalue::Discriminant documents "Returns zero for types without discriminant"
                                let zero = self.vcx.mk_uint::<0>();
                                (e_rvalue_ty.generic_predicate.expect_prim().prim_to_snap)(zero.upcast_ty()).upcast_ty()
                            }
                        }
                    }
                    mir::Rvalue::Ref(_reg, _kind, place) => {
                        match rvalue_ty.kind() {
                            TyKind::Ref(_, inner_ty, ty::Mutability::Not) => {
                                let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                                let place_expr = self.encode_place(Place::from(*place)).expr;
                                let cast = self
                                    .deps
                                    .require_local::<RustTyCastersEnc<CastTypePure>>(*inner_ty)
                                    .unwrap();
                                /*
                                let snap = inner_ty_out.generic_predicate.ref_to_snap.apply(self.vcx, &[place_expr]);
                                // The snapshot of the referenced value should be encoded as a generic `Param`
                                */
                                let snap = self.encode_operand_snap(&mir::Operand::Copy(*place));
                                let snap = cast.cast_to_generic_if_necessary(self.vcx, snap);
                                let inner = e_rvalue_ty.generic_predicate.expect_immref();
                                (inner.snap_data.prim_to_snap)(place_expr, snap).upcast_ty()
                            }
                            TyKind::Ref(_, inner_ty, ty::Mutability::Mut) => {
                                let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                                let (place_expr, snap, _, _) = self.encode_place_snap(Place::from(*place));
                                let cast = self
                                    .deps
                                    .require_local::<RustTyCastersEnc<CastTypePure>>(*inner_ty)
                                    .unwrap();

                                // The snapshot of the referenced value should be encoded as a generic `Param`
                                let snap = cast.cast_to_generic_if_necessary(self.vcx, snap);
                                let inner = e_rvalue_ty.generic_predicate.expect_mutref();
                                (inner.snap_data.prim_to_snap)(place_expr.expr, snap).upcast_ty()
                            }
                            _ => unreachable!(),
                        }
                    }

                    //mir::Rvalue::Discriminant(Place<'vir>) => {}
                    //mir::Rvalue::ShallowInitBox(Operand<'vir>, Ty<'vir>) => {}
                    //mir::Rvalue::CopyForDeref(Place<'vir>) => {}
                    other => {
                        let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                        tracing::error!("unsupported rvalue {other:?}");
                        self.vcx.mk_todo_expr(vir::vir_format!(self.vcx, "rvalue {rvalue:?}"), e_rvalue_ty.snapshot())
                    }
                };

                // TODO: this is to do FPCS repacks after accessing the rvalue
                //let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                //let (rval_var, rval_expr) = self.new_tmp(e_rvalue_ty.snapshot());
                //self.stmt(self.vcx.mk_pure_assign_stmt(rval_expr, expr));

                //self.fpcs_repacks_location(location, |loc| &loc.repacks_middle);

                let dest_ty = dest.ty(self.local_decls, self.vcx.tcx());
                assert!(dest_ty.variant_index.is_none());
                let dest_ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(dest_ty.ty).unwrap();
                let method_assign_app = dest_ty_out.apply_method_assign(
                    self.vcx,
                    proj_enc.expr,
                    rval_enc,
                );

                self.stmt(method_assign_app);
            }

            // no-ops ?
            mir::StatementKind::StorageLive(..)
            | mir::StatementKind::StorageDead(..) => {}

            // no-ops
            mir::StatementKind::FakeRead(_)
            | mir::StatementKind::Retag(..)
            | mir::StatementKind::PlaceMention(_)
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::Coverage(_)
            //| mir::StatementKind::ConstEvalCounter
            | mir::StatementKind::Nop => {}

            k => todo!("statement {k:?}"),
        }
        self.new_after_label(location);
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'vir>, location: mir::Location) {
        if self.deps.check_cycle().is_err() {
            return;
        }

        comment!(self, "[MIR] {location:?}: {:?}", terminator.kind);
        let span = terminator.source_info.span;

        let current_fpcs = self.current_fpcs.take().unwrap();
        let cfpcs = &current_fpcs.statements[location.statement_index];
        for phase in EvalStmtPhase::phases() {
            comment!(self, "PCG (T) {phase}");
            self.pcg_actions(&cfpcs.states[phase], cfpcs.actions(phase), false);
        }
        self.current_fpcs = Some(current_fpcs);

        let terminator = match &terminator.kind {
            mir::TerminatorKind::Goto { target }
            | mir::TerminatorKind::FalseUnwind {
                real_target: target,
                ..
            }
            | mir::TerminatorKind::FalseEdge {
                real_target: target,
                ..
            } => {
                const REAL_TARGET_SUCC_IDX: usize = 0;
                // Ensure that the terminator succ that we use for the repacks is the correct one
                assert_eq!(
                    &self.current_fpcs.as_ref().unwrap().terminator.succs[REAL_TARGET_SUCC_IDX]
                        .block(),
                    target
                );
                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows =
                    current_fpcs.statements.last().unwrap().states[EvalStmtPhase::PostMain].clone();
                self.pcs_succ(
                    &borrows,
                    &current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX],
                );
                self.current_fpcs = Some(current_fpcs);
                let set_flag = self.set_from_to_flag(location.block, *target);
                self.stmt(set_flag);
                self.vcx.mk_goto_stmt(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                )
            }
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let discr_ty_rs = discr.ty(self.local_decls, self.vcx.tcx());
                let discr_ty = self
                    .deps
                    .require_ref::<RustTyPredicatesEnc>(discr_ty_rs)
                    .unwrap()
                    .generic_predicate
                    .expect_prim();

                let goto_targets = self.vcx.alloc_slice(
                    &targets
                        .iter()
                        .enumerate()
                        .map(|(idx, (value, target))| {
                            assert_eq!(
                                self.current_fpcs.as_ref().unwrap().terminator.succs[idx].block(),
                                target
                            );

                            let current_fpcs = self.current_fpcs.take().unwrap();
                            let borrows = &current_fpcs.statements.last().unwrap().states
                                [EvalStmtPhase::PostMain];
                            let mut extra_stmts =
                                self.collect_pcs_succ(borrows, &current_fpcs.terminator.succs[idx]);
                            self.current_fpcs = Some(current_fpcs);
                            extra_stmts.push(self.set_from_to_flag(location.block, target));

                            self.vcx.mk_goto_if_target(
                                discr_ty.expr_from_bits(discr_ty_rs, value).as_dyn(),
                                self.vcx
                                    .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                                self.vcx.alloc_slice(&extra_stmts),
                            )
                        })
                        .collect::<Vec<_>>(),
                );
                let goto_otherwise = self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(
                    targets.otherwise().as_usize(),
                ));

                let otherwise_succ_idx = goto_targets.len();
                assert_eq!(
                    self.current_fpcs.as_ref().unwrap().terminator.succs[otherwise_succ_idx]
                        .block(),
                    targets.otherwise()
                );

                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows =
                    &current_fpcs.statements.last().unwrap().states[EvalStmtPhase::PostMain];
                let mut otherwise_stmts = self
                    .collect_pcs_succ(borrows, &current_fpcs.terminator.succs[otherwise_succ_idx]);
                self.current_fpcs = Some(current_fpcs);
                otherwise_stmts.push(self.set_from_to_flag(location.block, targets.otherwise()));

                let discr_ex =
                    (discr_ty.snap_to_prim)(self.encode_operand_snap(discr).downcast_ty());
                self.vcx.mk_goto_if_stmt(
                    discr_ex.as_dyn(), // self.vcx.mk_local_ex(discr_name),
                    goto_targets,
                    goto_otherwise,
                    self.vcx.alloc_slice(&otherwise_stmts),
                )
            }
            mir::TerminatorKind::Return => {
                let current_fpcs = self.current_fpcs.take().unwrap();
                let wands = core::mem::take(&mut self.wands);
                let borrows = current_fpcs.statements.last().unwrap().states
                    [EvalStmtPhase::PostMain]
                    .borrow_pcg();
                let wand_packages = wands.package_wands(borrows, self);
                self.wands = wands;
                self.current_fpcs = Some(current_fpcs);
                self.stmts(wand_packages);

                self.vcx
                    .mk_goto_stmt(self.vcx.alloc(vir::CfgBlockLabelData::End))
            }
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                // emit the current block, create a new label for the terminator
                // TODO: should we do this for any other terminators?
                let current_block = match self.current_block_label {
                    Some(vir::CfgBlockLabelData::BasicBlock(block)) => *block,
                    _ => unreachable!(),
                };
                self.encoded_blocks.push(
                    self.vcx.mk_cfg_block(
                        std::mem::replace(
                            &mut self.current_block_label,
                            Some(self.vcx.alloc(vir::CfgBlockLabelData::BasicBlockTerminator(
                                current_block,
                            ))),
                        )
                        .unwrap(),
                        &[],
                        self.vcx.alloc_slice(
                            &std::mem::replace(&mut self.current_stmts, Some(Vec::new())).unwrap(),
                        ),
                        self.vcx
                            .mk_goto_stmt(self.vcx.alloc(
                                vir::CfgBlockLabelData::BasicBlockTerminator(current_block),
                            )),
                    ),
                );

                let (func_def_id, caller_substs) = self.get_def_id_and_caller_substs(func);
                let is_pure = crate::encoders::with_proc_spec(
                    SpecQuery::GetProcKind(
                        func_def_id,
                        ty::List::identity_for_item(self.vcx().tcx(), func_def_id),
                    ),
                    |spec| spec.kind.is_pure().unwrap_or_default(),
                )
                .unwrap_or_default();

                let dest = self.encode_place(Place::from(*destination)).expr;

                let task = (func_def_id, self.def_id);
                let sig = self.vcx().tcx().fn_sig(func_def_id);
                let sig = if self.monomorphize {
                    let typing_env = ty::TypingEnv::post_analysis(self.vcx().tcx(), self.def_id);
                    self.vcx().tcx().instantiate_and_normalize_erasing_regions(
                        caller_substs,
                        typing_env,
                        sig,
                    )
                } else {
                    sig.instantiate_identity()
                };
                let fn_arg_tys = sig
                    .inputs()
                    .iter()
                    .map(|i| i.skip_binder())
                    .copied()
                    .collect::<Vec<_>>();
                if is_pure {
                    let pure_func_app = self.encode_pure_func_app(
                        func_def_id,
                        sig,
                        caller_substs,
                        args,
                        destination,
                        self.def_id,
                        &(),
                    );

                    let return_ty = destination.ty(self.local_decls, self.vcx.tcx()).ty;
                    let assign_stmt = self
                        .deps
                        .require_ref::<RustTyPredicatesEnc>(return_ty)
                        .unwrap()
                        .apply_method_assign(self.vcx, dest, pure_func_app);

                    self.stmt(assign_stmt);
                } else {
                    let Ok(func_out) = self.deps.require_ref::<encoders::MirImpureEnc>(
                        FunctionCallTaskDescription::new(task.0, caller_substs, task.1),
                    ) else {
                        self.current_terminator = Some(
                            self.vcx
                                .mk_dummy_stmt(vir::vir_format!(self.vcx, "recursion",)),
                        );
                        return;
                    };

                    let method_in = args
                        .iter()
                        .map(|arg| self.encode_operand(&arg.node))
                        .collect::<Vec<_>>();

                    for ((fn_arg_ty, arg), arg_ex) in
                        fn_arg_tys.iter().zip(args.iter()).zip(method_in.iter())
                    {
                        let local_decls = self.local_decls_src();
                        let tcx = self.vcx().tcx();
                        let arg_ty = arg.node.ty(local_decls, tcx);
                        let caster = self
                            .deps()
                            .require_ref::<CastToEnc<CastTypeImpure>>(CastArgs {
                                expected: *fn_arg_ty,
                                actual: arg_ty,
                            })
                            .unwrap();
                        // In this context, `apply_cast_if_necessary` returns
                        // the impure operation to perform the cast
                        if let Some(stmt) = caster.apply_cast_if_necessary(self.vcx(), arg_ex) {
                            self.stmt(stmt);
                        }
                    }

                    let method_args = std::iter::once(dest).chain(method_in).collect::<Vec<_>>();
                    let mono = self.monomorphize;
                    let ty_args = self
                        .deps()
                        .require_local::<LiftedFuncAppTyParamsEnc>((mono, caller_substs))
                        .unwrap()
                        .iter()
                        .map(|ty| ty.expr(self.vcx()))
                        .collect::<Vec<_>>();

                    let label_pre = self.new_label("pre");
                    self.vcx().with_span(span, |vcx| {
                        vcx.handle_error(
                            "call.precondition:assertion.false",
                            move |reason_span_opt| {
                                let mut error = PrustiError::verification(
                                    "precondition might not hold",
                                    span.into(),
                                );
                                if let Some(reason_span) = reason_span_opt {
                                    error.add_note_mut(
                                        "the failing precondition is here",
                                        Some(reason_span.into()),
                                    );
                                }
                                Some(vec![error])
                            },
                        );
                        self.stmt(
                            self.vcx.alloc(vir::StmtGenData::new(
                                self.vcx
                                    .alloc((func_out.method_ref)(&method_args, &ty_args)),
                            )),
                        );
                    });
                    let label_post = self.new_label("post");
                    self.call_labels
                        .insert(location.block, (label_pre, label_post));
                    let expected_ty = destination.ty(self.local_decls_src(), self.vcx.tcx()).ty;
                    let fn_result_ty = sig.output().skip_binder();
                    let result_cast = self
                        .deps()
                        .require_ref::<CastToEnc<CastTypeImpure>>(CastArgs {
                            expected: expected_ty,
                            actual: fn_result_ty,
                        })
                        .unwrap();
                    if let Some(stmt) = result_cast.apply_cast_if_necessary(self.vcx, dest) {
                        self.stmt(stmt);
                    }
                }

                target
                    .map(|target| {
                        const REAL_TARGET_SUCC_IDX: usize = 0;
                        // Ensure that the terminator succ that we use for the repacks is the correct one
                        assert_eq!(
                            self.current_fpcs.as_ref().unwrap().terminator.succs
                                [REAL_TARGET_SUCC_IDX]
                                .block(),
                            target
                        );
                        let current_fpcs = self.current_fpcs.take().unwrap();
                        let borrows = current_fpcs.statements.last().unwrap().states
                            [EvalStmtPhase::PostMain]
                            .clone();
                        self.pcs_succ(
                            &borrows,
                            &current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX],
                        );
                        self.current_fpcs = Some(current_fpcs);
                        let set_flag = self.set_from_to_flag(location.block, target);
                        self.stmt(set_flag);

                        self.vcx.mk_goto_stmt(
                            self.vcx
                                .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                        )
                    })
                    .unwrap_or_else(|| {
                        // TODO: detect panic causes, adjust message accordingly
                        self.vcx().with_span(span, |vcx| {
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification(
                                    "unreachable statement might be reached",
                                    span.into(),
                                )])
                            });
                            self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                            self.vcx.mk_assume_false_stmt()
                        })
                    })
            }
            mir::TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                unwind,
            } => {
                const REAL_TARGET_SUCC_IDX: usize = 0;
                // Ensure that the terminator succ that we use for the repacks is the correct one
                assert_eq!(
                    &self.current_fpcs.as_ref().unwrap().terminator.succs[REAL_TARGET_SUCC_IDX]
                        .block(),
                    target,
                );
                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows =
                    current_fpcs.statements.last().unwrap().states[EvalStmtPhase::PostMain].clone();
                self.pcs_succ(
                    &borrows,
                    &current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX],
                );
                self.current_fpcs = Some(current_fpcs);

                let e_bool = self
                    .deps
                    .require_ref::<RustTyPredicatesEnc>(self.vcx.tcx().types.bool)
                    .unwrap();
                let enc = self.encode_operand_snap(cond).downcast_ty();
                let enc = (e_bool.generic_predicate.expect_prim().snap_to_prim)(enc);
                let expected = self.vcx.mk_const_expr(vir::ConstData::Bool(*expected));
                let assert = self.vcx.mk_eq_expr(enc, expected);
                let error_msg = match **msg {
                    mir::AssertMessage::BoundsCheck { .. } => "bounds check may fail",
                    mir::AssertMessage::Overflow(..) | mir::AssertMessage::OverflowNeg(..) => {
                        "operation may overflow"
                    }
                    mir::AssertMessage::DivisionByZero(..)
                    | mir::AssertMessage::RemainderByZero(..) => "division by zero may occur",
                    mir::AssertMessage::ResumedAfterReturn(..) => {
                        "execution may continue after return"
                    }
                    mir::AssertMessage::ResumedAfterPanic(..) => {
                        "execution may continue after panic"
                    }
                    mir::AssertMessage::MisalignedPointerDereference { .. } => {
                        "misaligned pointer may be dereferenced"
                    } // mir::AssertMessage::NullPointerDereference => "",
                };
                self.vcx().with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification(error_msg, span.into())])
                    });
                    self.stmt(self.vcx.mk_exhale_stmt(assert));
                });

                let target_bb = self
                    .vcx
                    .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize()));
                let otherwise = match unwind {
                    mir::UnwindAction::Cleanup(bb) => self
                        .vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(bb.as_usize())),
                    _ => todo!(),
                };

                let statements = self.set_from_to_flag(location.block, *target);
                let statements = self.vcx.alloc_slice(&[statements]);

                self.vcx.mk_goto_if_stmt(
                    enc.as_dyn(),
                    self.vcx.alloc_slice(&[self.vcx.mk_goto_if_target(
                        expected.as_dyn(),
                        target_bb,
                        statements,
                    )]),
                    otherwise,
                    &[],
                )
            }
            mir::TerminatorKind::Unreachable => self.vcx().with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::verification(
                        "unreachable statement might be reached",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),

            mir::TerminatorKind::Drop { target, .. } => {
                let set_flag = self.set_from_to_flag(location.block, *target);
                self.stmt(set_flag);
                self.vcx.mk_goto_stmt(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                )
            }

            unsupported_kind => self.vcx.mk_dummy_stmt(vir::vir_format!(
                self.vcx,
                "terminator {unsupported_kind:?}"
            )),
        };
        self.new_after_label(location);
        assert!(self.current_terminator.replace(terminator).is_none());
    }
}
