use pcg::{
    PcgOutput,
    action::{BorrowPcgAction, PcgAction, PcgActions},
    borrow_pcg::{
        action::BorrowPcgActionKind,
        borrow_pcg_edge::BorrowPcgEdge,
        borrow_pcg_expansion::BorrowPcgExpansion,
        edge::{
            abstraction::{AbstractionEdge, FunctionCallOrLoop},
            kind::BorrowPcgEdgeKind,
        },
        state::BorrowsState,
        unblock_graph::BorrowPcgUnblockAction,
    },
    coupling::PcgCoupledEdgeKind,
    free_pcs::RepackOp,
    r#loop::{LoopAnalysis, LoopId, PlaceUsages},
    pcg::{CapabilityKind, EvalStmtPhase, Pcg, PcgNode, PcgSuccessor},
    results::PcgBasicBlock,
    utils::{CompilerCtxt, HasPlace, Place, maybe_old::MaybeLabelledPlace},
};
use prusti_interface::{PrustiError, specs::specifications::SpecQuery};
use prusti_rustc_interface::{
    abi,
    data_structures::fx::FxHashMap,
    middle::{
        mir,
        ty::{self, TyKind},
    },
    span::{Span, def_id::DefId},
};
use prusti_utils::config;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, CompType};

use crate::encoders::{
    self, FunctionCallEnc, TyUseImpureEnc, WandEnc, WandEncTask,
    mir_fn::{CallTaskDescription, RustSignature},
    mir_shared::PureRvalueEnc,
    ty::{
        RustTyDecomposition,
        use_impure::TyUseImpure,
        use_pure::{TyUsePure, TyUsePureEnc},
    },
};

use super::WandEncOutput;

pub struct ImpureEncVisitor<'vir, 'enc, E: TaskEncoder>
where
    'vir: 'enc,
{
    pub vcx: &'vir vir::VirCtxt<'vir>,
    pub deps: &'enc mut TaskEncoderDependencies<'vir, E>,
    pub def_id: DefId,
    pub local_decls: &'enc mir::LocalDecls<'vir>,
    pub fpcs_analysis: PcgOutput<'enc, 'vir>,
    pub local_defs: crate::encoders::MirLocalDefEncOutput<'vir>,
    pub body: &'enc mir::Body<'vir>,

    pub wands: WandEncOutput<'vir>,

    pub tmp_ctr: usize,
    pub label_ctr: usize,
    pub call_labels: FxHashMap<mir::BasicBlock, (&'vir str, &'vir str)>,
    pub from_to_vars: FxHashMap<mir::BasicBlock, Vec<(mir::BasicBlock, vir::LocalDeclBool<'vir>)>>,

    // for the current basic block
    pub current_fpcs: Option<PcgBasicBlock<'enc, 'vir>>,

    pub current_block_label: Option<vir::CfgBlockLabel<'vir>>,
    pub current_stmts: Option<Vec<vir::Stmt<'vir>>>,
    pub current_terminator: Option<vir::TerminatorStmt<'vir>>,

    pub encoded_blocks: Vec<vir::CfgBlock<'vir>>, // TODO: use IndexVec ?
}

/// Represents the translation of a MIR place. If the place crosses a shared
/// reference, then we will no longer have a predicate for the `address` Ref,
/// but we do also have the snapshot available.
pub(crate) struct PlaceExpr<'vir> {
    address: vir::ExprRef<'vir>,
    snap: Option<vir::ExprSnap<'vir>>,
}

impl<'vir> PlaceExpr<'vir> {
    /// Expects the encoded place to not be behind a shared ref
    pub(crate) fn expect_predicate(&self) -> vir::ExprRef<'vir> {
        assert!(self.snap.is_none());
        self.address
    }

    pub(crate) fn map(
        self,
        fa: impl FnOnce(vir::ExprRef<'vir>) -> vir::ExprRef<'vir>,
        fs: impl FnOnce(vir::ExprSnap<'vir>) -> vir::ExprSnap<'vir>,
    ) -> Self {
        PlaceExpr {
            address: fa(self.address),
            snap: self.snap.map(fs),
        }
    }
}

pub(crate) struct EncodePlaceResult<'vir> {
    pub(crate) expr: PlaceExpr<'vir>,
    pub(crate) ty: mir::PlaceTy<'vir>,
}

macro_rules! comment {
    ($self:tt, $($arg:tt)*) => { $self.comment(
        vir::vir_format!($self.vcx, $($arg)*),
    ) };
}

type EncodeResult<'vir, T, E> = Result<T, EncodeFullError<'vir, E>>;

enum EncodeRvalueError<'vir, E: TaskEncoder> {
    UnsupportedRvalue,
    EncoderError(EncodeFullError<'vir, E>),
}

impl<'vir, E: TaskEncoder> From<EncodeFullError<'vir, E>> for EncodeRvalueError<'vir, E> {
    fn from(e: EncodeFullError<'vir, E>) -> Self {
        EncodeRvalueError::EncoderError(e)
    }
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

    fn ty_use_impure(&mut self, ty: ty::Ty<'vir>) -> TyUseImpure<'vir> {
        let ty_task = RustTyDecomposition::from_ty(ty, self.vcx.tcx(), self.def_id);
        self.deps.require_dep::<TyUseImpureEnc>(ty_task).unwrap()
    }

    fn encode_rvalue_snap(
        &mut self,
        rvalue: &mir::Rvalue<'vir>,
        span: Span,
    ) -> Result<vir::ExprSnap<'vir>, EncodeRvalueError<'vir, E>> {
        let rvalue_ty = rvalue.ty(self.local_decls, self.vcx.tcx());
        match rvalue {
            mir::Rvalue::Use(op) => self.encode_operand_snap(op, &()).map_err(Into::into),
            mir::Rvalue::Cast(cast_kind, operand, ty) => {
                let encoded_cast = self.encode_cast_snap(*cast_kind, operand, *ty, &())?;

                self.vcx.with_span(span, |_| {
                    self.vcx
                        .handle_error("exhale.failed:assertion.false", move |_| {
                            Some(vec![PrustiError::verification(
                                "cast may fail: value might not fit into the target type",
                                span.into(),
                            )])
                        });
                    for precondition in encoded_cast.preconditions {
                        self.stmt(self.vcx.mk_exhale_stmt(precondition));
                    }
                });

                Ok(encoded_cast.expr)
            }
            mir::Rvalue::Len(place) => Ok(self.encode_len_snap((*place).into(), &())),

            mir::Rvalue::BinaryOp(op, box (l, r)) => self
                .encode_binop_snap(rvalue_ty, *op, l, r, &())
                .map_err(Into::into),

            mir::Rvalue::UnaryOp(unop, operand) => self
                .encode_unary_op_snap(rvalue_ty, *unop, operand, &())
                .map_err(Into::into),

            mir::Rvalue::Aggregate(
                box kind @ (mir::AggregateKind::Adt(..) | mir::AggregateKind::Tuple),
                fields,
            ) => self
                .encode_aggregate_snap(rvalue_ty, kind, fields, &())
                .map_err(Into::into),

            mir::Rvalue::Discriminant(place) => {
                let e_rvalue_ty = self.ty_use_pure(rvalue_ty);
                let place_ty = place.ty(self.local_decls, self.vcx.tcx());
                let ty = self.ty_use_impure(place_ty.ty);
                let place_expr = self.encode_place(Place::from(*place)).expr;

                Ok(match ty
                    .get_enumlike()
                    .filter(|_| place_ty.variant_index.is_none())
                {
                    Some(el) => {
                        if let Some(snap) = place_expr.snap {
                            let ty = self.ty_use_pure(place_ty.ty).expect_enumlike();
                            ty.snap_to_discr_snap(snap.downcast_ty())
                        } else {
                            let place_expr = place_expr.expect_predicate();
                            self.vcx.mk_unfolding_expr(
                                ty.ref_to_pred_app(place_expr, Some(self.vcx.mk_wildcard())),
                                el.discr_ty()
                                    .ref_to_snap(el.discr(place_expr))
                                    .downcast_ty(),
                            )
                        }
                    }
                    None => {
                        // mir::Rvalue::Discriminant documents "Returns zero for types without discriminant"
                        let zero = self.vcx.mk_uint::<0>();
                        (e_rvalue_ty.expect_primitive().prim_to_snap)(zero.upcast_ty())
                    }
                }
                .upcast_ty())
            }

            mir::Rvalue::Ref(_reg, _kind, place) => {
                Ok(match rvalue_ty.kind() {
                    TyKind::Ref(.., ty::Mutability::Not) => {
                        let (address, snap, _, _) = self.encode_place_with_snap((*place).into());
                        let inner = self.ty_use_pure(rvalue_ty).expect_immref();
                        inner.prim_to_snap(address.expr.address, snap).upcast_ty()
                    }
                    TyKind::Ref(.., ty::Mutability::Mut) => {
                        let e_rvalue_ty = self.ty_use_pure(rvalue_ty);
                        let (place_expr, snap, _, _) =
                            self.encode_place_with_snap(Place::from(*place));

                        // The snapshot of the referenced value should be encoded as a generic `Param`
                        let inner = e_rvalue_ty.expect_mutref();
                        inner
                            .prim_to_snap(place_expr.expr.expect_predicate(), snap)
                            .upcast_ty()
                    }
                    _ => unreachable!(),
                })
            }
            _ => Err(EncodeRvalueError::UnsupportedRvalue),
        }
    }

    /*
    fn project_fields(
        &mut self,
        mut ty_out: crate::encoders::TyImpureRef<'vir>,
        projection: &'vir ty::List<mir::PlaceElem<'vir>>
    ) -> &'vir [&'vir str] {
        let mut ret = vec![];
        for proj in projection {
            match proj {
                mir::ProjectionElem::Field(f, ty) => {
                    let ty_out_struct = ty_out.expect_structlike();
                    let field_ty_out = self.deps.require_ref::<crate::encoders::TyImpureEnc>(
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
                    let field_ty_out = self.deps.require_ref::<crate::encoders::TyImpureEnc>(
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
        state: &Pcg<'_, 'vir>,
        pcs: &'a PcgSuccessor<'_, 'vir>,
    ) -> Vec<vir::Stmt<'vir>> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        self.pcs_succ(state, pcs);
        let new_stmts = self.current_stmts.take().unwrap();
        self.current_stmts = current_stmts;
        new_stmts
    }

    pub(crate) fn block<Err>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<(), Err>,
    ) -> Result<Vec<vir::Stmt<'vir>>, Err> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        f(self)?;
        let new_stmts = self.current_stmts.take().unwrap();
        self.current_stmts = current_stmts;
        Ok(new_stmts)
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
        let PcgNode::Place(base) = base else {
            // Ignore expansions of region projections
            return;
        };
        let (place, old) = match base {
            MaybeLabelledPlace::Current(place) => (place, None),
            MaybeLabelledPlace::Labelled(snap) => {
                // We shouldn't be unfolding old places?
                debug_assert!(!unfold);
                (
                    snap.place(),
                    Some(Self::get_location_label(self.vcx, snap.at())),
                )
            }
        };
        if matches!(
            self.local_decls[place.local].ty.kind(),
            ty::TyKind::Ref(_, _, ty::Mutability::Not)
        ) {
            return; // TODO: does this make sense??? we don't want to unfold because for immut refs we only use snapshot read/writes
        }
        let ref_p = self.encode_place(place);
        let place_ty = ref_p.ty;
        let mut ref_p = ref_p.expr.expect_predicate();
        let data = self.ty_use_impure(place_ty.ty);

        if let Some(label) = old {
            ref_p = self.vcx.mk_old(ref_p, label);
        } else if let Some(label) = label {
            ref_p = self.vcx.mk_local_labelled_old_expr(ref_p, label);
        }
        if unfold {
            for stmt in data.unfold(place_ty.variant_index, ref_p, None) {
                self.stmt(stmt);
            }
        } else {
            for stmt in data.fold(place_ty.variant_index, ref_p, None) {
                self.stmt(stmt);
            }
        }
    }

    fn pcs_handle_edge(
        &mut self,
        borrows_state: &BorrowsState<'_, 'vir>,
        edge: &BorrowPcgEdge<'vir>,
        add: bool,
        label: Option<&'vir str>,
        edge_to_loop: bool,
        to_skip: &mut Vec<mir::BasicBlock>,
    ) -> EncodeResult<'vir, (), E> {
        let conditions = edge.conditions();

        // For each block `b` where the edge is only valid if control flow
        // continues from `b` to a specified subset of its successors, `cond`
        // contains the corresponding VIR expression.
        let cond = conditions
            .all_branch_choices()
            .map(|choices| {
                let successors = choices.successors(self.body);
                let from = choices.from();
                let conj = successors
                    .iter()
                    .map(|to| {
                        let decl = self
                            .from_to_vars
                            .get(&from)
                            .and_then(|tos| tos.iter().find(|(t, _)| t == to))
                            .map(|(_, decl)| *decl);
                        let decl = decl.unwrap_or_else(|| {
                            let name = vir::vir_format!(
                                self.vcx,
                                "_from_bb{}_to_bb{}",
                                from.index(),
                                to.index()
                            );
                            self.vcx.mk_local_decl(name, vir::TYPE_BOOL)
                        });
                        self.vcx.mk_local_ex(decl)
                    })
                    .collect::<Vec<_>>();
                // Control flow must continue from `choices.from()` to any one of the `successors`
                self.vcx.mk_disj(self.vcx.alloc_slice(&conj))
            })
            .collect::<Vec<_>>();
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
        })?;
        if stmts.is_empty()
            || stmts
                .iter()
                .all(|stmt| matches!(stmt.kind, vir::StmtKindData::Comment(_)))
        {
            self.stmts(stmts);
            return Ok(());
        }
        let stmts = self.vcx.alloc_slice(&stmts);
        self.stmt(self.vcx.mk_if_stmt(cond, stmts, &[]));
        Ok(())
    }

    fn pcs_handle_edge_conditionless(
        &mut self,
        borrows_state: &BorrowsState<'_, 'vir>,
        edge: &BorrowPcgEdge<'vir>,
        add: bool,
        label: Option<&'vir str>,
        edge_to_loop: bool,
        to_skip: &mut Vec<mir::BasicBlock>,
    ) -> EncodeResult<'vir, (), E> {
        match edge.kind() {
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                self.pcs_borrow_expansion(expansion.clone(), add, label);
            }
            BorrowPcgEdgeKind::Coupled(PcgCoupledEdgeKind(FunctionCallOrLoop::FunctionCall(
                call_edge,
            ))) => {
                if add {
                    // The wand will be introduced by the method call itself.
                    return Ok(());
                }
                let call = call_edge.metadata();
                // We may be encoding multiple edges as a single wand, skip
                // further edge removals. This is a hack to get around the fact
                // that Viper doesn't support hyperwands.
                if to_skip.contains(&call.location().block) {
                    return Ok(());
                }
                to_skip.push(call.location().block);
                // TODO: this applies *all* the wands for the referenced
                //   function call; instead we should figure out which
                //   wand it is based on the edge info.
                // TODO: closures
                let wands = self
                    .deps
                    .require_dep::<WandEnc>(WandEncTask {
                        data: call.function_data().unwrap(),
                    })
                    .unwrap();
                let bb = &self.body[call.location().block];
                let terminator = bb.terminator.as_ref().unwrap();
                match &terminator.kind {
                    mir::TerminatorKind::Call {
                        args, destination, ..
                    } => {
                        let (_, dest_snap, _, _) =
                            self.encode_place_with_snap((*destination).into());
                        let wand_args =
                            std::iter::once(Ok(dest_snap))
                                .chain(args.iter().map(|operand| {
                                    self.encode_operand_snap_immediate(&operand.node)
                                }))
                                .collect::<Result<Vec<_>, EncodeFullError<'vir, E>>>()?;
                        let (label_pre, label_post) = self.call_labels[&call.location().block];
                        wands.apply_wands(&wand_args, label_pre, label_post, self);
                    }
                    _ => unreachable!(),
                }
            }
            BorrowPcgEdgeKind::Abstraction(at @ AbstractionEdge::Loop(_)) => {
                self.pcs_handle_wand(
                    borrows_state,
                    add,
                    &at.clone().into_singleton_coupled_edge(),
                    label,
                    edge_to_loop,
                );
            }
            other => comment!(self, "(ignoring) {other:?}"),
        }
        Ok(())
    }

    pub(crate) fn pcs_unblock_actions(
        &mut self,
        borrows_state: &BorrowsState<'_, 'vir>,
        actions: &[BorrowPcgUnblockAction<'vir>],
        label: Option<&'vir str>,
    ) -> EncodeResult<'vir, (), E> {
        let mut to_skip = Vec::new();
        for action in actions {
            self.pcs_handle_edge(
                borrows_state,
                action.edge(),
                false,
                label,
                false,
                &mut to_skip,
            )?;
        }
        Ok(())
    }

    fn pcg_actions(
        &mut self,
        pcg: &Pcg<'_, 'vir>,
        actions: &PcgActions<'vir>,
        edge_to_loop: bool,
    ) -> EncodeResult<'vir, (), E> {
        for action in actions.iter() {
            match action {
                PcgAction::Borrow(action) => self.borrow_action(pcg, action, edge_to_loop)?,
                PcgAction::Owned(action) => self.pcg_repack(action.kind()),
            }
        }
        Ok(())
    }
    fn borrow_action(
        &mut self,
        pcg: &Pcg<'_, 'vir>,
        action: &BorrowPcgAction<'vir>,
        edge_to_loop: bool,
    ) -> EncodeResult<'vir, (), E> {
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
            BorrowPcgActionKind::Weaken(weaken)
                if matches!(weaken.from_cap(), CapabilityKind::Exclusive)
                    && matches!(weaken.to_cap(), None | Some(CapabilityKind::Write)) =>
            {
                self.pcg_weaken(weaken.place());
                Ok(())
            }
            //RenamePlace {
            //    old: MaybeLabelledPlace<'tcx>,
            //    new: MaybeLabelledPlace<'tcx>,
            //},
            other => {
                comment!(self, "(ignoring) {other:?}");
                Ok(())
            }
        }
    }

    fn pcg_repack(&mut self, repack_op: &RepackOp<'vir>) {
        comment!(self, "[PCG] {repack_op:?}");
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
                    //assert!(matches!(repack_op, RepackOp::Collapse(..)));
                    if !matches!(repack_op, RepackOp::Collapse(..)) {
                        comment!(self, "expected RepackOp::Collapse but got {repack_op:?}");
                    }
                    return;
                }
                let place_enc = self.encode_place(place);
                let place_ty = place_enc.ty;
                let place_enc = place_enc.expr.expect_predicate();
                let data = self.ty_use_impure(place_ty.ty);
                if matches!(repack_op, pcg::free_pcs::RepackOp::Expand(..)) {
                    for stmt in data.unfold(place_ty.variant_index, place_enc, None) {
                        self.stmt(stmt);
                    }
                } else {
                    for stmt in data.fold(place_ty.variant_index, place_enc, None) {
                        self.stmt(stmt);
                    }
                }
            }
            RepackOp::Weaken(place, CapabilityKind::Exclusive, CapabilityKind::Write) => {
                self.pcg_weaken(*place)
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

    fn pcg_weaken(&mut self, place: Place<'vir>) {
        let place_ty = place.ty(self.pcg_ctxt());
        assert!(place_ty.variant_index.is_none());

        let place_ty_out = self.ty_use_impure(place_ty.ty);

        let place_enc = self.encode_place(place);
        comment!(self, "exhale due to Weaken(E, W)");
        self.stmt(self.vcx.mk_exhale_stmt(place_ty_out.ref_to_pred(
            self.vcx,
            place_enc.expr.expect_predicate(),
            None,
        )));
    }

    fn loop_analysis(&mut self) -> &LoopAnalysis {
        self.fpcs_analysis.analysis().loop_analysis()
    }

    fn loop_place_usages(&mut self, block: mir::BasicBlock) -> Option<PlaceUsages<'vir>> {
        self.fpcs_analysis
            .analysis()
            .loop_place_usages(block)
            .cloned()
    }

    fn loop_head_of(&mut self, block: mir::BasicBlock) -> Option<LoopId> {
        self.loop_analysis().loop_head_of(block)
    }

    fn pcs_succ<'a>(&mut self, pcg_state: &Pcg<'_, 'vir>, succ: &'a PcgSuccessor<'_, 'vir>) {
        let edge_to_loop = self.loop_head_of(succ.block()).is_some();
        self.pcg_actions(pcg_state, succ.actions(), edge_to_loop)
            .unwrap();
    }

    fn encode_operand(
        &mut self,
        operand: &mir::Operand<'vir>,
    ) -> EncodeResult<'vir, vir::ExprRef<'vir>, E> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx());
        let (encode_place_result, ty_out) = match operand {
            &mir::Operand::Move(source) => {
                return Ok(self
                    .encode_place(Place::from(source))
                    .expr
                    .expect_predicate());
            }
            &mir::Operand::Copy(_source) => {
                let ty_out = self.ty_use_impure(ty);
                (self.encode_operand_snap(operand, &())?, ty_out)
            }
            mir::Operand::Constant(box constant) => {
                let ty_out = self.ty_use_impure(ty);
                let constant = self.encode_constant_snap(constant)?;
                (constant.upcast_ty(), ty_out)
            }
        };
        let tmp_exp: vir::ExprRef<'vir> = self.new_tmp(vir::TYPE_REF);
        self.stmt(ty_out.apply_method_assign(self.vcx, tmp_exp, encode_place_result));
        Ok(tmp_exp)
    }

    /// Encodes the snapshot of an operand. This should not be used for encoding
    /// regular mir statements/terminators as it doesn't match the semantics.
    fn encode_operand_snap_immediate(
        &mut self,
        operand: &mir::Operand<'vir>,
    ) -> Result<vir::ExprSnap<'vir>, EncodeFullError<'vir, E>> {
        match operand {
            &mir::Operand::Move(source) | &mir::Operand::Copy(source) => {
                Ok(self.encode_place_with_snap(Place::from(source)).1)
            }
            mir::Operand::Constant(box constant) => {
                Ok(self.encode_constant_snap(constant)?.upcast_ty())
            }
        }
    }

    pub(crate) fn encode_place(&mut self, place: Place<'vir>) -> EncodePlaceResult<'vir> {
        let mut place_ty = mir::PlaceTy::from_ty(self.local_decls[place.local].ty);
        let mut encoded_place = mir::Place::from(place.local);
        let mut result = PlaceExpr {
            address: self.local_defs[place.local].local_ex,
            snap: None,
        };
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

    pub(crate) fn encode_place_with_snap(
        &mut self,
        place: Place<'vir>,
    ) -> (
        EncodePlaceResult<'vir>,
        vir::ExprSnap<'vir>,
        mir::PlaceTy<'vir>,
        TyUseImpure<'vir>,
    ) {
        let ty = (*place).ty(self.local_decls, self.vcx.tcx());
        assert!(ty.variant_index.is_none());

        let ty_out = self.ty_use_impure(ty.ty);
        let result = self.encode_place(place);
        let snap = result
            .expr
            .snap
            .unwrap_or_else(|| ty_out.ref_to_snap(result.expr.address));
        (result, snap, ty, ty_out)
    }

    fn encode_place_element(
        &mut self,
        place_ty: mir::PlaceTy<'vir>,
        elem: mir::PlaceElem<'vir>,
        expr: PlaceExpr<'vir>,
    ) -> PlaceExpr<'vir> {
        match elem {
            mir::ProjectionElem::Field(field_idx, _) => {
                let e_ty = self.ty_use_impure(place_ty.ty);
                let field_access = e_ty.expect_variant_opt(place_ty.variant_index);
                expr.map(
                    |r| field_access[field_idx].field_ref(r),
                    |snap| {
                        let e_ty = self.ty_use_pure(place_ty.ty);
                        let field_access = e_ty.expect_variant_opt(place_ty.variant_index);
                        field_access[field_idx].read(snap.downcast_ty())
                    },
                )
            }
            // TODO: should all variants start at the same `Ref`?
            mir::ProjectionElem::Downcast(..) => expr,
            mir::ProjectionElem::Deref => {
                assert!(place_ty.variant_index.is_none());
                let e_ty = self.ty_use_impure(place_ty.ty);
                match place_ty.ty.kind() {
                    ty::TyKind::Adt(adt, _) if adt.is_box() => {
                        let field_access = e_ty.expect_variant_opt(None);
                        expr.map(
                            // TODO: this is unsound: a Box should be modelled
                            // with a Ref field rather than a field_access
                            // function.
                            |r| field_access[abi::FieldIdx::ZERO].field_ref(r),
                            |snap| {
                                let e_ty = self.ty_use_pure(place_ty.ty);
                                let field_access = e_ty.expect_variant_opt(None);
                                field_access[abi::FieldIdx::ZERO].read(snap.downcast_ty())
                            },
                        )
                    }
                    ty::TyKind::Ref(_, _, ty::Mutability::Not) => {
                        let snap = expr
                            .snap
                            .unwrap_or_else(|| e_ty.ref_to_snap(expr.address))
                            .downcast_ty();
                        let p_ty = self.ty_use_pure(place_ty.ty).expect_immref();
                        PlaceExpr {
                            address: p_ty.deref_access(snap),
                            snap: Some(p_ty.value_access(snap)),
                        }
                    }
                    ty::TyKind::Ref(_, _, ty::Mutability::Mut) => {
                        if let Some(snap) = expr.snap {
                            let snap = snap.downcast_ty();
                            let p_ty = self.ty_use_pure(place_ty.ty).expect_mutref();
                            PlaceExpr {
                                address: p_ty.deref_access(snap),
                                snap: Some(p_ty.value_access(snap)),
                            }
                        } else {
                            PlaceExpr {
                                address: e_ty.expect_mutref().deref(expr.address),
                                snap: None,
                            }
                        }
                    }
                    _ => unreachable!(),
                }
            }
            _ => todo!("Unsupported ProjectionElem {:?}", elem),
        }
    }

    fn new_tmp<T: CompType>(&mut self, ty: vir::Type<'vir, T>) -> vir::Expr<'vir, T> {
        let name = vir::vir_format!(self.vcx, "_tmp{}", self.tmp_ctr);
        let local = vir::vir_local_decl! { self.vcx; [name] : [ty] };
        self.tmp_ctr += 1;
        self.stmt(self.vcx.mk_local_decl_stmt(local, None));
        self.vcx.mk_local_ex(local)
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
        let decl = self.vcx.mk_local_decl(name, vir::TYPE_BOOL);
        let tos = self.from_to_vars.entry(from).or_default();
        debug_assert!(!tos.contains(&(to, decl)));
        tos.push((to, decl));
        let local = self.vcx.mk_local_ex(decl);
        self.vcx
            .mk_pure_assign_stmt(local, self.vcx.mk_bool::<true>())
    }
}

impl<'vir, 'enc, E: TaskEncoder> PureRvalueEnc<'vir> for ImpureEncVisitor<'vir, 'enc, E> {
    type Encoder = E;
    type EncodePlaceCtxt = ();
    type ExprCurr = ();
    type ExprNext = !;
    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir, Self::Encoder> {
        self.deps
    }

    fn vcx(&self) -> &'vir vir::VirCtxt<'vir> {
        self.vcx
    }

    fn body(&self) -> &mir::Body<'vir> {
        self.body
    }

    fn ty_use_pure(&mut self, ty: ty::Ty<'vir>) -> TyUsePure<'vir> {
        let ty_task = RustTyDecomposition::from_ty(ty, self.vcx.tcx(), self.def_id);
        self.deps.require_dep::<TyUsePureEnc>(ty_task).unwrap()
    }

    fn encode_operand_snap(
        &mut self,
        operand: &mir::Operand<'vir>,
        _ctxt: &Self::EncodePlaceCtxt,
    ) -> Result<vir::ExprSnap<'vir>, EncodeFullError<'vir, E>> {
        match operand {
            &mir::Operand::Move(source) => {
                let (result, snap_val, _, ty_out) =
                    self.encode_place_with_snap(Place::from(source));

                let tmp_exp = self.new_tmp(ty_out.snapshot());
                self.stmt(self.vcx.mk_pure_assign_stmt(tmp_exp, snap_val));
                self.stmt(self.vcx.mk_exhale_stmt(ty_out.ref_to_pred(
                    self.vcx,
                    result.expr.expect_predicate(),
                    None,
                )));
                Ok(tmp_exp)
            }
            &mir::Operand::Copy(place) => Ok(self.encode_place_with_snap(place.into()).1),
            mir::Operand::Constant(box constant) => {
                Ok(self.encode_constant_snap(constant)?.upcast_ty())
            }
        }
    }

    fn encode_place_snap(
        &mut self,
        place: Place<'vir>,
        _ctxt: &Self::EncodePlaceCtxt,
    ) -> vir::ExprGenSnap<'vir, Self::ExprCurr, Self::ExprNext> {
        self.encode_place_with_snap(place).1
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
                        .mk_dummy_stmt(vir::vir_format!(self.vcx, "cleanup block")),
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
            .loop_place_usages(block)
            .map(|place_usages| self.get_loop_inv(&cfpcs, &place_usages, self.pcg_ctxt()))
            .unwrap_or_default();

        self.current_fpcs = Some(cfpcs);

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
        self.vcx.with_span(statement.source_info.span, |_vcx| {
            if self.deps.check_cycle().is_err() {
                return;
            }

            comment!(self, "[MIR] {location:?}: {statement:?}");

            let current_fpcs = self.current_fpcs.take().unwrap();
            let cfpcs = &current_fpcs.statements[location.statement_index];
            for phase in EvalStmtPhase::phases() {
                self.pcg_actions(&cfpcs.states[phase], cfpcs.actions(phase), false).unwrap();
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

            let span = statement.source_info.span;

            match &statement.kind {
                mir::StatementKind::Assign(box (dest, rvalue)) => {
                    // What are we assigning to?
                    let proj_enc = self
                        .encode_place(Place::from(*dest))
                        .expr
                        .expect_predicate();

                    // The snapshot of the value that we are assigning.
                    let rval_enc = self.encode_rvalue_snap(rvalue, span);

                    match rval_enc {
                        Ok(rval_enc) => {
                            let dest_ty = dest.ty(self.local_decls, self.vcx.tcx());
                            assert!(dest_ty.variant_index.is_none());
                            let dest_ty_out = self.ty_use_impure(dest_ty.ty);
                            let method_assign_app =
                                dest_ty_out.apply_method_assign(self.vcx, proj_enc, rval_enc);
                                self.stmt(method_assign_app);
                        }
                        Err(_) => {
                            self.vcx.with_span(span, |vcx| {
                                let error_msg = format!("unsupported rvalue {rvalue:?} might be reached");
                                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                    Some(vec![PrustiError::verification(&error_msg, span.into())])
                                });
                                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                            });
                        }
                    }
                }

                // no-ops
                mir::StatementKind::StorageLive(..)
                | mir::StatementKind::StorageDead(..)
                | mir::StatementKind::FakeRead(_)
                | mir::StatementKind::PlaceMention(_)
                | mir::StatementKind::AscribeUserType(..)
                | mir::StatementKind::Coverage(_)
                | mir::StatementKind::ConstEvalCounter
                | mir::StatementKind::Nop
                | mir::StatementKind::BackwardIncompatibleDropHint { .. } => {}

                mir::StatementKind::Intrinsic(intrinsic_kind) => {
                    let intrinsic_kind = intrinsic_kind.clone();
                    self.vcx.with_span(span, |vcx| {
                        vcx.handle_error("exhale.failed:assertion.false", move |_| {
                            Some(vec![PrustiError::verification(
                                format!("unsupported intrinsic statement {intrinsic_kind:?} might be reached"),
                                span.into(),
                            )])
                        });
                        self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                    });
                }

                mir::StatementKind::Retag(..)
                | mir::StatementKind::SetDiscriminant { .. }
                | mir::StatementKind::Deinit(..) => unreachable!(
                    "the statement kind {:?} is not allowed in the MIR analysis phase",
                    statement.kind
                ),
            }
            self.new_after_label(location);
        });
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
            self.pcg_actions(&cfpcs.states[phase], cfpcs.actions(phase), false)
                .unwrap();
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
                let discr_ty = self.ty_use_pure(discr_ty_rs).expect_primitive();

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

                let discr_ex = (discr_ty.expect_native().snap_to_prim)(
                    self.encode_operand_snap(discr, &()).unwrap().downcast_ty(),
                );
                self.vcx.mk_goto_if_stmt(
                    discr_ex.as_dyn(), // self.vcx.mk_local_ex(discr_name),
                    goto_targets,
                    goto_otherwise,
                    self.vcx.alloc_slice(&otherwise_stmts),
                )
            }
            mir::TerminatorKind::Return => {
                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows = current_fpcs.statements.last().unwrap().states
                    [EvalStmtPhase::PostMain]
                    .borrow_pcg();
                let wand_packages = self.package_wands(borrows).unwrap();
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
                        self.current_block_label
                            .replace(
                                self.vcx.alloc(vir::CfgBlockLabelData::BasicBlockTerminator(
                                    current_block,
                                )),
                            )
                            .unwrap(),
                        &[],
                        self.vcx
                            .alloc_slice(&self.current_stmts.replace(Vec::new()).unwrap()),
                        self.vcx
                            .mk_goto_stmt(self.vcx.alloc(
                                vir::CfgBlockLabelData::BasicBlockTerminator(current_block),
                            )),
                    ),
                );

                let func_ty = func.ty(self.body, self.vcx.tcx());
                let (func_def_id, caller_substs) =
                    RustSignature::get_def_id_and_caller_substs(func_ty);
                let is_pure = crate::encoders::with_proc_spec(
                    SpecQuery::GetProcKind(
                        func_def_id,
                        ty::List::identity_for_item(self.vcx.tcx(), func_def_id),
                    ),
                    |spec| spec.kind.is_pure().unwrap_or_default(),
                )
                .unwrap_or_default();

                let dest = self
                    .encode_place(Place::from(*destination))
                    .expr
                    .expect_predicate();
                if is_pure {
                    let pure_func = self
                        .deps
                        .require_dep::<FunctionCallEnc>(CallTaskDescription::new(
                            self.def_id,
                            caller_substs,
                            func_def_id,
                        ))
                        .unwrap();
                    let snap_args = args
                        .iter()
                        .map(|arg| {
                            self.vcx.with_span(arg.span, |_| {
                                self.encode_operand_snap(&arg.node, &()).unwrap()
                            })
                        })
                        .collect::<Vec<_>>();
                    let pure_func_app = pure_func.call(snap_args);

                    let return_ty = destination.ty(self.local_decls, self.vcx.tcx()).ty;
                    let assign_stmt = self.ty_use_impure(return_ty).apply_method_assign(
                        self.vcx,
                        dest,
                        pure_func_app,
                    );

                    self.stmt(assign_stmt);
                } else {
                    vir::with_vcx(|vcx| {
                        vcx.with_span(terminator.source_info.span, |vcx| {
                            let Ok(func_out) = self.deps.require_dep::<encoders::MethodCallEnc>(
                                CallTaskDescription::new(self.def_id, caller_substs, func_def_id),
                            ) else {
                                self.current_terminator = Some(
                                    self.vcx
                                        .mk_dummy_stmt(vir::vir_format!(self.vcx, "recursion",)),
                                );
                                return;
                            };

                            let method_in = args
                                .iter()
                                .map(|arg| self.encode_operand(&arg.node).unwrap())
                                .collect::<Vec<_>>();

                            let call = func_out.call(method_in, dest);

                            let label_pre = self.new_label("pre");
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
                            self.stmts(call);
                            let label_post = self.new_label("post");
                            self.call_labels
                                .insert(location.block, (label_pre, label_post));
                        })
                    });
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
                        self.vcx.with_span(span, |vcx| {
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
            // If we are not checking for overflows, encode an overflow-checking
            // assertion as a goto.
            mir::TerminatorKind::Assert { msg, target, .. }
                if !config::check_overflows()
                    && matches!(
                        **msg,
                        mir::AssertMessage::Overflow(..) | mir::AssertMessage::OverflowNeg(..)
                    ) =>
            {
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
            mir::TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                ..
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

                let e_bool = self.ty_use_pure(self.vcx.tcx().types.bool);
                let enc = self.encode_operand_snap(cond, &()).unwrap().downcast_ty();
                let enc = (e_bool.expect_native().snap_to_prim)(enc);
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
                    }
                    mir::AssertKind::ResumedAfterDrop(..) => "execution may continue after drop",
                    mir::AssertKind::NullPointerDereference => "null pointer may be dereferenced",
                    mir::AssertKind::InvalidEnumConstruction(..) => {
                        "invalid enum construction may occur"
                    }
                };
                self.vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification(error_msg, span.into())])
                    });
                    self.stmt(self.vcx.mk_exhale_stmt(assert));
                });
                let set_flag = self.set_from_to_flag(location.block, *target);
                self.stmt(set_flag);
                let target_bb = self
                    .vcx
                    .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize()));
                self.vcx.mk_goto_stmt(target_bb)
            }
            mir::TerminatorKind::Unreachable => self.vcx.with_span(span, |vcx| {
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

            mir::TerminatorKind::UnwindResume | mir::TerminatorKind::UnwindTerminate(..) => {
                self.vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::unsupported(
                            "unwind paths are not supported",
                            span.into(),
                        )])
                    });
                    self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                    self.vcx.mk_assume_false_stmt()
                })
            }

            mir::TerminatorKind::TailCall { .. } => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::unsupported(
                        "tail calls are not supported",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),
            mir::TerminatorKind::Yield { .. } => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::unsupported(
                        "yield statements are not supported",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),
            mir::TerminatorKind::CoroutineDrop => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::unsupported(
                        "coroutines are not supported",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),
            mir::TerminatorKind::InlineAsm { .. } => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::unsupported(
                        "inline assembly is not supported",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),
        };
        self.new_after_label(location);
        assert!(self.current_terminator.replace(terminator).is_none());
    }
}
