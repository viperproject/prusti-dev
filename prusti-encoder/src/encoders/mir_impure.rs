use itertools::Itertools;
use pcg::{
    PcgOutput,
    action::{BorrowPcgAction, PcgAction, PcgActions},
    borrow_pcg::{
        action::BorrowPcgActionKind,
        borrow_pcg_edge::BorrowPcgEdge,
        borrow_pcg_expansion::BorrowPcgExpansion,
        edge::{
            abstraction::{AbstractionEdge, FunctionCallOrLoop},
            borrow_flow::BorrowFlowEdgeKind,
            kind::BorrowPcgEdgeKind,
        },
        region_projection::PlaceOrConst,
        state::BorrowsState,
        unblock_graph::BorrowPcgUnblockAction,
    },
    coupling::PcgCoupledEdgeKind,
    free_pcs::{RepackGuide, RepackOp},
    r#loop::{LoopAnalysis, LoopId},
    pcg::{CapabilityKind, EvalStmtPhase, Pcg, PcgNode, PcgSuccessor},
    results::{PcgBasicBlock, PcgLocation},
    utils::{
        CompilerCtxt, HasPlace, Place, SnapshotLocation, display::DisplayWithCtxt,
        maybe_old::MaybeLabelledPlace,
    },
};
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    abi,
    data_structures::graph::Successors,
    index::Idx,
    middle::{
        mir,
        ty::{self, TyKind},
    },
    span::{Span, def_id::DefId, source_map::Spanned},
};
use prusti_utils::config;
use rustc_hash::{FxHashMap, FxHashSet};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, CompType, LocalDeclData};

use crate::encoders::{
    self, FunctionCallEnc, MirBuiltinUseCastEnc, MirBuiltinUseCastTask, MirPureEnc, MirPureEncTask,
    PrustiBuiltin, PureKind, TyUseImpureEnc, WandEnc, WandEncTask,
    mir_fn::{CallTaskDescription, RustSignature, SpecBlockKind, SpecBlocks},
    mir_shared::{PureRvalueEnc, RustcIntrinsic},
    ty::{
        RustTyDecomposition,
        generics::{GArgs, GParams},
        use_impure::TyUseImpure,
        use_pure::{TyUsePure, TyUsePureEnc},
    },
};

use super::WandEncOutput;

#[derive(Clone, Copy)]
struct FromToVar<'vir> {
    decl: vir::LocalDeclBool<'vir>,
    expr: vir::ExprBool<'vir>,
}

impl<'vir> FromToVar<'vir> {
    fn new(vcx: &'vir vir::VirCtxt<'vir>, from: mir::BasicBlock, to: mir::BasicBlock) -> Self {
        let decl = vcx.mk_local_decl(
            vir::vir_format!(vcx, "_from_bb{}_to_bb{}", from.index(), to.index()),
            vir::TYPE_BOOL,
        );
        let expr = vcx.mk_local_ex(decl);
        Self { decl, expr }
    }
}

#[derive(Default)]
pub(crate) struct FromToVars<'vir>(FxHashMap<(mir::BasicBlock, mir::BasicBlock), FromToVar<'vir>>);

impl<'vir> FromToVars<'vir> {
    pub(crate) fn decls(&self) -> impl Iterator<Item = &'vir LocalDeclData<'vir, vir::Bool>> {
        self.0.values().map(|v| v.decl)
    }

    fn set_from_to_flag_stmt(
        &mut self,
        vcx: &'vir vir::VirCtxt<'vir>,
        from: mir::BasicBlock,
        to: mir::BasicBlock,
    ) -> vir::Stmt<'vir> {
        let var = self.get_or_create(vcx, from, to);
        vcx.mk_pure_assign_stmt(var.expr, vcx.mk_bool::<true>())
    }

    fn get_or_create(
        &mut self,
        vcx: &'vir vir::VirCtxt<'vir>,
        from: mir::BasicBlock,
        to: mir::BasicBlock,
    ) -> FromToVar<'vir> {
        *self
            .0
            .entry((from, to))
            .or_insert_with(|| FromToVar::new(vcx, from, to))
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum EdgeAction {
    Add,
    Remove,
}

impl EdgeAction {
    pub(crate) fn is_add(self) -> bool {
        matches!(self, EdgeAction::Add)
    }
    pub(crate) fn is_remove(self) -> bool {
        matches!(self, EdgeAction::Remove)
    }
}
pub(crate) enum FoldOrUnfold {
    Fold,
    Unfold,
}

impl FoldOrUnfold {
    pub(crate) fn for_action(action: EdgeAction) -> Self {
        match action {
            EdgeAction::Add => FoldOrUnfold::Unfold,
            EdgeAction::Remove => FoldOrUnfold::Fold,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum LocationLabelPrefix {
    Before,
    After,
    BeforeRefReassignment,
}

impl LocationLabelPrefix {
    pub(crate) fn to_str(self) -> &'static str {
        match self {
            LocationLabelPrefix::Before => "before",
            LocationLabelPrefix::After => "after",
            LocationLabelPrefix::BeforeRefReassignment => "before_ref_reassignment",
        }
    }
}

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
    pub spec_blocks: SpecBlocks,
    pub body: &'enc mir::Body<'vir>,

    pub wands: WandEncOutput<'vir>,

    pub tmp_ctr: usize,
    pub label_ctr: usize,
    pub call_labels: FxHashMap<mir::BasicBlock, (&'vir str, &'vir str)>,
    /// Blocks whose call terminator was not encoded as an impure method call
    /// (pure functions, intrinsics, `prusti_contracts` builtins) and thus
    /// created no wand to apply on expiry.
    pub wandless_calls: FxHashSet<mir::BasicBlock>,
    pub from_to_vars: FromToVars<'vir>,

    // for the current basic block
    pub current_fpcs: Option<PcgBasicBlock<'enc, 'vir>>,
    pub current_block: Option<mir::BasicBlock>,
    pub current_block_pres: Option<Vec<usize>>,
    pub current_block_succs: Option<FxHashMap<mir::BasicBlock, vir::CfgBlockLabel<'vir>>>,
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
    metadata: Option<vir::ExprSnap<'vir>>,
    snap: Option<vir::ExprSnap<'vir>>,
}

impl<'vir> PlaceExpr<'vir> {
    /// Expects the encoded place to not be behind a shared ref
    pub(crate) fn expect_predicate(&self) -> vir::ExprRef<'vir> {
        assert!(self.snap.is_none());
        self.address
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

/// Snapshots of the current statement's operands, captured between the
/// `PreOperands` and `PostOperands` repacks by
/// [ImpureEncVisitor::capture_operand_snaps] and passed (as the
/// [PureRvalueEnc::EncodePlaceCtxt]) only to the encoding of the statement's
/// effect; all other operand reads (terminators, repack guides) pass `None`.
type OperandSnaps<'vir> = Option<FxHashMap<mir::Place<'vir>, vir::ExprSnap<'vir>>>;

struct EncodedRvalue<'vir> {
    /// A snapshot of the rvalue. This snapshot is guaranteed to be well-formed
    /// in the state *before* the Rvalue has been assigned to a place. For
    /// example, in the statement `let rx = &mut x`, the snapshot encoding of
    /// `&mut x` relies on capabilities to `x` as they are *before* the
    /// assignment occurs. This is because the encoding of the assignment itself
    /// requires a snapshot of `&mut x`, and the snapshot constructor for
    /// &mut expects a snapshot of the borrowed place which can only be created
    /// when the capabilities are in the pre-assign state.
    expr: vir::ExprSnap<'vir>,

    /// Additional statements necessary to obtain the predicate for the assigned
    /// place of this Rvalue *after* the assignment. Such folds are necessary if
    /// make_generic / make_concrete type casts are necessary to move the capabilities
    /// from the state before the assignment to the predicate of the assigned place.
    ///
    /// For example, for the statement `let rx: &mut u32 = &mut x`, this should
    /// be called with the place corresponding to `rx`, and it will fold the
    /// type predicate for `rx` (in this case, this will make the `u32`
    /// permission held conceptually in *rx generic by calling
    /// `make_generic_u32(*rx)`
    ///
    /// Note that after executing these statements, the snapshot in `expr` is
    /// no-longer well-formed.
    post_assign_folds: Option<Box<dyn FnOnce(vir::ExprRef<'vir>) -> Vec<vir::Stmt<'vir>> + 'vir>>,
}

impl<'vir> EncodedRvalue<'vir> {
    fn post_fold_stmts(self, lhs_place: vir::ExprRef<'vir>) -> Vec<vir::Stmt<'vir>> {
        match self.post_assign_folds {
            Some(f) => f(lhs_place),
            None => Vec::new(),
        }
    }
}

impl<'vir> From<vir::ExprSnap<'vir>> for EncodedRvalue<'vir> {
    fn from(expr: vir::ExprSnap<'vir>) -> Self {
        Self {
            expr,
            post_assign_folds: None,
        }
    }
}

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
        let ty_task = RustTyDecomposition::from_ty(ty, self.def_id);
        self.deps.require_dep::<TyUseImpureEnc>(ty_task).unwrap()
    }

    fn encode_rvalue(
        &mut self,
        rvalue: &mir::Rvalue<'vir>,
        span: Span,
        operand_snaps: &OperandSnaps<'vir>,
    ) -> Result<EncodedRvalue<'vir>, EncodeRvalueError<'vir, E>> {
        let rvalue_ty = rvalue.ty(self.local_decls, self.vcx.tcx());
        match rvalue {
            mir::Rvalue::Use(op) => Ok(self
                .encode_operand_snap(op, operand_snaps)
                .map_err(EncodeRvalueError::from)?
                .into()),
            mir::Rvalue::Cast(cast_kind, operand, ty) => {
                assert_eq!(*ty, rvalue_ty);
                let (stmt, cast) = self
                    .encode_cast_snap(rvalue_ty, *cast_kind, operand, operand_snaps)
                    .map_err(EncodeRvalueError::from)?;
                self.stmts(stmt);
                Ok(cast.into())
            }
            mir::Rvalue::Len(place) => {
                Ok(self.encode_len_snap((*place).into(), operand_snaps)?.into())
            }

            mir::Rvalue::BinaryOp(op, box (l, r)) => Ok(self
                .encode_binop_snap(rvalue_ty, *op, l, r, operand_snaps, span)
                .map_err(EncodeRvalueError::from)?
                .into()),

            mir::Rvalue::UnaryOp(unop, operand) => Ok(self
                .encode_unary_op_snap(rvalue_ty, *unop, operand, operand_snaps)
                .map_err(EncodeRvalueError::from)?
                .into()),

            mir::Rvalue::Aggregate(box _kind @ mir::AggregateKind::Array(..), elements) => {
                let e_rvalue_ty = self.ty_use_pure(rvalue_ty);
                let al = e_rvalue_ty.expect_array();
                let tmp_exp: vir::ExprCSnap<'vir> =
                    self.new_tmp(e_rvalue_ty.snapshot.downcast_ty());
                for (idx, element) in elements.iter().enumerate() {
                    let element_snap = self.encode_operand_snap(element, operand_snaps)?;
                    self.stmt(
                        self.vcx.mk_inhale_stmt(
                            self.vcx.mk_eq_expr(
                                al.index(
                                    tmp_exp,
                                    self.vcx
                                        .mk_const_expr(vir::ConstData::Int(idx as u128))
                                        .downcast_ty(),
                                ),
                                element_snap,
                            ),
                        ),
                    );
                }
                Ok(tmp_exp.upcast_ty().into())
            }

            mir::Rvalue::Aggregate(
                box kind @ (mir::AggregateKind::Adt(..)
                | mir::AggregateKind::Tuple
                | mir::AggregateKind::Closure(..)),
                fields,
            ) => Ok(self
                .encode_aggregate_snap(rvalue_ty, kind, fields, operand_snaps)
                .map_err(EncodeRvalueError::from)?
                .into()),

            mir::Rvalue::Repeat(operand, _len) => {
                let e_rvalue_ty = self.ty_use_pure(rvalue_ty);
                let al = e_rvalue_ty.expect_array();
                let tmp_exp: vir::ExprCSnap<'vir> =
                    self.new_tmp(e_rvalue_ty.snapshot.downcast_ty());
                let operand_snap = self.encode_operand_snap(operand, operand_snaps)?;
                self.stmt(self.vcx.mk_inhale_stmt(vir::expr! {
                    forall idx: Int :: {[al.index(tmp_exp, idx)]}
                        ([al.index(tmp_exp, idx)]) == ([operand_snap])
                }));
                Ok(tmp_exp.upcast_ty().into())
            }

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
                        e_rvalue_ty
                            .expect_primitive()
                            .prim_to_snap(zero.upcast_ty())
                    }
                }
                .upcast_ty()
                .into())
            }

            mir::Rvalue::Ref(_reg, _kind, place) => Ok(match rvalue_ty.kind() {
                TyKind::Ref(.., ty::Mutability::Not) => {
                    let (address, snap, _, _) = self.encode_place_with_snap((*place).into());
                    let metadata = address.expr.metadata;
                    let metadata =
                        metadata.unwrap_or_else(|| self.expect_thin_ptr_metadata(rvalue_ty));
                    let inner = self.ty_use_pure(rvalue_ty).expect_immref();
                    inner
                        .prim_to_snap(address.expr.address, metadata, snap)
                        .upcast_ty()
                        .into()
                }
                TyKind::Ref(.., ty::Mutability::Mut) => {
                    let p_rvalue_ty = self.ty_use_impure(rvalue_ty);
                    let place_expr = self.encode_place(Place::from(*place));

                    let metadata = place_expr.expr.metadata;
                    let metadata =
                        metadata.unwrap_or_else(|| self.expect_thin_ptr_metadata(rvalue_ty));
                    let inner = p_rvalue_ty.expect_mutref();
                    let place_ref = place_expr.expr.expect_predicate();
                    EncodedRvalue {
                        expr: inner.prim_to_snap_assign(place_ref, metadata).upcast_ty(),
                        post_assign_folds: Some(Box::new(move |lhs_place| {
                            p_rvalue_ty.fold(None, lhs_place, None, None, None)
                        })),
                    }
                }
                _ => unreachable!(),
            }),

            mir::Rvalue::RawPtr(_, place) => {
                let place_expr = self.encode_place(Place::from(*place));
                let metadata = place_expr.expr.metadata;
                let metadata = metadata.unwrap_or_else(|| self.expect_thin_ptr_metadata(rvalue_ty));
                let raw = self.ty_use_pure(rvalue_ty).expect_raw();
                Ok(raw
                    .prim_to_snap(place_expr.expr.address, metadata)
                    .upcast_ty()
                    .into())
            }

            _ => Err(EncodeRvalueError::UnsupportedRvalue),
        }
    }

    /// Do the same as [self.pcs_succ] but instead of adding the statements to [self.current_stmts] return them instead.
    /// TODO: clean this up
    fn collect_pcs_succ<'a>(
        &mut self,
        cfpcs: &PcgLocation<'_, 'vir>,
        pcs: &'a PcgSuccessor<'_, 'vir>,
    ) -> Result<Vec<vir::Stmt<'vir>>, EncodeFullError<'vir, E>> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        let res = self.pcs_succ(cfpcs, pcs);
        let new_stmts = self.current_stmts.take().unwrap();
        self.current_stmts = current_stmts;
        res.map(|()| new_stmts)
    }

    /// Emit the repacks of the terminator edge to `target` ([Self::pcs_succ]).
    /// The succ is found by block: the target is usually the terminator's
    /// only non-unwind successor, but for a ghost switch the (second)
    /// `ghost_erased` successor is skipped.
    fn pcs_succ_to(&mut self, target: mir::BasicBlock) -> Result<(), EncodeFullError<'vir, E>> {
        let current_fpcs = self.current_fpcs.take().unwrap();
        let cfpcs = current_fpcs.statements.last().unwrap();
        let succ = current_fpcs
            .terminator
            .succs
            .iter()
            .find(|succ| succ.block() == target)
            .unwrap();
        let res = self.pcs_succ(cfpcs, succ);
        self.current_fpcs = Some(current_fpcs);
        res
    }

    /// [Self::collect_pcs_succ] for the `idx`-th successor: a `SwitchInt`
    /// edge, identified by index since several values may share a target.
    fn collect_pcs_succ_at(
        &mut self,
        idx: usize,
        target: mir::BasicBlock,
    ) -> Result<Vec<vir::Stmt<'vir>>, EncodeFullError<'vir, E>> {
        let current_fpcs = self.current_fpcs.take().unwrap();
        let cfpcs = current_fpcs.statements.last().unwrap();
        let succ = &current_fpcs.terminator.succs[idx];
        assert_eq!(succ.block(), target);
        let res = self.collect_pcs_succ(cfpcs, succ);
        self.current_fpcs = Some(current_fpcs);
        res
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

    pub(crate) fn unfold(&mut self, base: MaybeLabelledPlace<'vir>, label: Option<&'vir str>) {
        self.fold_or_unfold(base, FoldOrUnfold::Unfold, None, label);
    }

    pub(crate) fn fold_or_unfold(
        &mut self,
        base: MaybeLabelledPlace<'vir>,
        fold_or_unfold: FoldOrUnfold,
        expansion: Option<&BorrowPcgExpansion>,
        label: Option<&'vir str>,
    ) {
        let place = base.place();
        let label = if let MaybeLabelledPlace::Labelled(snap) = base {
            Some(self.get_location_label(snap.at()))
        } else {
            label.map(vir::OldLabel::Label)
        };

        // We don't want to unfold because for immutable refs we only use snapshot read/writes
        if place.is_shared_ref(self.pcg_ctxt()) || place.projects_shared_ref(self.pcg_ctxt()) {
            return;
        }

        let ref_p = self.encode_place(place);

        let place_ty = ref_p.ty;
        let ref_p = self
            .vcx
            .maybe_apply_label(ref_p.expr.expect_predicate(), label);
        let data = self.ty_use_impure(place_ty.ty);

        // TODO: use `guide` from `BorrowPcgExpansion`
        let index = expansion.and_then(|expansion| {
            match expansion.expansion()[0].place().projection.last() {
                Some(&mir::ProjectionElem::Index(index_local)) => {
                    let index = self
                        .encode_operand_snap(&mir::Operand::Copy(index_local.into()), &None)
                        .unwrap();
                    let usize_ty_out = self.ty_use_pure(self.vcx.tcx().types.usize);
                    Some(
                        usize_ty_out
                            .expect_primitive()
                            .snap_to_prim(index.downcast_ty())
                            .downcast_ty(),
                    )
                }
                _ => None,
            }
        });

        let stmts = match fold_or_unfold {
            FoldOrUnfold::Unfold => data.unfold(place_ty.variant_index, ref_p, index, None, label),
            FoldOrUnfold::Fold => data.fold(place_ty.variant_index, ref_p, index, None, label),
        };
        self.stmts(stmts);
    }

    fn pcs_handle_edge(
        &mut self,
        borrows_state: &BorrowsState<'_, 'vir>,
        edge: &BorrowPcgEdge<'vir>,
        edge_action: EdgeAction,
        label: Option<&'vir str>,
        edge_to_loop: bool,
        to_skip: &mut Vec<mir::BasicBlock>,
    ) -> EncodeResult<'vir, (), E> {
        let conditions = edge.conditions();

        // For each block `b` where the edge is only valid if control flow
        // continues from `b` to a specified subset of its successors, `cond`
        // contains the corresponding VIR expression.
        let cond_conjuncts = conditions
            .all_branch_choices()
            .map(|choices| {
                let successors = choices.successors(self.body);
                let from = choices.from();
                let conj = successors
                    .iter()
                    .map(|to| self.from_to_vars.get_or_create(self.vcx, from, *to).expr)
                    .collect::<Vec<_>>();
                // Control flow must continue from `choices.from()` to any one of the `successors`
                self.vcx.mk_disj(self.vcx.alloc_slice(&conj))
            })
            .collect::<Vec<_>>();
        // For each block `b` where the edge validity depends on the successor taken from `b`,
        // every successor must be valid.
        let cond = self.vcx.mk_conj(self.vcx.alloc_slice(&cond_conjuncts));
        let stmts = self.block(|self_| {
            self_.pcs_handle_edge_conditionless(
                borrows_state,
                edge,
                edge_action,
                label,
                edge_to_loop,
                to_skip,
            )
        })?;
        if stmts.is_empty()
            || stmts
                .iter()
                .all(|stmt| matches!(stmt.kind, vir::StmtKindData::Comment(_)))
            || cond_conjuncts.is_empty()
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
        edge_action: EdgeAction,
        label: Option<&'vir str>,
        edge_to_loop: bool,
        to_skip: &mut Vec<mir::BasicBlock>,
    ) -> EncodeResult<'vir, (), E> {
        match edge.kind() {
            BorrowPcgEdgeKind::Borrow(borrow) if borrow.is_mut() && edge_action.is_remove() => {
                // For a borrow e.g. let x = &mut y; the capability to `y` is
                // folded into the Rvalue `&mut y` that is stored in `x`. This
                // reverses that effect
                self.unfold(borrow.assigned_ref(), label);
            }
            BorrowPcgEdgeKind::BorrowFlow(borrow_flow)
                if let BorrowFlowEdgeKind::Assignment(assignment_data) = borrow_flow.kind()
                    && let Some(mir::CastKind::PointerCoercion(
                        ty::adjustment::PointerCoercion::Unsize,
                        _,
                    )) = assignment_data.cast_kind()
                    && edge_action.is_remove() =>
            {
                let kind = assignment_data.cast_kind().unwrap();

                // For an unsize operation `let slice = &mut array;` the PCG
                // will keep track of the connection between the two places;
                // during the unsize operation we call a method to transter
                // permissions from one to the other, when the slice expires,
                // we need to undo the unsize operation.
                let long = borrow_flow.long();
                let short = borrow_flow.short();
                let PlaceOrConst::Place(src) = long.base() else {
                    unreachable!();
                };
                let src = src.as_local_place().unwrap();
                let dst = short.base();

                let ctxt = CompilerCtxt::new(self.body, self.vcx.tcx(), ());
                let src_ty = src.ty(ctxt).ty;
                let dst_ty = dst.ty(ctxt).ty;
                // An undo is only needed when processing coercions `&mut T -> &mut U` when T: Unsize<U>:
                // The mutable borrow ends and we need to return the permission to the original
                // `&mut T`. For every other CoerceUnsized destination (`&T`, raw pointers,
                // `Box<T>`, `Rc<T>`, `Arc<T>`, ...), there is no mutable borrow expiring and
                // nothing to undo. (For shared references the slice cannot have modified the
                // array it unsized from, so there is likewise nothing to undo.)
                if !matches!(dst_ty.kind(), ty::TyKind::Ref(_, _, ty::Mutability::Mut)) {
                    return Ok(());
                }
                // Since we only undo unsize coercions for &mut T -> &mut U when T: Unsize<U>,
                // we only consider the edge with idx=0 on both src and dst. This
                // corresponds to the lifetime projections of the mutable references.
                // The single undo accounts for the entire unsize coercion.
                // All other BorrowFlow(Unsize) edges in the PCG are bookkeeping, for example:
                //   - same-index (e.g. `&mut [&mut T; N] -> &mut [&mut T]`
                //     emits a redundant idx=1 -> idx=1 edge
                //   - cross-index (e.g. `&mut T -> &mut dyn Trait + 'b`
                //     emits an idx=0 -> idx=1 edge).
                if long.region_idx().index() != 0 || short.region_idx().index() != 0 {
                    return Ok(());
                }

                let rvalue_ty = RustTyDecomposition::from_ty(dst_ty, self.context());
                let operand_ty = RustTyDecomposition::from_ty(src_ty, self.context());
                let cast_output =
                    self.deps()
                        .require_dep::<MirBuiltinUseCastEnc>(MirBuiltinUseCastTask::new(
                            rvalue_ty, kind, operand_ty,
                        ))?;
                let src_place = src.place();
                let src_label = if let MaybeLabelledPlace::Labelled(snap) = src {
                    Some(self.get_location_label(snap.at()))
                } else {
                    label.map(vir::OldLabel::Label)
                };
                let src_snap = self.encode_place_with_snap(src_place).1.downcast_ty();
                let src_enc = self.vcx.maybe_apply_label(src_snap, src_label);
                let undo = cast_output.undo(src_enc);
                self.stmts(undo);
                return Ok(());
            }
            BorrowPcgEdgeKind::Deref(deref) => {
                self.fold_or_unfold(
                    deref.blocked_place(),
                    FoldOrUnfold::for_action(edge_action),
                    None,
                    label,
                );
            }
            // Ignore expansions of lifetime projections for now
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion)
                if let PcgNode::Place(base) = expansion.base() =>
            {
                self.fold_or_unfold(
                    base,
                    FoldOrUnfold::for_action(edge_action),
                    Some(expansion),
                    label,
                );
            }
            BorrowPcgEdgeKind::Coupled(PcgCoupledEdgeKind(FunctionCallOrLoop::FunctionCall(
                call_edge,
            ))) => {
                if edge_action.is_add() {
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
                let wands = self.deps.require_dep::<WandEnc>(WandEncTask {
                    data: call.function_data().unwrap(),
                })?;
                let bb = &self.body[call.location().block];
                let terminator = bb.terminator.as_ref().unwrap();
                match &terminator.kind {
                    mir::TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        ..
                    } => {
                        // Calls not encoded as impure method calls create no
                        // wands (e.g., a Viper function application).
                        if self.wandless_calls.contains(&call.location().block) {
                            return Ok(());
                        }
                        let (_, caller_substs, _) = self.get_call_data(func);

                        let (_, dest_snap, _, _) =
                            self.encode_place_with_snap((*destination).into());
                        let wand_args =
                            std::iter::once(Ok(dest_snap))
                                .chain(args.iter().map(|operand| {
                                    self.encode_operand_snap_immediate(&operand.node)
                                }))
                                .collect::<Result<Vec<_>, EncodeFullError<'vir, E>>>()?;
                        let (label_pre, label_post) = self.call_labels[&call.location().block];
                        let call_ctx = self.gargs(caller_substs);
                        wands.apply_wands(&wand_args, label_pre, label_post, call_ctx, self);
                    }
                    _ => unreachable!(),
                }
            }
            BorrowPcgEdgeKind::Abstraction(at @ AbstractionEdge::Loop(_)) => {
                self.pcs_handle_wand(
                    borrows_state,
                    edge_action.is_add(),
                    &at.clone().into_singleton_coupled_edge(),
                    label,
                    edge_to_loop,
                );
            }
            other => comment!(self, "(ignoring) {edge_action:?} {other:?}"),
        }
        comment!(
            self,
            "(PCG) handled edge {edge_action:?}: {}",
            edge.to_short_string(self.pcg_ctxt())
        );
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
                EdgeAction::Remove,
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

    /// Emit the repacks of `phase` at `location`.
    fn pcg_phase_actions(
        &mut self,
        location: mir::Location,
        phase: EvalStmtPhase,
    ) -> EncodeResult<'vir, (), E> {
        let current_fpcs = self.current_fpcs.take().unwrap();
        let cfpcs = &current_fpcs.statements[location.statement_index];
        self.pcg_actions(&cfpcs.states[phase], &cfpcs.actions(phase), false)?;
        self.current_fpcs = Some(current_fpcs);
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
            //Restore(RestoreCapability<'tcx>),
            //MakePlaceOld(Place<'tcx>),
            //SetLatest(Place<'tcx>, Location),
            //AddRegionProjectionMember(RegionProjectionMember<'tcx>, PathConditions),
            BorrowPcgActionKind::RemoveEdge(edge) => self.pcs_handle_edge(
                pcg.borrow_pcg(),
                edge,
                EdgeAction::Remove,
                None,
                edge_to_loop,
                &mut to_skip,
            ),
            BorrowPcgActionKind::AddEdge { edge } => self.pcs_handle_edge(
                pcg.borrow_pcg(),
                edge,
                EdgeAction::Add,
                None,
                edge_to_loop,
                &mut to_skip,
            ),
            BorrowPcgActionKind::Weaken(weaken)
                if matches!(weaken.from_cap(), CapabilityKind::Exclusive)
                    && matches!(weaken.to_cap(), None | Some(CapabilityKind::Write)) =>
            {
                self.pcg_weaken(weaken.place(), weaken.is_for_storage_dead());
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

        fn should_ignore(repack_op: &RepackOp<'_>) -> bool {
            match repack_op {
                RepackOp::RegainLoanedCapability(..) => true,
                RepackOp::Weaken(weaken) => {
                    weaken.from_cap().is_exclusive() && weaken.to_cap().is_read()
                }
                RepackOp::StorageDead(..) => true,
                _ => false,
            }
        }

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
                // TODO: guide should be implemented on `RepackOp`
                let guide = match repack_op {
                    pcg::free_pcs::RepackOp::Expand(expand) => expand.guide(),
                    pcg::free_pcs::RepackOp::Collapse(collapse) => collapse.guide(),
                    _ => None,
                };
                let index = guide.and_then(|guide| match guide {
                    RepackGuide::Index(index_local, _) => {
                        let index = self
                            .encode_operand_snap(&mir::Operand::Copy(index_local.into()), &None)
                            .unwrap();
                        let usize_ty_out = self.ty_use_pure(self.vcx.tcx().types.usize);
                        Some(
                            usize_ty_out
                                .expect_primitive()
                                .snap_to_prim(index.downcast_ty())
                                .downcast_ty(),
                        )
                    }
                    _ => None,
                });
                if matches!(repack_op, pcg::free_pcs::RepackOp::Expand(..)) {
                    self.stmts(data.unfold(place_ty.variant_index, place_enc, index, None, None));
                } else if matches!(repack_op, pcg::free_pcs::RepackOp::Collapse(..)) {
                    self.stmts(data.fold(place_ty.variant_index, place_enc, index, None, None));
                } else {
                    unreachable!()
                }
            }
            RepackOp::Weaken(weaken)
                if weaken.from_cap().is_exclusive() && weaken.to_cap().is_write() =>
            {
                self.pcg_weaken(weaken.place(), weaken.is_for_storage_dead())
            }
            other => {
                if should_ignore(other) {
                    self.stmt(self.vcx.mk_comment_stmt(vir::vir_format!(
                        self.vcx,
                        "ignored repack op: {other:?}"
                    )));
                } else {
                    self.stmt(self.vcx.mk_comment_stmt(vir::vir_format!(
                        self.vcx,
                        "unsupported repack op: {other:?}"
                    )));
                    self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                }
            }
        }
    }

    fn pcg_weaken(&mut self, place: Place<'vir>, for_storage_dead: bool) {
        let place_ty = place.ty(self.pcg_ctxt());
        assert!(place_ty.variant_index.is_none());

        // Skip the exhale for StorageDead-triggered weakens, since the place may
        // have already been moved/consumed and no longer hold permissions.
        // Temporary workaround until https://github.com/prusti/pcg/issues/137
        // is resolved.
        if for_storage_dead {
            comment!(
                self,
                "Weaken(E, W) for {:?} (skipped exhale: StorageDead)",
                place
            );
            return;
        }

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

    fn loop_head_of(&mut self, block: mir::BasicBlock) -> Option<LoopId> {
        self.loop_analysis().loop_head_of(block)
    }

    fn pcs_succ<'a>(
        &mut self,
        cfpcs: &PcgLocation<'_, 'vir>,
        succ: &'a PcgSuccessor<'_, 'vir>,
    ) -> Result<(), EncodeFullError<'vir, E>> {
        // The terminator's deferred `PostMain` actions (e.g. the collapse
        // re-packing owned places for the CFG join); see
        // [Self::visit_terminator].
        comment!(self, "PCG (T) {}", EvalStmtPhase::PostMain);
        let post_main = &cfpcs.states[EvalStmtPhase::PostMain];
        self.pcg_actions(post_main, &cfpcs.actions(EvalStmtPhase::PostMain), false)?;
        let edge_to_loop = self.loop_head_of(succ.block()).is_some();
        self.pcg_actions(post_main, succ.actions(), edge_to_loop)
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
                (self.encode_operand_snap(operand, &None)?, ty_out)
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

    /// Read `operand`'s snapshot into a fresh temporary at the current
    /// program point; a `Move` operand additionally consumes its place,
    /// exhaling the place's predicate.
    fn capture_operand_snap(
        &mut self,
        operand: &mir::Operand<'vir>,
    ) -> EncodeResult<'vir, vir::ExprSnap<'vir>, E> {
        match operand {
            &mir::Operand::Copy(place) | &mir::Operand::Move(place) => {
                let (result, snap_val, _, ty_out) = self.encode_place_with_snap(Place::from(place));
                let tmp = self.new_tmp(ty_out.snapshot());
                self.stmt(self.vcx.mk_pure_assign_stmt(tmp, snap_val));
                if matches!(operand, mir::Operand::Move(_)) {
                    self.stmt(self.vcx.mk_exhale_stmt(ty_out.ref_to_pred(
                        self.vcx,
                        result.expr.expect_predicate(),
                        None,
                    )));
                }
                Ok(tmp)
            }
            mir::Operand::Constant(box constant) => {
                Ok(self.encode_constant_snap(constant)?.upcast_ty())
            }
        }
    }

    /// Read `statement`'s operands into an [OperandSnaps] map; see the call
    /// site in [Self::visit_statement].
    fn capture_operand_snaps(
        &mut self,
        statement: &mir::Statement<'vir>,
        location: mir::Location,
    ) -> EncodeResult<'vir, OperandSnaps<'vir>, E> {
        use mir::visit::Visitor;
        struct OperandCollector<'vir>(Vec<mir::Operand<'vir>>);
        impl<'vir> Visitor<'vir> for OperandCollector<'vir> {
            fn visit_operand(&mut self, operand: &mir::Operand<'vir>, _location: mir::Location) {
                if operand.place().is_some() {
                    self.0.push(operand.clone());
                }
            }
        }
        let mut collector = OperandCollector(Vec::new());
        collector.visit_statement(statement, location);
        let mut snaps = FxHashMap::default();
        for operand in &collector.0 {
            let place = operand.place().unwrap();
            if snaps.contains_key(&place) {
                continue;
            }
            let snap = self.capture_operand_snap(operand)?;
            snaps.insert(place, snap);
        }
        Ok(Some(snaps))
    }

    pub(crate) fn encode_place(&mut self, place: Place<'vir>) -> EncodePlaceResult<'vir> {
        let mut place_ty = mir::PlaceTy::from_ty(self.local_decls[place.local].ty);
        let mut result = PlaceExpr {
            address: self.local_defs[place.local].local_ex,
            metadata: None,
            snap: None,
        };
        // TODO: factor this out (duplication with pure encoder)?
        for (place, elem) in place.iter_projections() {
            result = self.encode_place_element(place.into(), elem, result);
            place_ty = place_ty.projection_ty(self.vcx.tcx(), elem);
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
        place: Place<'vir>,
        elem: mir::PlaceElem<'vir>,
        expr: PlaceExpr<'vir>,
    ) -> PlaceExpr<'vir> {
        let place_ty = place.ty(self.pcg_ctxt());
        match elem {
            mir::ProjectionElem::Field(field_idx, _) => {
                let e_ty = self.ty_use_impure(place_ty.ty);
                let field_access = e_ty.expect_variant_opt(place_ty.variant_index);
                // Only the last field of a struct/tuple can be unsized (a DST's
                // tail); it then shares the containing value's pointer metadata.
                let is_last_field = field_idx.index() + 1 == field_access.fields.len();
                PlaceExpr {
                    address: field_access[field_idx].field_ref(expr.address),
                    metadata: if is_last_field { expr.metadata } else { None },
                    snap: expr.snap.map(|snap| {
                        let e_ty = self.ty_use_pure(place_ty.ty);
                        let field_access = e_ty.expect_variant_opt(place_ty.variant_index);
                        field_access[field_idx].read(snap.downcast_ty())
                    }),
                }
            }

            mir::ProjectionElem::Index(idx) => {
                let e_ty = self.ty_use_impure(place_ty.ty).expect_array();
                let idx = self.encode_place_with_snap(mir::Place::from(idx).into());
                let usize_ty = self.ty_use_pure(self.vcx.tcx().types.usize);
                let idx = usize_ty
                    .expect_primitive()
                    .snap_to_prim(idx.1.downcast_ty())
                    .downcast_ty();
                PlaceExpr {
                    address: e_ty.ref_to_index_ref(expr.address, idx),
                    metadata: None,
                    snap: expr.snap.map(|snap| {
                        let e_ty = self.ty_use_pure(place_ty.ty).expect_array();
                        e_ty.index(snap.downcast_ty(), idx)
                    }),
                }
            }
            // TODO: should all variants start at the same `Ref`?
            mir::ProjectionElem::Downcast(..) => PlaceExpr {
                address: expr.address,
                metadata: None,
                snap: expr.snap,
            },
            mir::ProjectionElem::Deref => {
                assert!(place_ty.variant_index.is_none());
                let e_ty = self.ty_use_impure(place_ty.ty);
                match place_ty.ty.kind() {
                    ty::TyKind::Adt(adt, _) if adt.is_box() => {
                        let field_access = e_ty.expect_variant_opt(None);
                        PlaceExpr {
                            // TODO: this is unsound: a Box should be modelled
                            // with a Ref field rather than a field_access
                            // function.
                            address: field_access[abi::FieldIdx::ZERO].field_ref(expr.address),
                            // TODO: also should have metadata
                            metadata: None,
                            snap: expr.snap.map(|snap| {
                                let e_ty = self.ty_use_pure(place_ty.ty);
                                let field_access = e_ty.expect_variant_opt(None);
                                field_access[abi::FieldIdx::ZERO].read(snap.downcast_ty())
                            }),
                        }
                    }
                    ty::TyKind::Ref(_, _, ty::Mutability::Not) => {
                        let snap = expr
                            .snap
                            .unwrap_or_else(|| e_ty.ref_to_snap(expr.address))
                            .downcast_ty();
                        let p_ty = self.ty_use_pure(place_ty.ty).expect_immref();
                        PlaceExpr {
                            address: p_ty.deref_access(snap),
                            metadata: Some(p_ty.metadata_access(snap)),
                            snap: Some(p_ty.value_access(snap)),
                        }
                    }
                    ty::TyKind::Ref(_, _, ty::Mutability::Mut) => {
                        let ref_snap = e_ty.ref_to_snap(expr.address).downcast_ty();
                        let p_ty = self.ty_use_pure(place_ty.ty).expect_mutref();
                        PlaceExpr {
                            address: p_ty.deref_access(ref_snap),
                            metadata: Some(p_ty.metadata_access(ref_snap)),
                            snap: None,
                        }
                    }
                    ty::TyKind::RawPtr(..) => {
                        let ref_snap = e_ty.ref_to_snap(expr.address).downcast_ty();
                        let p_ty = self.ty_use_pure(place_ty.ty).expect_raw();
                        PlaceExpr {
                            address: p_ty.address_access(ref_snap),
                            metadata: Some(p_ty.metadata_access(ref_snap)),
                            snap: None,
                        }
                    }
                    _ => unreachable!(),
                }
            }
            _ => todo!("Unsupported ProjectionElem {:?}", elem),
        }
    }

    fn get_call_data(&self, func: &mir::Operand<'vir>) -> (DefId, ty::GenericArgsRef<'vir>, bool) {
        let func_ty = func.ty(self.body, self.vcx.tcx());
        let (func_def_id, caller_substs) = RustSignature::get_def_id_and_caller_substs(func_ty);
        let is_pure =
            crate::encoders::is_function_pure(func_def_id, GArgs::new(self.def_id, caller_substs));
        (func_def_id, caller_substs, is_pure)
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

    pub(crate) fn get_location_label(&self, at: SnapshotLocation) -> vir::OldLabel<'vir> {
        // TODO: this should probably take pre-loop labels into account, somehow
        if let SnapshotLocation::BeforeJoin(bb) | SnapshotLocation::Loop(bb) = at {
            return vir::OldLabel::Block(vir::CfgBlockLabelData::BasicBlock(bb.as_usize()));
        }
        let prefix = match at {
            SnapshotLocation::Before(..) => LocationLabelPrefix::Before,
            SnapshotLocation::After(..) => LocationLabelPrefix::After,
            SnapshotLocation::BeforeRefReassignment(..) => {
                LocationLabelPrefix::BeforeRefReassignment
            }
            SnapshotLocation::Loop(_) | SnapshotLocation::BeforeJoin(_) => unreachable!(),
        };
        let location = at.location();
        let label = self.location_label(prefix, location, &[]);
        vir::OldLabel::Label(label)
    }

    pub(crate) fn location_label(
        &self,
        prefix: LocationLabelPrefix,
        location: mir::Location,
        loop_pres: &[usize],
    ) -> &'vir str {
        let pres = loop_pres
            .iter()
            .map(|l| format!("_pre{l}"))
            .collect::<String>();
        vir::vir_format!(
            self.vcx,
            "_{}_{}{pres}_{}",
            prefix.to_str(),
            location.block.index(),
            location.statement_index
        )
    }

    fn new_before_label(&mut self, location: mir::Location) {
        let label = self.location_label(
            LocationLabelPrefix::Before,
            location,
            self.current_block_pres.as_ref().unwrap(),
        );
        self.stmt(self.vcx.mk_label_stmt(label));
    }

    fn set_from_to_flag(&mut self, from: mir::BasicBlock, to: mir::BasicBlock) -> vir::Stmt<'vir> {
        self.from_to_vars.set_from_to_flag_stmt(self.vcx, from, to)
    }

    pub fn visit_body(&mut self, body: &mir::Body<'vir>) -> Result<(), EncodeFullError<'vir, E>> {
        /// A work-queue item, min-ordered by the block's reverse-postorder
        /// index (ties broken by insertion order): every non-back-edge
        /// predecessor of a block is then encoded before the block itself,
        /// in particular both branches before their join. The borrow-expiry
        /// handling relies on this: a call's `call_labels`/`wandless_calls`
        /// entry must exist by the time an expiring borrow references the
        /// call's block. `heads_hit` is payload, not part of the order.
        struct WorkItem {
            rpo_idx: usize,
            seq: usize,
            block: mir::BasicBlock,
            heads_hit: FxHashSet<LoopId>,
        }
        impl PartialEq for WorkItem {
            fn eq(&self, other: &Self) -> bool {
                (self.rpo_idx, self.seq) == (other.rpo_idx, other.seq)
            }
        }
        impl Eq for WorkItem {}
        impl PartialOrd for WorkItem {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for WorkItem {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                // Reversed so that the max-heap `BinaryHeap` pops the minimum.
                (other.rpo_idx, other.seq).cmp(&(self.rpo_idx, self.seq))
            }
        }

        let rpo_idx: FxHashMap<mir::BasicBlock, usize> = body
            .basic_blocks
            .reverse_postorder()
            .iter()
            .enumerate()
            .map(|(idx, block)| (*block, idx))
            .collect();
        let mut next_seq = 0..;
        let mut queue = std::collections::BinaryHeap::new();
        let mut visited = FxHashSet::default();

        // In Prusti, we want to be able to support body invariants, i.e.,
        // functional specifications for loops, placed at a point further
        // *within* the loop body. When encoding such invariants into Viper, we
        // choose to unroll the first part of the loop (before the invariant is
        // reached), then encode the rest of the loop followed by the repeated
        // first part of the loop as an actual Viper loop with an invariant
        // annotation. This means that the part of the loop before the body
        // invariant is reached is encoded in duplicate, thus we need to ensure
        // basic block labels etc are *not* emitted in duplicate. As a result,
        // we keep track of a "pre-loop" set: the set of loops we have entered
        // (in the CFG) but whose body invariants we have not yet reached.
        //
        // The pre-loop set is a set because of pathological cases like this:
        // ```rust
        // while { // (OUT)
        //     loop { // (IN)
        //         // (maybe break;) ... (A)
        //         body_invariant!(...);
        //         // ...
        //     }
        //     // ...
        // } {
        //     // ...
        //     body_invariant!(...);
        //     // ...
        // }
        // ```
        // Here, the loop guard of the outer `while` loop contains a loop as
        // well. The "(A)" code fragment must be encoded multiple times:
        // * when entering (OUT) and (IN);
        // * when entering (OUT), for an arbitrary iteration of (IN);
        // * for an arbitrary iteration of (OUT); entering (IN); and
        // * for an arbitrary iteration of (OUT) and (IN).
        // The pre-loop sets for the four instances are, respectively:
        // * {OUT, IN},
        // * {OUT},
        // * {IN}, and
        // * {}.
        //
        // Loop heads and body invariants: loops as identified by the PCG loop
        // analysis have a loop head at the very first basic block, i.e., the
        // basic block that backedges jump to. For Prusti, we want to instead
        // consider the body invariant, if declared, to be the loop head, as
        // explained above. We only fall back to the PCG loop head if the body
        // invariant is not declared (i.e., we will only emit a permission
        // invariant, not a functional specification).
        //
        // The overall approach in this method is to walk basic blocks of the
        // CFG using a queue. Each item in the queue is a pair (basic block.
        // loop heads hit), where the latter is a set of loop heads that were
        // already crossed on this path. The pre-loop set is then the set of
        // loops the current block is in minus loop heads hit.

        // keep track of which loops we have already entered (on a particular
        // path); a LoopId is in this set as soon as the loop head (or the body
        // invariant for a loop with one) is entered
        let mut start_heads = FxHashSet::default();
        let start_loops = self
            .loop_analysis()
            .loops(mir::START_BLOCK)
            .collect::<FxHashSet<_>>();
        if !start_loops.is_empty() {
            // the start block is either not part of a loop, or else it is in
            // exactly one loop, of which it *may* be the head (if the body
            // invariant is omitted or coincides with the start block)
            assert_eq!(start_loops.len(), 1);
            let start_loop = *start_loops.iter().next().unwrap();
            if self.spec_blocks.loop_head_at[&start_loop] == mir::START_BLOCK {
                start_heads.insert(start_loop);
            }
        }
        queue.push(WorkItem {
            rpo_idx: rpo_idx[&mir::START_BLOCK],
            seq: next_seq.next().unwrap(),
            block: mir::START_BLOCK,
            heads_hit: start_heads,
        });

        while let Some(WorkItem {
            block,
            mut heads_hit,
            ..
        }) = queue.pop()
        {
            let in_loops = self.loop_analysis().loops(block).collect::<FxHashSet<_>>();

            heads_hit.retain(|l| in_loops.contains(l));

            // is this a loop head?
            if let Some(loop_spec) = self.spec_blocks.loop_specs.get(&block)
                && !heads_hit.insert(loop_spec.loop_id)
            {
                // we already walked over this loop head, so the full loop
                // iteration was already emitted on this path
                continue;
            }

            let pre_loops = in_loops
                .iter()
                .copied()
                .filter(|l| !heads_hit.contains(l))
                .sorted()
                .collect::<Vec<_>>();

            if !visited.insert((block, pre_loops.clone())) {
                continue;
            }

            self.current_block = Some(block);
            // Allocate label for current block and its successors with the
            // correct pre-loop prefixes.
            self.current_block_pres = Some(pre_loops.iter().map(|l| l.index()).collect());
            self.current_block_succs = Some(
                body.basic_blocks
                    .successors(block)
                    // Successors can have a different prefix than the current
                    // block; the successor can be:
                    // * part of a loop the current block is not in;
                    // * the loop head of a loop the current block is in; and/or
                    // * not part of a loop the current block is in.
                    .map(|succ| {
                        // TODO: this does a lot of duplicate work
                        //   maybe some two-pass approach would be nicer?
                        let succ_in_loops =
                            self.loop_analysis().loops(succ).collect::<FxHashSet<_>>();
                        let mut succ_heads_hit = heads_hit.clone();
                        succ_heads_hit.retain(|l| succ_in_loops.contains(l));
                        if let Some(loop_spec) = self.spec_blocks.loop_specs.get(&succ) {
                            succ_heads_hit.insert(loop_spec.loop_id);
                        }
                        let succ_pre_loops = succ_in_loops
                            .iter()
                            .copied()
                            .filter(|l| !succ_heads_hit.contains(l))
                            .map(|l| l.index())
                            .sorted();
                        (
                            succ,
                            self.vcx.mk_block_label(succ.as_usize(), succ_pre_loops),
                        )
                    })
                    .collect(),
            );

            self.visit_basic_block_data(block, &body[block])?;
            self.current_block = None;
            self.current_block_pres = None;
            self.current_block_succs = None;

            for successor in body.basic_blocks.successors(block) {
                // Specification-only arms are not encoded at all; their
                // switches are encoded as jumps to the live target.
                if self.spec_blocks.spec_arms.blocks.contains(&successor) {
                    continue;
                }
                queue.push(WorkItem {
                    rpo_idx: rpo_idx[&successor],
                    seq: next_seq.next().unwrap(),
                    block: successor,
                    heads_hit: heads_hit.clone(),
                });
            }
        }
        Ok(())
    }

    fn encode_spec_block(
        &mut self,
        spec_block: mir::BasicBlock,
    ) -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, E>> {
        let enc_output = self.deps.require_dep::<MirPureEnc>(MirPureEncTask {
            encoding_depth: 0,
            parent_def_id: self.def_id,
            gargs: GParams::from(self.def_id).identity_args(),
            kind: PureKind::SpecBlock(spec_block),
        })?;
        use vir::Reify;
        let locals: FxHashMap<mir::Local, _> = enc_output
            .inputs
            .iter()
            .map(|local| (*local, self.local_defs[*local].impure_snap))
            .collect();
        let expr = enc_output
            .expr
            .reify(self.vcx, (self.def_id, self.vcx.alloc(locals)))
            .downcast_ty();
        Ok(expr)
    }

    fn visit_basic_block_data(
        &mut self,
        block: mir::BasicBlock,
        data: &mir::BasicBlockData<'vir>,
    ) -> Result<(), EncodeFullError<'vir, E>> {
        let current_block_label = self.vcx.mk_block_label(
            block.as_usize(),
            self.current_block_pres.as_ref().unwrap().iter().copied(),
        );

        // We are verifying the absence of panics, so cleanup block should never
        // be reached, or even referenced.
        if data.is_cleanup {
            self.encoded_blocks.push(
                self.vcx.mk_cfg_block(
                    current_block_label,
                    &[],
                    &[],
                    self.vcx
                        .mk_dummy_stmt(vir::vir_format!(self.vcx, "cleanup block")),
                ),
            );
            return Ok(());
        }

        // Specification-only arms are unreachable after their switches are
        // encoded as jumps to the live target; emit nothing. The specs
        // themselves are encoded separately (assertions at the block they
        // are attached to, loop invariants at the loop head, closure specs
        // as the closure's contract).
        if self.spec_blocks.spec_arms.blocks.contains(&block) {
            return Ok(());
        }

        self.deps().check_cycle()?;

        self.current_stmts = Some(Vec::with_capacity(
            data.statements.len(), // TODO: not exact?
        ));
        self.current_block_label = Some(current_block_label);
        let cfpcs = self.fpcs_analysis.get_all_for_bb(block).unwrap().unwrap();

        // Calculate invariant at the body invariant, if specified, or at the
        // loop head by default
        let mut invariant = None;
        if let Some(loop_spec) = self.spec_blocks.loop_specs.get(&block) {
            let loop_place_usages = self
                .fpcs_analysis
                .analysis()
                .loop_place_usages(loop_spec.loop_id)
                .clone();
            let functional = loop_spec
                .invariants
                .clone()
                .into_iter()
                .map(|(spec_block, span)| {
                    self.vcx.with_span(span, |vcx| {
                        let error_msg = "loop invariant might not be preserved";
                        vcx.handle_error("invariant.not.preserved:assertion.false", move |_| {
                            Some(vec![PrustiError::verification(error_msg, span.into())])
                        });
                        self.vcx.with_span(span, |vcx| {
                            let error_msg = "loop invariant might not hold on entry";
                            vcx.handle_error(
                                "invariant.not.established:assertion.false",
                                move |_| {
                                    Some(vec![PrustiError::verification(error_msg, span.into())])
                                },
                            );
                            self.encode_spec_block(spec_block)
                        })
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            let permissions = self.get_loop_inv(&cfpcs, &loop_place_usages, self.pcg_ctxt());
            invariant = Some(
                self.vcx.alloc_slice(
                    &permissions
                        .into_iter()
                        .chain(functional)
                        .collect::<Vec<_>>(),
                ),
            );
        }

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
        for (index, statement) in data.statements.iter().enumerate() {
            let location = mir::Location {
                block,
                statement_index: index,
            };
            self.visit_statement(statement, location)?;
        }
        let location = mir::Location {
            block,
            statement_index: data.statements.len(),
        };
        self.visit_terminator(data.terminator(), location)?;

        if let Some(specs) = self.spec_blocks.specs_for.get(&block).cloned() {
            for spec in specs {
                let spec_expr = self.encode_spec_block(spec.block)?;
                let span = spec.span;
                match spec.kind {
                    SpecBlockKind::Assert => {
                        self.vcx.with_span(span, |vcx| {
                            let error_msg = "assertion might not hold";
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification(error_msg, span.into())])
                            });
                            self.stmt(self.vcx.mk_exhale_stmt(spec_expr));
                        });
                    }
                    SpecBlockKind::Assume => {
                        self.stmt(self.vcx.mk_inhale_stmt(spec_expr));
                    }
                    SpecBlockKind::Refute => {
                        // TODO: handle_error
                        self.stmt(self.vcx.mk_refute_stmt(spec_expr));
                    }
                    SpecBlockKind::LoopInvariant => {
                        // nothing to do: loop invariants are handled elsewhere
                    }
                }
            }
        }

        let stmts = self.current_stmts.take().unwrap();
        let terminator = self.current_terminator.take().unwrap();
        self.encoded_blocks.push(self.vcx.mk_cfg_block(
            self.current_block_label.take().unwrap(),
            invariant.unwrap_or_default(),
            self.vcx.alloc_slice(&stmts),
            terminator,
        ));
        Ok(())
    }

    fn visit_statement(
        &mut self,
        statement: &mir::Statement<'vir>,
        location: mir::Location,
    ) -> Result<(), EncodeFullError<'vir, E>> {
        self.vcx.with_span(statement.source_info.span, |_vcx| {
            self.deps().check_cycle()?;

            self.new_before_label(location);

            comment!(self, "[MIR] {location:?}: {statement:?}");

            self.pcg_phase_actions(location, EvalStmtPhase::PreOperands)?;

            // Read the statement's operands at their temporal position,
            // between the `PreOperands` and `PostOperands` repacks. An
            // operand's place may alias the destination, whose predicate the
            // `PreMain` weaken exhales before the effect is encoded (`x /= y`
            // lowers to `x = Div(copy x, move y)`).
            let captured = self.capture_operand_snaps(statement, location)?;

            self.pcg_phase_actions(location, EvalStmtPhase::PostOperands)?;
            self.pcg_phase_actions(location, EvalStmtPhase::PreMain)?;

            // Assignments to the locals only serving specification-only arms
            // (necessarily scaffolding stores) are not encoded, since the
            // locals are not declared.
            if let mir::StatementKind::Assign(box (dest, _)) = &statement.kind
                && let Some(local) = dest.as_local()
                && self.spec_blocks.spec_arms.spec_only_locals.contains(&local)
            {
                return Ok(());
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
                    let rval_enc = self.encode_rvalue(rvalue, span, &captured);

                    match rval_enc {
                        Ok(rval_enc) => {
                            let dest_ty = dest.ty(self.local_decls, self.vcx.tcx());
                            assert!(dest_ty.variant_index.is_none());
                            let dest_ty_out = self.ty_use_impure(dest_ty.ty);
                            let method_assign_app =
                                dest_ty_out.apply_method_assign(self.vcx, proj_enc, rval_enc.expr);
                            self.stmt(method_assign_app);
                            self.stmts(rval_enc.post_fold_stmts(proj_enc));
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

            self.pcg_phase_actions(location, EvalStmtPhase::PostMain)?;
            Ok(())
        })
    }

    fn visit_terminator(
        &mut self,
        terminator: &mir::Terminator<'vir>,
        location: mir::Location,
    ) -> Result<(), EncodeFullError<'vir, E>> {
        self.deps().check_cycle()?;

        self.new_before_label(location);
        comment!(self, "[MIR] {location:?}: {:?}", terminator.kind);
        let span = terminator.source_info.span;

        // `PostMain` is not emitted here: a terminator's operands are read
        // after these phases' repacks (e.g. a `SwitchInt` discriminant that
        // projects into an aggregate is read in the branch condition, relying
        // on the `PreOperands` unfolds), while the `PostMain` actions re-pack
        // owned places for the CFG join and thus may fold those operands'
        // places away. They are instead emitted on each outgoing edge by
        // [Self::pcs_succ], after the terminator's operands have been read.
        // Terminators that do not go through [Self::pcs_succ] have no
        // successor state to re-pack for.
        for phase in [
            EvalStmtPhase::PreOperands,
            EvalStmtPhase::PostOperands,
            EvalStmtPhase::PreMain,
        ] {
            comment!(self, "PCG (T) {phase}");
            self.pcg_phase_actions(location, phase)?;
        }

        // A specification-only arm's `if false` switch is encoded as an
        // unconditional jump to the live target (the continuation, or the
        // inline ghost body); the arm itself is not encoded.
        let spec_goto = self
            .spec_blocks
            .spec_arms
            .switches
            .get(&location.block)
            .map(|live_target| mir::TerminatorKind::Goto {
                target: *live_target,
            });
        let terminator = match spec_goto.as_ref().unwrap_or(&terminator.kind) {
            mir::TerminatorKind::Goto { target }
            | mir::TerminatorKind::FalseUnwind {
                real_target: target,
                ..
            }
            | mir::TerminatorKind::FalseEdge {
                real_target: target,
                ..
            }
            | mir::TerminatorKind::Drop { target, .. } => {
                // A `Drop`'s semantics (releasing the dropped place's
                // permission via a weaken exhale) are carried by the PCG
                // statements, so only its goto remains to be encoded here.
                self.pcs_succ_to(*target)?;
                let set_flag = self.set_from_to_flag(location.block, *target);
                self.stmt(set_flag);
                self.vcx
                    .mk_goto_stmt(self.current_block_succs.as_ref().unwrap()[target])
            }
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let discr_ty_rs = discr.ty(self.local_decls, self.vcx.tcx());
                let discr_ty = self.ty_use_pure(discr_ty_rs).expect_primitive();

                let goto_targets = self.vcx.alloc_slice(
                    &targets
                        .iter()
                        .enumerate()
                        .map(|(idx, (value, target))| {
                            let mut extra_stmts = self.collect_pcs_succ_at(idx, target)?;
                            extra_stmts.push(self.set_from_to_flag(location.block, target));

                            Ok(self.vcx.mk_goto_if_target(
                                discr_ty.expr_from_bits(discr_ty_rs, value).as_dyn(),
                                self.current_block_succs.as_ref().unwrap()[&target],
                                self.vcx.alloc_slice(&extra_stmts),
                            ))
                        })
                        .collect::<Result<Vec<_>, EncodeFullError<'vir, E>>>()?,
                );
                let goto_otherwise =
                    self.current_block_succs.as_ref().unwrap()[&targets.otherwise()];

                let otherwise_succ_idx = goto_targets.len();
                let mut otherwise_stmts =
                    self.collect_pcs_succ_at(otherwise_succ_idx, targets.otherwise())?;
                otherwise_stmts.push(self.set_from_to_flag(location.block, targets.otherwise()));

                let discr_ex = discr_ty.snap_to_prim(
                    self.encode_operand_snap(discr, &None)
                        .unwrap()
                        .downcast_ty(),
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
                let wand_packages = self.package_wands(borrows)?;
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
                let terminator_label = self.vcx.mk_terminator_label(
                    self.current_block.unwrap().as_usize(),
                    self.current_block_pres.as_ref().unwrap().iter().copied(),
                );
                self.encoded_blocks.push(
                    self.vcx.mk_cfg_block(
                        self.current_block_label.replace(terminator_label).unwrap(),
                        &[],
                        self.vcx
                            .alloc_slice(&self.current_stmts.replace(Vec::new()).unwrap()),
                        self.vcx.mk_goto_stmt(terminator_label),
                    ),
                );

                let (func_def_id, caller_substs, is_pure) = self.get_call_data(func);
                // A call whose span comes from a macro expansion (e.g. the
                // `core::panicking::panic` call inside a failing `assert!`)
                // was not written by the user, so reporting "precondition
                // might not hold" at the expanded fragment is confusing: no
                // visible call exists there. Report at the macro invocation
                // that produced the call, naming the actually-called function.
                let verification_error = if span.from_expansion() {
                    let name = self.vcx.tcx().def_path_str(func_def_id);
                    let message = format!(
                        "precondition of `{name}` (called by this macro expansion) might not hold"
                    );
                    PrustiError::verification(message, span.source_callsite().into())
                } else {
                    PrustiError::verification("precondition might not hold", span.into())
                };

                let dest = self
                    .encode_place(Place::from(*destination))
                    .expr
                    .expect_predicate();
                self.vcx.with_span(span, |vcx| {
                    let pure =
                        self.pure_call_result(func_def_id, caller_substs, args, is_pure, span)?;
                    if let Some((can_fail, pure)) = pure {
                        self.wandless_calls.insert(self.current_block.unwrap());
                        let return_ty = destination.ty(self.local_decls, self.vcx.tcx()).ty;
                        let assign_stmt = self
                            .ty_use_impure(return_ty)
                            .apply_method_assign(self.vcx, dest, pure);
                        if can_fail {
                            vcx.handle_error(
                                "application.precondition:assertion.false",
                                move |reason_span_opt| {
                                    let mut error = verification_error.clone();
                                    if let Some(reason_span) = reason_span_opt {
                                        error.add_note_mut(
                                            "the failing precondition is here",
                                            Some(reason_span.into()),
                                        );
                                    }
                                    Some(vec![error])
                                },
                            );
                        }
                        self.stmt(assign_stmt);
                    } else {
                        let Ok(func_out) = self.deps.require_dep::<encoders::MethodCallEnc>(
                            CallTaskDescription::new(self.def_id, caller_substs, func_def_id),
                        ) else {
                            self.current_terminator = Some(
                                self.vcx
                                    .mk_dummy_stmt(vir::vir_format!(self.vcx, "recursion",)),
                            );
                            return Ok(());
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
                                let mut error = verification_error.clone();
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
                    }
                    Ok(())
                })?;

                match *target {
                    Some(target) => {
                        self.pcs_succ_to(target)?;
                        let set_flag = self.set_from_to_flag(location.block, target);
                        self.stmt(set_flag);

                        self.vcx
                            .mk_goto_stmt(self.current_block_succs.as_ref().unwrap()[&target])
                    }
                    None => {
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
                    }
                }
            }
            mir::TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                ..
            } => {
                let enc = self
                    .encode_operand_snap(cond, &None)?
                    .downcast_ty::<vir::Bool>();
                let expected = self
                    .vcx
                    .mk_const_expr(vir::ConstData::Bool(*expected))
                    .downcast_ty();
                let assert = self.vcx.mk_eq_expr(enc, expected);
                let error_msg = match **msg {
                    mir::AssertMessage::BoundsCheck { .. } => Some("bounds check may fail"),
                    mir::AssertMessage::Overflow(..) | mir::AssertMessage::OverflowNeg(..)
                        if !config::check_overflows() =>
                    {
                        // If we are not checking for overflows, encode an overflow-checking
                        // assertion as an assume instead.
                        None
                    }
                    mir::AssertMessage::Overflow(..) | mir::AssertMessage::OverflowNeg(..) => {
                        Some("operation may overflow")
                    }
                    mir::AssertMessage::DivisionByZero(..)
                    | mir::AssertMessage::RemainderByZero(..) => Some("division by zero may occur"),
                    mir::AssertMessage::ResumedAfterReturn(..) => {
                        Some("execution may continue after return")
                    }
                    mir::AssertMessage::ResumedAfterPanic(..) => {
                        Some("execution may continue after panic")
                    }
                    mir::AssertMessage::MisalignedPointerDereference { .. } => {
                        Some("misaligned pointer may be dereferenced")
                    }
                    mir::AssertKind::ResumedAfterDrop(..) => {
                        Some("execution may continue after drop")
                    }
                    mir::AssertKind::NullPointerDereference => {
                        Some("null pointer may be dereferenced")
                    }
                    mir::AssertKind::InvalidEnumConstruction(..) => {
                        Some("invalid enum construction may occur")
                    }
                };
                if let Some(error_msg) = error_msg {
                    self.vcx.with_span(span, |vcx| {
                        vcx.handle_error("exhale.failed:assertion.false", move |_| {
                            Some(vec![PrustiError::verification(error_msg, span.into())])
                        });
                        self.stmt(self.vcx.mk_exhale_stmt(assert));
                    });
                } else {
                    self.stmt(self.vcx.mk_inhale_stmt(assert));
                }
                // The check is the terminator's main effect, emitted before
                // the deferred `PostMain` re-pack, which may fold the place
                // the condition projects into.
                self.pcs_succ_to(*target)?;
                let set_flag = self.set_from_to_flag(location.block, *target);
                self.stmt(set_flag);
                self.vcx
                    .mk_goto_stmt(self.current_block_succs.as_ref().unwrap()[target])
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
        assert!(self.current_terminator.replace(terminator).is_none());
        Ok(())
    }

    fn pure_call_result(
        &mut self,
        func_def_id: DefId,
        caller_substs: ty::GenericArgsRef<'vir>,
        args: &[Spanned<mir::Operand<'vir>>],
        is_pure: bool,
        span: Span,
    ) -> Result<Option<(bool, vir::ExprSnap<'vir>)>, EncodeFullError<'vir, E>> {
        // The bodiless `ptr_metadata` intrinsic is only lowered to
        // `UnOp::PtrMetadata` in optimized MIR; do the lowering here.
        let intrinsic = self.vcx.tcx().intrinsic(func_def_id);
        let intrinsic = intrinsic.and_then(RustcIntrinsic::from_intrinsic);
        Ok(if let Some(intrinsic) = intrinsic {
            Some((
                false,
                self.encode_intrinsic(intrinsic, caller_substs, args, &None)?,
            ))
        } else if let Some(builtin) = PrustiBuiltin::new(func_def_id, self.gargs(caller_substs)) {
            // A `prusti_contracts` builtin used in executable code
            // (e.g. `Int::from(2) + Int::from(3)`): encode it with
            // the shared operand-based encoding and assign the
            // resulting ghost snapshot into the destination. The
            // spec-only builtins (those gated behind the `prusti`
            // feature) are rejected, except in ghost code (the inline
            // bodies of `ghost!` blocks), where all non-`Spec` builtins
            // are allowed.
            let in_ghost_code = self
                .spec_blocks
                .ghost
                .code
                .contains(&self.current_block.unwrap());
            if builtin.is_spec_only()
                && (!in_ghost_code || matches!(builtin, PrustiBuiltin::Spec(_)))
            {
                return Err(self.unsupported_rvalue(
                    format!(
                        "`prusti_contracts` builtin {builtin:?} cannot be used in executable code"
                    ),
                    span,
                ));
            }
            let expr = self
                .encode_prusti_builtin(
                    builtin,
                    func_def_id,
                    self.gargs(caller_substs),
                    args,
                    span,
                    &None,
                )?
                .unwrap();
            Some((false, expr))
        } else if is_pure {
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
                        self.encode_operand_snap(&arg.node, &None).unwrap()
                    })
                })
                .collect::<Vec<_>>();
            Some((true, pure_func.call_impure(snap_args)))
        } else {
            None
        })
    }
}

impl<'vir, 'enc, E: TaskEncoder> PureRvalueEnc<'vir> for ImpureEncVisitor<'vir, 'enc, E> {
    type Encoder = E;
    type EncodePlaceCtxt = OperandSnaps<'vir>;
    const PURE: bool = false;
    type ExprCurr = ();
    type ExprNext = !;
    fn context(&self) -> GParams<'vir> {
        // Impure bodies are encoded at identity substs, so the function's own
        // context is the body's context.
        self.def_id.into()
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
        let ty_task = RustTyDecomposition::from_ty(ty, self.def_id);
        self.deps.require_dep::<TyUsePureEnc>(ty_task).unwrap()
    }

    fn encode_operand_snap(
        &mut self,
        operand: &mir::Operand<'vir>,
        operand_snaps: &Self::EncodePlaceCtxt,
    ) -> Result<vir::ExprSnap<'vir>, EncodeFullError<'vir, E>> {
        // While a statement's effect is encoded, every place operand must
        // have been captured by [Self::capture_operand_snaps]. In particular,
        // `Move` operands were already consumed at capture time (snapshot
        // temporary plus predicate exhale) and must not be consumed again.
        if let Some(operand_snaps) = operand_snaps
            && let Some(place) = operand.place()
        {
            let snap = operand_snaps.get(&place).unwrap_or_else(|| {
                panic!("operand {operand:?} was not captured for the current statement")
            });
            return Ok(*snap);
        }
        match operand {
            mir::Operand::Move(_) => self.capture_operand_snap(operand),
            _ => self.encode_operand_snap_immediate(operand),
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
