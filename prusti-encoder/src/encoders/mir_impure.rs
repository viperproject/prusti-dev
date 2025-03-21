use std::collections::HashMap;

use pcs::{
    borrow_pcg::{
        action::BorrowPCGAction, borrow_pcg_expansion::BorrowPCGExpansion,
        edge::kind::BorrowPCGEdgeKind, unblock_graph::BorrowPCGUnblockAction,
    },
    combined_pcs::{EvalStmtPhase, PCGNode, PcgSuccessor},
    free_pcs::{CapabilityKind, PcgBasicBlock, PcgLocation, RepackOp},
    utils::{HasPlace, Place},
    FpcsOutput,
};
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{
        mir,
        ty::{self, GenericArgs, TyKind},
    },
    span::def_id::DefId,
    target::abi,
};
//use mir_ssa_analysis::{
//    SsaAnalysis,
//};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

pub struct MirImpureEnc;

#[derive(Clone, Debug)]
pub enum MirImpureEncError {
    // Unsupported,
}

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
        FunctionCallTaskDescription, MirBuiltinEnc,
    },
};

use super::{
    lifted::{
        cast::{CastArgs, CastToEnc},
        casters::CastTypeImpure,
        rust_ty_cast::RustTyCastersEnc,
        ty::{EncodeGenericsAsLifted, LiftedTyEnc},
    },
    rust_ty_predicates::RustTyPredicatesEnc,
    ConstEnc, MirMonoImpureEnc, MirPolyImpureEnc,
};

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
    //ssa_analysis: SsaAnalysis,
    pub fpcs_analysis: FpcsOutput<'enc, 'vir>,
    pub local_defs: crate::encoders::MirLocalDefEncOutput<'vir>,

    pub tmp_ctr: usize,

    // for the current basic block
    pub current_fpcs: Option<PcgBasicBlock<'vir>>,

    pub current_block_label: Option<vir::CfgBlockLabel<'vir>>,
    pub current_stmts: Option<Vec<vir::Stmt<'vir>>>,
    pub current_terminator: Option<vir::TerminatorStmt<'vir>>,

    pub encoded_blocks: Vec<vir::CfgBlock<'vir>>, // TODO: use IndexVec ?

    pub place_overrides: HashMap<mir::Place<'vir>, vir::Expr<'vir>>,
}

impl<'vir, E: TaskEncoder> PureFuncAppEnc<'vir, E> for ImpureEncVisitor<'vir, '_, E> {
    type EncodeOperandArgs = ();
    type Curr = !;
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
    ) -> vir::ExprGen<'vir, Self::Curr, Self::Next> {
        self.encode_operand_snap(operand).expr
    }

    fn monomorphize(&self) -> bool {
        self.monomorphize
    }
}

pub(crate) struct EncodePlaceResult<'vir> {
    pub(crate) expr: vir::Expr<'vir>,

    apply_casts: Vec<vir::Stmt<'vir>>,

    /// Statements to undo the impure casts that were made to access the place.
    /// If the place was only accessed to take a snapshot or copy (rather than a
    /// move), these statements should be applied in-order to restore
    /// permissions to the root of the place.
    undo_casts: Vec<vir::Stmt<'vir>>,
}

impl<'vir> EncodePlaceResult<'vir> {
    fn new(expr: vir::Expr<'vir>) -> Self {
        Self {
            expr,
            apply_casts: Vec::new(),
            undo_casts: Vec::new(),
        }
    }

    fn map_expr(&mut self, f: impl FnOnce(vir::Expr<'vir>) -> vir::Expr<'vir>) -> &mut Self {
        self.expr = f(self.expr);
        self
    }
}

macro_rules! comment {
    ($self:tt, $($arg:tt)*) => { $self.comment(
        vir::vir_format!($self.vcx, $($arg)*),
    ); };
}

impl<'vir, 'enc, E: TaskEncoder> ImpureEncVisitor<'vir, 'enc, E> {
    fn stmt(&mut self, stmt: vir::Stmt<'vir>) {
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
    fn collect_pcs_succ<'a>(&mut self, pcs: &'a PcgSuccessor<'vir>) -> Vec<vir::Stmt<'vir>> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        self.pcs_succ(pcs);
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
        expansion: BorrowPCGExpansion<'vir>,
        unfold: bool,
    ) {
        // TODO: code duplication with pcs_reborrow_expands
        if expansion.base().place().is_owned(self.fpcs_analysis.repacker()) {
            return;
        }
        let base = expansion.base();
        let place = base.place().place();
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

        let ref_p = self.encode_place(place).expr;
        let args = place_ty_out.ref_to_args(self.vcx, ref_p);
        let predicate = ref_to_pred.apply(self.vcx, args, None);
        if unfold {
            self.stmt(self.vcx.mk_unfold_stmt(predicate));
        } else {
            self.stmt(self.vcx.mk_fold_stmt(predicate));
        }
    }

    pub(crate) fn pcs_unblock_actions(
        &mut self,
        actions: &[BorrowPCGUnblockAction<'vir>],
        // location: Location,
    ) {
        use pcs::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
        for action in actions {
            // TODO: conditions (also in other PCS functions)
            match action.edge().kind() {
                BorrowPCGEdgeKind::BorrowPCGExpansion(expansion) => {
                    self.pcs_borrow_expansion(expansion.clone(), false);
                }
                // BorrowPCGEdgeKind::Borrow(borrow_edge) => todo!(),
                // BorrowPCGEdgeKind::Abstraction(abstraction_edge) => todo!(),
                // BorrowPCGEdgeKind::RegionProjectionMember(region_projection_member) => todo!(),
                _ => (),
            }
        }
    }

    pub(crate) fn pcs_actions(
        &mut self,
        actions: &[BorrowPCGAction<'vir>],
        // location: Location,
    ) {
        use pcs::borrow_pcg::action::BorrowPCGActionKind;
        for action in actions {
            comment!(self, "pcs_action: {:?}", action.kind());
            match action.kind() {
                //Weaken(Weaken<'tcx>),
                //Restore(RestoreCapability<'tcx>),
                //MakePlaceOld(Place<'tcx>),
                //SetLatest(Place<'tcx>, Location),
                //AddRegionProjectionMember(RegionProjectionMember<'tcx>, PathConditions),
                BorrowPCGActionKind::RemoveEdge(edge) => match edge.kind() {
                    BorrowPCGEdgeKind::BorrowPCGExpansion(expansion) => {
                        self.pcs_borrow_expansion(expansion.clone(), false);
                    }
                    _ => comment!(self, "(ignoring)"),
                },
                BorrowPCGActionKind::AddEdge {
                    edge,
                    for_exclusive: _,
                } => match edge.kind() {
                    BorrowPCGEdgeKind::BorrowPCGExpansion(expansion) => {
                        self.pcs_borrow_expansion(expansion.clone(), true);
                    }
                    _ => comment!(self, "(ignoring)"),
                },
                //RenamePlace {
                //    old: MaybeOldPlace<'tcx>,
                //    new: MaybeOldPlace<'tcx>,
                //},
                _ => comment!(self, "(ignoring)"),
            }
            /*
            match action.edge().kind() {
                BorrowPCGEdgeKind::Borrow(borrow) => {
                    if borrow.is_mut() {
                        /*
                        self.handle_removed_borrow(
                            borrow.blocked_place,
                            &borrow.assigned_place,
                            heap,
                            location,
                        );
                        */
                    }
                }
                BorrowPCGEdgeKind::BorrowPCGExpansion(expansion) => {
                    // BorrowPCGEdgeKind::DerefExpansion(deref_expansion)
                    /*
                    self.collapse_place_from(
                        deref_expansion.base(),
                        deref_expansion.expansion(self.repacker())[0],
                        heap,
                        location,
                    );
                    */
                }
                BorrowPCGEdgeKind::Abstraction(abstraction_edge) => match &abstraction_edge
                    .abstraction_type
                {
                    pcs::borrows::domain::AbstractionType::FunctionCall(c) => {
                        // A snapshot may not exist if the call is specification "ghost" code, e.g. old()
                        // statements applied to mutable refs in Prusti.
                        /*
                        if let Some(snapshot) = function_call_snapshots.get_snapshot(&c.location())
                        {
                            for edge in c.edges() {
                                for input in edge.inputs() {
                                    for output in edge.outputs() {
                                        let input = input.as_region_projection().unwrap();
                                        let idx =
                                            snapshot.index_of_arg_local(input.local().unwrap());
                                        let input_place = match input.deref(self.repacker()) {
                                            Some(place) => place,
                                            None => {
                                                // TODO: region projection
                                                continue;
                                            }
                                        };
                                        let output_place = match output.deref(self.repacker()) {
                                            Some(place) => place,
                                            None => {
                                                // TODO: region projection
                                                continue;
                                            }
                                        };
                                        let value = self.arena.mk_backwards_fn(BackwardsFn::new(
                                            self.arena.tcx,
                                            c.def_id(),
                                            c.substs(),
                                            Some(self.def_id.into()),
                                            snapshot.args(),
                                            self.arena.mk_ref(
                                                self.encode_maybe_old_place::<LookupGet, _>(
                                                    heap.0,
                                                    &output_place,
                                                ),
                                                Mutability::Mut,
                                            ),
                                            Local::from_usize(idx + 1),
                                        ));
                                        assert!(!snapshot
                                            .arg(idx)
                                            .kind
                                            .ty(self.tcx)
                                            .rust_ty()
                                            .is_primitive());
                                        assert_eq!(
                                            value.ty(self.tcx),
                                            snapshot.arg(idx).ty(self.tcx)
                                        );
                                        heap.insert_maybe_old_place(
                                            input_place,
                                            self.arena.mk_projection(ProjectionElem::Deref, value),
                                        );
                                    }
                                }
                            }
                        }
                           */
                    }
                    _ => {
                        // TODO: loops
                    }
                },
                BorrowPCGEdgeKind::RegionProjectionMember(region_projection_member) => {
                    /*
                    for input in region_projection_member.inputs().iter() {
                        if let Ok(place) = TryInto::<MaybeOldPlace<'tcx>>::try_into(*input) {
                            heap.insert(
                                place,
                                self.mk_fresh_symvar(place.ty(self.repacker()).ty),
                                location,
                            );
                        }
                    }
                    */
                }
            }
            */
        }
    }

    fn pcs_repacks<'a>(&mut self, repacks: impl Iterator<Item = &'a RepackOp<'vir>>)
    where
        'vir: 'a,
    {
        for &repack_op in repacks {
            comment!(self, "pcs_repack: {repack_op:?}");
            match repack_op {
                RepackOp::Expand(place, _target, capability_kind)
                | RepackOp::Collapse(place, _target, capability_kind) => {
                    if matches!(capability_kind, CapabilityKind::Write) {
                        // Collapsing an already exhaled place is a no-op
                        // TODO: unless it's through a Ref I imagine?
                        assert!(matches!(repack_op, RepackOp::Collapse(..)));
                        return;
                    }
                    let place_ty = (*place).ty(self.local_decls, self.vcx.tcx());
                    let place_ty_out = self
                        .deps
                        .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                        .unwrap();
                    let ref_to_pred = place_ty_out
                        .generic_predicate
                        .expect_pred_variant_opt(place_ty.variant_index);

                    let place_enc = self.encode_place(place);
                    let args = place_ty_out.ref_to_args(self.vcx, place_enc.expr);
                    let predicate = ref_to_pred.apply(self.vcx, args, None);
                    if matches!(repack_op, pcs::free_pcs::RepackOp::Expand(..)) {
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
                        self.stmts(place_enc.apply_casts);
                        self.stmt(self.vcx.mk_unfold_stmt(predicate));
                    } else {
                        self.stmt(self.vcx.mk_fold_stmt(predicate));
                        self.stmts(place_enc.undo_casts);
                    }
                }
                RepackOp::Weaken(place, CapabilityKind::Exclusive, CapabilityKind::Write) => {
                    let place_ty = (*place).ty(self.local_decls, self.vcx.tcx());
                    assert!(place_ty.variant_index.is_none());

                    let place_ty_out = self
                        .deps
                        .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                        .unwrap();

                    let place_enc = self.encode_place(place);
                    comment!(self, "exhale due to Weaken(E, W)");
                    self.stmts(place_enc.apply_casts);
                    self.stmt(self.vcx.mk_exhale_stmt(place_ty_out.ref_to_pred(
                        self.vcx,
                        place_enc.expr,
                        None,
                    )));
                }
                ignored_op @ (RepackOp::RegainLoanedCapability(..)
                | RepackOp::Weaken(
                    _,
                    CapabilityKind::Exclusive,
                    CapabilityKind::Read,
                )) => {
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
    }

    pub(crate) fn pcs_reborrow_expands(
        &mut self,
        expands: Vec<BorrowPCGExpansion<'vir>>,
        // location: Location,
    ) {
        // TODO: Explain why owned expansions don't need to be handled
        let expands = expands
            .into_iter()
            .filter(|expansion| !expansion.base().place().is_owned(self.fpcs_analysis.repacker()))
            .collect::<Vec<_>>();

        // Expand places with smaller projections first. For example, if f ->
        // {f.g} and f.g -> {f.g.h}, are expansions, we must expand f before
        // f.g.
        // TODO: do this
        //expands.sort_by_key(|ep| ep.expansion().base().place().projection().len());

        for ep in expands {
            let base = ep.base();
            let PCGNode::Place(place) = base else {
                continue;
            };
            let place = place.place();
            //if matches!(capability_kind, CapabilityKind::Write) {
            //    // Collapsing an already exhaled place is a no-op
            //    // TODO: unless it's through a Ref I imagine?
            //    assert!(matches!(repack_op, RepackOp::Collapse(..)));
            //    return;
            //}
            let place_ty = (*place).ty(self.local_decls, self.vcx.tcx());
            let place_ty_out = self
                .deps
                .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                .unwrap();
            let ref_to_pred = place_ty_out
                .generic_predicate
                .expect_pred_variant_opt(place_ty.variant_index);

            let ref_p = self.encode_place(place).expr;
            let args = place_ty_out.ref_to_args(self.vcx, ref_p);
            let predicate = ref_to_pred.apply(self.vcx, args, None);
            comment!(self, "unfolding in pcs_reborrow_expands");
            self.stmt(self.vcx.mk_unfold_stmt(predicate));

            /*
            let place = ep.base();
            let value = self.encode_maybe_old_place::<LookupGet, _>(heap.0, &place);

            self.explode_value(
                value,
                ep.expansion(self.fpcs_analysis.repacker()).into_iter(),
                heap,
                location,
            );
            */
        }
    }

    fn pcs_succ<'a>(&mut self, pcs: &'a PcgSuccessor<'vir>) {
        self.pcs_actions(pcs.borrow_ops().actions());
        self.pcs_repacks(pcs.owned_ops().iter());
    }

    fn undo_impure_casts(&mut self, result: EncodePlaceResult<'vir>) {
        assert!(result.undo_casts.is_empty());
        result.undo_casts.iter().for_each(|stmt| self.stmt(stmt));
    }

    fn encode_operand_snap(&mut self, operand: &mir::Operand<'vir>) -> EncodePlaceResult<'vir> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx());
        match operand {
            &mir::Operand::Move(source) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                let result = self.encode_place(Place::from(source));
                let snap_val = ty_out.ref_to_snap(self.vcx, result.expr);

                let tmp_exp = self.new_tmp(ty_out.snapshot()).1;
                self.stmts(result.apply_casts);
                self.stmt(self.vcx.mk_pure_assign_stmt(tmp_exp, snap_val));
                self.stmt(
                    self.vcx
                        .mk_exhale_stmt(ty_out.ref_to_pred(self.vcx, result.expr, None)),
                );
                EncodePlaceResult::new(tmp_exp)
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
                        (true, EncodePlaceResult::new(snap_val))
                    } else {
                        (
                            false,
                            EncodePlaceResult::new(self.local_defs.locals[place.local].local_ex),
                        )
                    };
                let mut last_apply_cast = None;
                let mut last_unapply_cast = None;
                for elem in place.projection {
                    if let Some(overridden) = self.place_overrides.get(&encoded_place) {
                        result.expr = overridden; // TODO: casts?
                    }
                    if crossed_ref {
                        use vir::Reify;
                        let (expr, _) = crate::encoders::mir_pure::encode_place_element(
                            self.vcx,
                            self.deps,
                            place_ty,
                            elem,
                            result.expr.lift(),
                            None,
                        );
                        result.expr = expr.reify(self.vcx, (self.def_id, &[]));
                    } else {
                        let (expr, apply_cast_stmt, unapply_cast_stmt) =
                            self.encode_place_element(place_ty, elem, result.expr);
                        result.expr = expr;
                        last_apply_cast = apply_cast_stmt;
                        last_unapply_cast = unapply_cast_stmt;
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
                        result.expr = ty_out.ref_to_snap(self.vcx, result.expr);
                        crossed_ref = true;
                    }
                }
                if let Some(overridden) = self.place_overrides.get(&encoded_place) {
                    result.expr = overridden; // TODO: casts?
                }
                if !crossed_ref {
                    let ty_out = self
                        .deps
                        .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                        .unwrap();
                    result.expr = ty_out.ref_to_snap(self.vcx, result.expr);
                }
                result.apply_casts.extend(last_apply_cast);
                result.undo_casts.extend(last_unapply_cast);
                result
            }
            mir::Operand::Constant(box constant) => EncodePlaceResult::new(
                self.deps
                    .require_local::<ConstEnc>((constant.const_, 0, self.def_id))
                    .unwrap(),
            ),
        }
    }

    fn encode_operand(&mut self, operand: &mir::Operand<'vir>) -> vir::Expr<'vir> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx());
        let (encode_place_result, ty_out) = match operand {
            &mir::Operand::Move(source) => return self.encode_place(Place::from(source)).expr,
            &mir::Operand::Copy(_source) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                (self.encode_operand_snap(operand), ty_out)
            }
            mir::Operand::Constant(box constant) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                let constant = self
                    .deps
                    .require_local::<ConstEnc>((constant.const_, 0, self.def_id))
                    .unwrap();
                (EncodePlaceResult::new(constant), ty_out)
            }
        };
        let tmp_exp: vir::Expr<'vir> = self.new_tmp(&vir::TypeData::Ref).1;
        self.stmt(ty_out.apply_method_assign(self.vcx, tmp_exp, encode_place_result.expr));
        self.undo_impure_casts(encode_place_result);
        tmp_exp
    }

    pub(crate) fn encode_place(&mut self, place: Place<'vir>) -> EncodePlaceResult<'vir> {
        let mut place_ty = mir::tcx::PlaceTy::from_ty(self.local_decls[place.local].ty);
        let mut encoded_place = mir::Place::from(place.local);
        let mut result = EncodePlaceResult::new(self.local_defs.locals[place.local].local_ex);
        // TODO: factor this out (duplication with pure encoder)?
        let mut last_apply_cast = None;
        let mut last_unapply_cast = None;
        for &elem in place.projection {
            if let Some(overridden) = self.place_overrides.get(&encoded_place) {
                result.expr = overridden; // TODO: casts?
            }
            let (expr, apply_cast_stmt, unapply_cast_stmt) =
                self.encode_place_element(place_ty, elem, result.expr);
            result.expr = expr;
            last_apply_cast = apply_cast_stmt;
            last_unapply_cast = unapply_cast_stmt;
            place_ty = place_ty.projection_ty(self.vcx.tcx(), elem);
            encoded_place = encoded_place.project_deeper(&[elem], self.vcx.tcx());
        }
        if let Some(overridden) = self.place_overrides.get(&encoded_place) {
            result.expr = overridden; // TODO: casts?
        }
        result.apply_casts.extend(last_apply_cast);
        result.undo_casts.extend(last_unapply_cast);
        result
    }

    // Returns a tuple (expr, unapply_cast), where `expr` is the encoded place element,
    // and `unapply_cast` is a statement to undo the impure cast that was made to access
    // it.
    fn encode_place_element(
        &mut self,
        place_ty: mir::tcx::PlaceTy<'vir>,
        elem: mir::PlaceElem<'vir>,
        expr: vir::Expr<'vir>,
    ) -> (
        vir::Expr<'vir>,
        Option<vir::Stmt<'vir>>,
        Option<vir::Stmt<'vir>>,
    ) {
        match elem {
            mir::ProjectionElem::Field(field_idx, ty) => {
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
                    .ref_to_args(self.vcx, instantiated_ty, expr);
                let proj_app = projection_p.apply(self.vcx, proj_args);
                let mut proj_cast_stmts_apply = None;
                let mut proj_cast_stmts_unapply = None;
                match place_ty.ty.kind() {
                    TyKind::Adt(def, _) => {
                        let variant =
                            def.variant(place_ty.variant_index.unwrap_or(abi::FIRST_VARIANT));
                        let generic_field_ty = variant.fields[field_idx].ty(
                            self.vcx.tcx(),
                            GenericArgs::identity_for_item(self.vcx.tcx(), def.did()),
                        );
                        let cast_args = CastArgs {
                            expected: ty,
                            actual: generic_field_ty,
                        };
                        if let Some(cast) = self
                            .deps
                            .require_ref::<CastToEnc<CastTypeImpure>>(cast_args)
                            .unwrap()
                            .apply_cast_if_necessary(self.vcx, proj_app)
                        {
                            proj_cast_stmts_apply = Some(cast);
                            proj_cast_stmts_unapply = self
                                .deps
                                .require_ref::<CastToEnc<CastTypeImpure>>(cast_args.reversed())
                                .unwrap()
                                .apply_cast_if_necessary(self.vcx, proj_app);
                        }
                    }
                    TyKind::Tuple(_) => {
                        if let Some(cast_stmts) = self
                            .deps
                            .require_local::<RustTyCastersEnc<CastTypeImpure>>(ty)
                            .unwrap()
                            .cast_to_concrete_if_possible(self.vcx, proj_app)
                        {
                            proj_cast_stmts_apply = Some(cast_stmts.apply_cast_stmt);
                            proj_cast_stmts_unapply = Some(cast_stmts.unapply_cast_stmt);
                        }
                    }
                    _ => {}
                }
                (proj_app, proj_cast_stmts_apply, proj_cast_stmts_unapply)
            }
            // TODO: should all variants start at the same `Ref`?
            mir::ProjectionElem::Downcast(..) => (expr, None, None),
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
                        let proj_args =
                            e_ty.generic_predicate
                                .ref_to_args(self.vcx, instantiated_ty, expr);
                        let proj_app = projection_p.apply(self.vcx, proj_args);
                        let mut proj_cast_stmts_apply = None;
                        let mut proj_cast_stmts_unapply = None;
                        if let Some(cast_stmts) = self
                            .deps
                            .require_local::<RustTyCastersEnc<CastTypeImpure>>(
                                place_ty.ty.expect_boxed_ty(),
                            )
                            .unwrap()
                            .cast_to_concrete_if_possible(self.vcx, proj_app)
                        {
                            proj_cast_stmts_apply = Some(cast_stmts.apply_cast_stmt);
                            proj_cast_stmts_unapply = Some(cast_stmts.unapply_cast_stmt);
                        }
                        (proj_app, proj_cast_stmts_apply, proj_cast_stmts_unapply)
                    }
                    ty::TyKind::Ref(_, inner_ty, ty::Mutability::Not) => {
                        // TODO: unfold? function? use snapshot?
                        let instantiated_ty = self
                            .deps
                            .require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(place_ty.ty)
                            .unwrap();
                        let deref_args =
                            e_ty.generic_predicate
                                .ref_to_args(self.vcx, instantiated_ty, expr);
                        let expr_deref = e_ty
                            .generic_predicate
                            .expect_immref()
                            .deref_func
                            .apply(self.vcx, deref_args.try_into().unwrap());
                        (expr_deref, None, None)
                    }
                    ty::TyKind::Ref(_, _, ty::Mutability::Mut) => {
                        // TODO: unfold? function? use snapshot?
                        let expr_deref = e_ty
                            .generic_predicate
                            .expect_mutref()
                            .deref_func
                            .apply(self.vcx, [expr]);
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
                        (expr_deref, None, None)
                    }
                    _ => unreachable!(),
                }
            }
            _ => todo!("Unsupported ProjectionElem {:?}", elem),
        }
    }

    fn new_tmp(&mut self, ty: &'vir vir::TypeData<'vir>) -> (vir::Local<'vir>, vir::Expr<'vir>) {
        let name = vir::vir_format!(self.vcx, "_tmp{}", self.tmp_ctr);
        self.tmp_ctr += 1;
        self.stmt(
            self.vcx
                .mk_local_decl_stmt(vir::vir_local_decl! { self.vcx; [name] : [ty] }, None),
        );
        let tmp = self.vcx.mk_local(name, ty);
        (tmp, self.vcx.mk_local_ex_local(tmp))
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
                    self.vcx
                        .mk_dummy_stmt(vir::vir_format!(self.vcx, "cleanup block",)),
                ),
            );
            return;
        }
        if !self.deps.check_cycle().is_ok() {
            return;
        }

        self.current_block_label = Some(self.vcx
            .alloc(vir::CfgBlockLabelData::BasicBlock(block.as_usize())));
        self.current_fpcs = Some(self.fpcs_analysis.get_all_for_bb(block).unwrap().unwrap());

        self.current_stmts = Some(Vec::with_capacity(
            data.statements.len(), // TODO: not exact?
        ));
        if ENCODE_REACH_BB {
            self.stmt(self.vcx.mk_pure_assign_stmt(
                self.vcx.mk_local_ex(
                    vir::vir_format!(self.vcx, "_reach_bb{}", block.as_usize()),
                    &vir::TypeData::Bool,
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
        self.encoded_blocks.push(
            self.vcx.mk_cfg_block(
                self.current_block_label.take().unwrap(),
                self.vcx.alloc_slice(&stmts),
                terminator,
            ),
        );
    }

    fn visit_statement(&mut self, statement: &mir::Statement<'vir>, location: mir::Location) {
        if !self.deps.check_cycle().is_ok() {
            return;
        }

        comment!(self, "[MIR] {location:?}: {statement:?}");

        let current_fpcs = self.current_fpcs.take().unwrap();
        // TODO: does this belong here?
        self.pcs_actions(current_fpcs.statements[location.statement_index].borrow_pcg_actions(EvalStmtPhase::PreOperands).actions());
        self.pcs_actions(current_fpcs.statements[location.statement_index].borrow_pcg_actions(EvalStmtPhase::PostOperands).actions());
        // TODO: move this to after getting operands, before assignment
        self.pcs_actions(current_fpcs.statements[location.statement_index].borrow_pcg_actions(EvalStmtPhase::PreMain).actions());
        self.pcs_actions(current_fpcs.statements[location.statement_index].borrow_pcg_actions(EvalStmtPhase::PostMain).actions());
        self.pcs_repacks(current_fpcs.statements[location.statement_index].repacks_start.iter());
        self.pcs_repacks(current_fpcs.statements[location.statement_index].repacks_middle.iter());
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
                        ).unwrap().function;
                        EncodePlaceResult::new(binop_function.apply(self.vcx, &[
                            self.encode_operand_snap(l).expr,
                            self.encode_operand_snap(r).expr,
                        ]))
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
                        ).unwrap().function;
                        EncodePlaceResult::new(unop_function.apply(self.vcx, &[self.encode_operand_snap(operand).expr]))
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
                        let field_snaps = fields.iter().map(|field| self.encode_operand_snap(field).expr).collect::<Vec<_>>();
                        let casted_args = ty_caster.apply_casts(self.vcx, field_snaps.into_iter());
                        EncodePlaceResult::new(sl.snap_data.field_snaps_to_snap.apply(self.vcx, self.vcx.alloc_slice(&casted_args)))
                    }
                    mir::Rvalue::Discriminant(place) => {
                        let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                        let place_ty = place.ty(self.local_decls, self.vcx.tcx());
                        let ty = self.deps.require_ref::<RustTyPredicatesEnc>(place_ty.ty).unwrap();
                        let place_expr = self.encode_place(Place::from(*place)).expr;

                        EncodePlaceResult::new(match ty.generic_predicate.get_enumlike().filter(|_| place_ty.variant_index.is_none()) {
                            Some(el) => {
                                let discr_ty = place_ty.ty.discriminant_ty(self.vcx.tcx());
                                let discr_ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(discr_ty).unwrap();
                                let discr_expr = discr_ty_out.ref_to_snap(self.vcx, el.as_ref().unwrap().discr.apply(self.vcx, [place_expr]));
                                self.vcx.mk_unfolding_expr(ty.ref_to_pred_app(self.vcx, place_expr, Some(self.vcx.mk_wildcard())), discr_expr)
                            }
                            None => {
                                // mir::Rvalue::Discriminant documents "Returns zero for types without discriminant"
                                let zero = self.vcx.mk_uint::<0>();
                                e_rvalue_ty.generic_predicate.expect_prim().prim_to_snap.apply(self.vcx, [zero])
                            }
                        })
                    }
                    mir::Rvalue::Ref(_reg, _kind, place) => {
                        EncodePlaceResult::new(match rvalue_ty.kind() {
                            TyKind::Ref(_, inner_ty, ty::Mutability::Not) => {
                                let inner_ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(*inner_ty).unwrap();
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
                                let snap = self.encode_operand_snap(&mir::Operand::Copy(*place)).expr;
                                let snap = cast.cast_to_generic_if_necessary(self.vcx, snap);
                                let inner = e_rvalue_ty.generic_predicate.expect_immref();
                                inner.snap_data.prim_to_snap.apply(self.vcx, [place_expr, snap])
                            }
                            TyKind::Ref(_, inner_ty, ty::Mutability::Mut) => {
                                let inner_ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(*inner_ty).unwrap();
                                let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                                let place_expr = self.encode_place(Place::from(*place)).expr;
                                let cast = self
                                    .deps
                                    .require_local::<RustTyCastersEnc<CastTypePure>>(*inner_ty)
                                    .unwrap();
                                let snap = inner_ty_out.generic_predicate.ref_to_snap.apply(self.vcx, &[place_expr]);
                                // The snapshot of the referenced value should be encoded as a generic `Param`
                                let snap = cast.cast_to_generic_if_necessary(self.vcx, snap);
                                let inner = e_rvalue_ty.generic_predicate.expect_mutref();
                                inner.snap_data.prim_to_snap.apply(self.vcx, [place_expr, snap])
                            }
                            _ => unreachable!(),
                        })
                    }

                    //mir::Rvalue::Discriminant(Place<'vir>) => {}
                    //mir::Rvalue::ShallowInitBox(Operand<'vir>, Ty<'vir>) => {}
                    //mir::Rvalue::CopyForDeref(Place<'vir>) => {}
                    other => {
                        tracing::error!("unsupported rvalue {other:?}");
                        EncodePlaceResult::new(self.vcx.mk_todo_expr(vir::vir_format!(self.vcx, "rvalue {rvalue:?}")))
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
                    rval_enc.expr,
                );

                self.stmts(rval_enc.apply_casts);
                self.stmt(method_assign_app);
                self.stmts(rval_enc.undo_casts);
                self.stmts(proj_enc.undo_casts);
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
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'vir>, location: mir::Location) {
        if !self.deps.check_cycle().is_ok() {
            return;
        }

        self.stmt(self.vcx.mk_comment_stmt(
            // TODO: also add bb and location for better debugging?
            vir::vir_format!(self.vcx, "{:?}", terminator.kind),
        ));
        let span = terminator.source_info.span;

        let current_fpcs = self.current_fpcs.take().unwrap();
        self.pcs_actions(current_fpcs.statements[location.statement_index].borrow_pcg_actions(EvalStmtPhase::PreOperands).actions());
        // TODO: move this to after getting operands, before assignment
        self.pcs_actions(current_fpcs.statements[location.statement_index].borrow_pcg_actions(EvalStmtPhase::PostOperands).actions());
        self.pcs_actions(current_fpcs.statements[location.statement_index].borrow_pcg_actions(EvalStmtPhase::PreMain).actions());
        self.pcs_actions(current_fpcs.statements[location.statement_index].borrow_pcg_actions(EvalStmtPhase::PostMain).actions());
        self.pcs_repacks(current_fpcs.statements[location.statement_index].repacks_start.iter());
        self.pcs_repacks(current_fpcs.statements[location.statement_index].repacks_middle.iter());
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
                self.pcs_succ(&current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX]);
                self.current_fpcs = Some(current_fpcs);

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
                            let extra_stmts = self.collect_pcs_succ(&current_fpcs.terminator.succs[idx]);
                            self.current_fpcs = Some(current_fpcs);

                            self.vcx.mk_goto_if_target(
                                discr_ty.expr_from_bits(discr_ty_rs, value),
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
                let otherwise_stmts = self.collect_pcs_succ(&current_fpcs.terminator.succs[otherwise_succ_idx]);
                self.current_fpcs = Some(current_fpcs);

                let discr_ex = discr_ty
                    .snap_to_prim
                    .apply(self.vcx, [self.encode_operand_snap(discr).expr]);
                self.vcx.mk_goto_if_stmt(
                    discr_ex, // self.vcx.mk_local_ex(discr_name),
                    goto_targets,
                    goto_otherwise,
                    self.vcx.alloc_slice(&otherwise_stmts),
                )
            }
            mir::TerminatorKind::Return => self
                .vcx
                .mk_goto_stmt(self.vcx.alloc(vir::CfgBlockLabelData::End)),
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
                        std::mem::replace(&mut self.current_block_label, Some(self.vcx
                            .alloc(vir::CfgBlockLabelData::BasicBlockTerminator(current_block))))
                            .unwrap(),
                        self.vcx.alloc_slice(&std::mem::replace(&mut self.current_stmts, Some(Vec::new())).unwrap()),
                        self
                            .vcx
                            .mk_goto_stmt(self.vcx.alloc(vir::CfgBlockLabelData::BasicBlockTerminator(current_block))),
                    ),
                );

                let (func_def_id, caller_substs) = self.get_def_id_and_caller_substs(func);
                let is_pure = crate::encoders::with_proc_spec(func_def_id, |spec| {
                    spec.kind.is_pure().unwrap_or_default()
                })
                .unwrap_or_default();

                let dest = self.encode_place(Place::from(*destination)).expr;

                let task = (func_def_id, self.def_id);
                let sig = self.vcx().tcx().fn_sig(func_def_id);
                let sig = if self.monomorphize {
                    let param_env = self.vcx().tcx().param_env(self.def_id);
                    self.vcx().tcx().instantiate_and_normalize_erasing_regions(
                        caller_substs,
                        param_env,
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

                    let mut method_args =
                        std::iter::once(dest).chain(method_in).collect::<Vec<_>>();
                    let mono = self.monomorphize;
                    let encoded_ty_args = self
                        .deps()
                        .require_local::<LiftedFuncAppTyParamsEnc>((mono, caller_substs))
                        .unwrap()
                        .iter()
                        .map(|ty| ty.expr(self.vcx()));

                    method_args.extend(encoded_ty_args);

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
                                    .alloc(func_out.method_ref.apply(self.vcx, &method_args)),
                            )),
                        );
                    });
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
                            self.current_fpcs.as_ref().unwrap().terminator.succs[REAL_TARGET_SUCC_IDX]
                                .block(),
                            target
                        );
                        let current_fpcs = self.current_fpcs.take().unwrap();
                        self.pcs_succ(&current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX]);
                        self.current_fpcs = Some(current_fpcs);

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
                self.pcs_succ(&current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX]);
                self.current_fpcs = Some(current_fpcs);

                let e_bool = self
                    .deps
                    .require_ref::<RustTyPredicatesEnc>(self.vcx.tcx().types.bool)
                    .unwrap();
                let enc = self.encode_operand_snap(cond).expr;
                let enc = e_bool
                    .generic_predicate
                    .expect_prim()
                    .snap_to_prim
                    .apply(self.vcx, [enc]);
                let expected = self.vcx.mk_const_expr(vir::ConstData::Bool(*expected));
                let assert = self
                    .vcx
                    .mk_bin_op_expr(vir::BinOpKind::CmpEq, enc, expected);
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
                    // mir::AssertMessage::NullPointerDereference => "",
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

                self.vcx.mk_goto_if_stmt(
                    enc,
                    self.vcx
                        .alloc_slice(&[self.vcx.mk_goto_if_target(expected, target_bb, &[])]),
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

            mir::TerminatorKind::Drop { target, .. } => self.vcx.mk_goto_stmt(
                self.vcx
                    .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
            ),

            unsupported_kind => self.vcx.mk_dummy_stmt(vir::vir_format!(
                self.vcx,
                "terminator {unsupported_kind:?}"
            )),
        };
        assert!(self.current_terminator.replace(terminator).is_none());
    }
}
