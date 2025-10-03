use pcg::{
    borrow_pcg::region_projection::{
        LifetimeProjection, PcgLifetimeProjectionBase, PcgLifetimeProjectionBaseLike,
    },
    r#loop::PlaceUsages,
    pcg::{EvalStmtPhase, PcgNode},
    results::PcgBasicBlock,
    utils::{
        HasCompilerCtxt, Place, SnapshotLocation, maybe_old::MaybeLabelledPlace,
        maybe_remote::MaybeRemotePlace,
    },
};
use prusti_rustc_interface::middle::mir;

use task_encoder::TaskEncoder;
use vir::Reify;

use crate::encoders::{
    ImpureEncVisitor, TyUseImpureEnc,
    ty::{RustTyDecomposition, indirect::IndirectPredicatesEnc, use_impure::TyUseImpure},
};

pub(super) enum WandOldOuter<'vir> {
    LetBind(Vec<LetBind<'vir>>),
    Label(Option<&'vir str>),
}

impl<'vir, 'enc, E: TaskEncoder> ImpureEncVisitor<'vir, 'enc, E> {
    /// Calculate invariant at loop head
    pub(crate) fn get_loop_inv<'a>(
        &mut self,
        cfpcs: &PcgBasicBlock<'_, 'vir>,
        loop_place_usages: &PlaceUsages<'vir>,
        ctxt: impl HasCompilerCtxt<'a, 'vir>,
    ) -> &'vir [vir::ExprBool<'vir>] {
        let mut inv = Vec::new();
        let start = &cfpcs.statements[0];
        let state = &start.states[EvalStmtPhase::PreOperands];
        let loop_invariant_place_capabilities =
            cfpcs.loop_invariant_place_capabilities(loop_place_usages, ctxt);

        for (place, capability) in loop_invariant_place_capabilities.iter() {
            if capability.is_write() {
                continue; // No permissions are encoded for places with write capabilities currently
            }
            let (place_res, _snap, _, _) = self.encode_place_snap(*place);
            let ty = (*place).ty(self.pcg_ctxt());
            let task = RustTyDecomposition::from_ty(ty.ty, self.def_id);
            let ty_out = self.deps.require_dep::<TyUseImpureEnc>(task).unwrap();
            let pred = ty_out.ref_to_pred(self.vcx, place_res.expr.expect_predicate(), None);
            inv.push(pred);
        }

        for (inputs, outputs) in self.get_abstraction_edges(state.borrow_pcg().graph()) {
            let mut let_bind = WandOldOuter::LetBind(Vec::new());
            let mut wand_rhs = Vec::new();
            for i in inputs {
                self.encode_pcg_node(&i, &mut wand_rhs, &mut let_bind);
            }
            let mut wand_lhs = Vec::new();
            for i in outputs {
                let i = match *i {
                    PcgNode::LifetimeProjection(region_projection) => region_projection,
                    PcgNode::Place(_) => unreachable!(),
                };
                let exprs = self.encode_lifetime_projection(i, &mut let_bind);
                wand_lhs.extend(exprs);
            }
            let wand = self.vcx.mk_wand(
                self.vcx.mk_conj(self.vcx.alloc_slice(&wand_lhs)),
                self.vcx.mk_conj(self.vcx.alloc_slice(&wand_rhs)),
            );
            let mut wand = self.vcx.mk_wand_expr(wand);
            let WandOldOuter::LetBind(let_bind) = let_bind else {
                unreachable!()
            };
            for lb in let_bind {
                wand = lb.map_or_else(
                    |(d, e)| self.vcx.mk_let_expr(d, e, wand),
                    |(d, e)| self.vcx.mk_let_expr(d, e, wand),
                );
            }
            inv.push(wand);
        }
        self.vcx.alloc_slice(&inv)
    }

    pub(super) fn encode_pcg_node<T: PcgLifetimeProjectionBaseLike<'vir>>(
        &mut self,
        node: &PcgNode<'vir, MaybeRemotePlace<'vir>, T>,
        wand_rhs: &mut Vec<vir::ExprBool<'vir>>,
        old_outer: &mut WandOldOuter<'vir>,
    ) {
        match node {
            PcgNode::Place(MaybeRemotePlace::Remote(_)) => unreachable!(),
            PcgNode::Place(place @ MaybeRemotePlace::Local(_)) => {
                let p = Self::get_place(*place);
                let ty = (*p).ty(self.local_decls, self.vcx.tcx());
                let task = RustTyDecomposition::from_ty(ty.ty, self.def_id);
                let ty_out = self.deps.require_dep::<TyUseImpureEnc>(task).unwrap();
                let p = self.encode_place(p);
                let p = self.configure_old(*place, p.expr.expect_predicate(), old_outer);

                let pred = ty_out.ref_to_pred(self.vcx, p, None);
                wand_rhs.push(pred);
            }
            PcgNode::LifetimeProjection(r) => {
                let exprs = self.encode_lifetime_projection(*r, old_outer);
                wand_rhs.extend(exprs);
            }
        }
    }

    pub(super) fn encode_lifetime_projection<T: PcgLifetimeProjectionBaseLike<'vir>>(
        &mut self,
        r: LifetimeProjection<'vir, T>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> Vec<vir::ExprBool<'vir>> {
        let place = r.base().to_pcg_lifetime_projection_base();
        let (place_snap, ty, _) = match place {
            PcgLifetimeProjectionBase::Place(p) => {
                self.encode_maybe_remote_place_snap(p, old_outer)
            }
            PcgLifetimeProjectionBase::Const(c) => todo!("{c:?}"),
        };
        let ty = RustTyDecomposition::from_ty(ty.ty, self.def_id);
        let indirect = self
            .deps
            .require_dep::<IndirectPredicatesEnc>(r.with_base(ty))
            .unwrap();
        indirect
            .predicate_applications
            .into_iter()
            .map(|expr| expr.reify(self.vcx, place_snap))
            .collect::<Vec<_>>()
    }

    fn get_place(place: MaybeRemotePlace<'vir>) -> Place<'vir> {
        match place {
            MaybeRemotePlace::Local(MaybeLabelledPlace::Current(place)) => place,
            MaybeRemotePlace::Local(MaybeLabelledPlace::Labelled(place)) => place.place(),
            MaybeRemotePlace::Remote(r) => r.assigned_local().into(),
        }
    }

    fn encode_maybe_remote_place_snap(
        &mut self,
        place: MaybeRemotePlace<'vir>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> (vir::ExprSnap<'vir>, mir::PlaceTy<'vir>, TyUseImpure<'vir>) {
        let p = Self::get_place(place);
        let (_, place_snap, ty, ty_out) = self.encode_place_snap(p);
        let place_snap = self.configure_old(place, place_snap, old_outer);
        (place_snap, ty, ty_out)
    }

    fn configure_old<T: SnapOrRef>(
        &mut self,
        place: MaybeRemotePlace,
        expr: vir::Expr<'vir, T>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> vir::Expr<'vir, T> {
        match place {
            MaybeRemotePlace::Local(MaybeLabelledPlace::Current { .. }) => {
                self.mk_wand_outer(expr, old_outer)
            }
            MaybeRemotePlace::Local(MaybeLabelledPlace::Labelled(place)) => {
                let label = Self::get_location_label(self.vcx, place.at());
                self.vcx.mk_old(expr, label)
            }
            MaybeRemotePlace::Remote(_) => self.vcx.mk_old_expr(expr),
        }
    }

    pub(crate) fn get_location_label(
        vcx: &'vir vir::VirCtxt<'vir>,
        at: SnapshotLocation,
    ) -> vir::OldLabel<'vir> {
        if let SnapshotLocation::BeforeJoin(bb) | SnapshotLocation::Loop(bb) = at {
            return vir::OldLabel::Block(vir::CfgBlockLabelData::BasicBlock(bb.as_usize()));
        }
        let label_identifier = match at {
            SnapshotLocation::Before(..) => "before",
            SnapshotLocation::After(..) => "after",
            SnapshotLocation::BeforeRefReassignment(..) => "before_ref_reassignment",
            SnapshotLocation::Loop(_) | SnapshotLocation::BeforeJoin(_) => unreachable!(),
        };
        let location = at.location();
        let label = vir::vir_format!(
            vcx,
            "_{}_{}_{}",
            label_identifier,
            location.block.index(),
            location.statement_index
        );
        vir::OldLabel::Label(label)
    }

    fn mk_wand_outer<T: SnapOrRef>(
        &mut self,
        expr: vir::Expr<'vir, T>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> vir::Expr<'vir, T> {
        match old_outer {
            WandOldOuter::LetBind(let_bind) => {
                let ident = vir::vir_format!(self.vcx, "_lb{}", let_bind.len());
                let decl = self.vcx.mk_local_decl(ident, expr.ty());
                let_bind.push(T::as_result(decl, expr));
                self.vcx.mk_local_ex(decl)
            }
            WandOldOuter::Label(label) => {
                let label = *label.get_or_insert_with(|| self.new_label("outer_package"));
                self.vcx.mk_local_labelled_old_expr(expr, label)
            }
        }
    }
}

type LetBind<'vir> = Result<
    (vir::LocalDeclSnap<'vir>, vir::ExprSnap<'vir>),
    (vir::LocalDeclRef<'vir>, vir::ExprRef<'vir>),
>;

trait SnapOrRef: vir::CompType {
    fn as_result<'vir>(d: vir::LocalDecl<'vir, Self>, e: vir::Expr<'vir, Self>) -> LetBind<'vir>;
}

impl SnapOrRef for vir::Snap {
    fn as_result<'vir>(d: vir::LocalDecl<'vir, Self>, e: vir::Expr<'vir, Self>) -> LetBind<'vir> {
        Ok((d, e))
    }
}

impl SnapOrRef for vir::Ref {
    fn as_result<'vir>(d: vir::LocalDecl<'vir, Self>, e: vir::Expr<'vir, Self>) -> LetBind<'vir> {
        Err((d, e))
    }
}
