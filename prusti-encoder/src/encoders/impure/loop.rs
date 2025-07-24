use pcg::{
    borrow_pcg::region_projection::{
        MaybeRemoteRegionProjectionBase, RegionProjection, RegionProjectionBaseLike,
    },
    free_pcs::PcgBasicBlock,
    pcg::{EvalStmtPhase, PCGNode},
    r#loop::LoopId,
    utils::{maybe_old::MaybeOldPlace, maybe_remote::MaybeRemotePlace, Place, SnapshotLocation},
};
use prusti_rustc_interface::middle::mir;

use task_encoder::TaskEncoder;
use vir::{CastType, Reify};

use crate::encoders::{
    indirect::{IndirectKey, IndirectPredicatesEnc},
    rust_ty_predicates::{RustTyPredicatesEnc, RustTyPredicatesEncOutputRef},
    ImpureEncVisitor,
};

pub(super) enum WandOldOuter<'vir> {
    LetBind(Vec<(&'vir str, vir::ExprSnap<'vir>)>),
    Label(Option<&'vir str>),
}

impl<'vir, 'enc, E: TaskEncoder> ImpureEncVisitor<'vir, 'enc, E> {
    /// Calculate invariant at loop head
    pub(crate) fn get_loop_inv(
        &mut self,
        _lh: LoopId,
        cfpcs: &PcgBasicBlock<'vir>,
    ) -> &'vir [vir::ExprBool<'vir>] {
        let mut inv = Vec::new();
        let start = &cfpcs.statements[0];
        let state = &start.states[EvalStmtPhase::PreOperands];
        // let borrows = &*start.borrows[EvalStmtPhase::PreOperands];
        // self.stmt(self.vcx.mk_comment_stmt(
        //     vir::vir_format!(self.vcx, "_borrows: {:#?}", borrows),
        // ));
        for cap_local in state.owned_pcg().locals().iter() {
            if cap_local.is_unallocated() {
                continue;
            }
            let cap = cap_local.get_allocated();
            for place in cap.leaves(self.pcg_ctxt()).iter() {
                if !state.capabilities().is_exclusive(*place) {
                    continue;
                }
                let (place_res, snap, _, _) = self.encode_place_snap(*place);
                let ty = (*place).ty(self.pcg_ctxt());
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty.ty).unwrap();
                let pred = ty_out.ref_to_pred(self.vcx, place_res.expr, None);
                inv.push(pred);

                let regions = ty.ty.walk().flat_map(IndirectKey::from_generic_arg);
                for region in regions {
                    let indirect = self
                        .deps
                        .require_ref::<IndirectPredicatesEnc>((ty.ty, region))
                        .unwrap();
                    inv.extend(
                        indirect
                            .covariant
                            .into_iter()
                            .map(|expr| expr.reify(self.vcx, snap)),
                    );
                }
            }
        }
        for (_edge, inputs, outputs) in Self::get_abstraction_edges(state.borrow_pcg().graph()) {
            let mut let_bind = WandOldOuter::LetBind(Vec::new());
            let mut wand_rhs = Vec::new();
            for i in inputs {
                self.encode_pcg_node(&i, &mut wand_rhs, &mut let_bind);
            }
            let mut wand_lhs = Vec::new();
            for i in outputs {
                let i = match *i {
                    PCGNode::RegionProjection(region_projection) => region_projection,
                    PCGNode::Place(_) => unreachable!(),
                };
                let exprs = self.encode_region_projection(i, &mut let_bind);
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
            for (ident, expr) in let_bind {
                wand = self.vcx.mk_let_expr(ident, expr, wand);
            }
            inv.push(wand);
        }
        self.vcx.alloc_slice(&inv)
    }

    pub(super) fn encode_pcg_node<T: RegionProjectionBaseLike<'vir>>(
        &mut self,
        node: &PCGNode<'vir, MaybeRemotePlace<'vir>, T>,
        wand_rhs: &mut Vec<vir::ExprBool<'vir>>,
        old_outer: &mut WandOldOuter<'vir>,
    ) {
        match node {
            PCGNode::Place(MaybeRemotePlace::Remote(_)) => unreachable!(),
            PCGNode::Place(place @ MaybeRemotePlace::Local(_)) => {
                let p = Self::get_place(*place);
                let ty = (*p).ty(self.local_decls, self.vcx.tcx());
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty.ty).unwrap();
                let p = self.encode_place(p);
                let p = self.configure_old(*place, p.expr, old_outer);

                let pred = ty_out.ref_to_pred(self.vcx, p, None);
                wand_rhs.push(pred);
            }
            PCGNode::RegionProjection(r) => {
                let exprs = self.encode_region_projection(*r, old_outer);
                wand_rhs.extend(exprs);
            }
        }
    }

    pub(super) fn encode_region_projection<T: RegionProjectionBaseLike<'vir>>(
        &mut self,
        r: RegionProjection<'vir, T>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> Vec<vir::ExprBool<'vir>> {
        let place = r.place().to_maybe_remote_region_projection_base();
        let (place_snap, ty, _) = match place {
            MaybeRemoteRegionProjectionBase::Place(p) => {
                self.encode_maybe_remote_place_snap(p, old_outer)
            }
            MaybeRemoteRegionProjectionBase::Const(c) => todo!("{c:?}"),
        };
        let mut regions = ty.ty.walk().flat_map(IndirectKey::from_generic_arg);
        let region = regions.next().unwrap();
        // TODO:
        assert!(
            regions.next().is_none(),
            "multiple regions in a type not supported ({:?})",
            ty.ty
        );
        let indirect = self
            .deps
            .require_ref::<IndirectPredicatesEnc>((ty.ty, region))
            .unwrap();
        indirect
            .covariant
            .into_iter()
            .map(|expr| expr.reify(self.vcx, place_snap))
            .collect::<Vec<_>>()
    }

    fn get_place(place: MaybeRemotePlace<'vir>) -> Place<'vir> {
        match place {
            MaybeRemotePlace::Local(MaybeOldPlace::Current { place }) => place,
            MaybeRemotePlace::Local(MaybeOldPlace::OldPlace(place)) => place.place(),
            MaybeRemotePlace::Remote(r) => r.assigned_local().into(),
        }
    }

    fn encode_maybe_remote_place_snap(
        &mut self,
        place: MaybeRemotePlace<'vir>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> (
        vir::ExprSnap<'vir>,
        mir::tcx::PlaceTy<'vir>,
        RustTyPredicatesEncOutputRef<'vir>,
    ) {
        let p = Self::get_place(place);
        let (_, place_snap, ty, ty_out) = self.encode_place_snap(p);
        let place_snap = self.configure_old(place, place_snap, old_outer);
        (place_snap, ty, ty_out)
    }

    fn configure_old<T: vir::CompType>(
        &mut self,
        place: MaybeRemotePlace,
        expr: vir::Expr<'vir, T>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> vir::Expr<'vir, T> {
        match place {
            MaybeRemotePlace::Local(MaybeOldPlace::Current { .. }) => {
                self.mk_wand_outer(expr, old_outer)
            }
            MaybeRemotePlace::Local(MaybeOldPlace::OldPlace(place)) => {
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
        if let SnapshotLocation::Start(bb) | SnapshotLocation::Loop(bb) = at {
            return vir::OldLabel::Block(vir::CfgBlockLabelData::BasicBlock(bb.as_usize()));
        }
        let label_identifier = match at {
            SnapshotLocation::Start(_) => "start",
            SnapshotLocation::Prepare(_) => "prepare",
            SnapshotLocation::BeforeCollapse(_) => "before_collapse",
            SnapshotLocation::Mid(_) => "mid",
            SnapshotLocation::After(_) => "after",
            SnapshotLocation::Loop(_) => "loop",
            SnapshotLocation::BeforeRefReassignment(_) => "before_ref_reassignment",
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

    fn mk_wand_outer<T: vir::CompType>(
        &mut self,
        expr: vir::Expr<'vir, T>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> vir::Expr<'vir, T> {
        match old_outer {
            WandOldOuter::LetBind(let_bind) => {
                let ident = vir::vir_format!(self.vcx, "_snap{}", let_bind.len());
                // TODO: this is sometimes `Ref` type?
                let_bind.push((ident, expr.inner_cast_ty()));
                self.vcx.mk_local_ex(ident, expr.ty())
            }
            WandOldOuter::Label(label) => {
                let label = *label.get_or_insert_with(|| self.new_label("outer_package"));
                self.vcx.mk_local_labelled_old_expr(expr, label)
            }
        }
    }
}
