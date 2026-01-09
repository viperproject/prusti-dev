use pcg::utils::Place;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

use crate::encoders::{
    ConstEnc, MirBuiltinEnc, MirBuiltinEncTask, r#const::ConstEncTask, ty::use_pure::TyUsePure,
};
use prusti_rustc_interface::{
    abi,
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
};

#[allow(type_alias_bounds)]
type ExprResult<'vir, Enc: PureRvalueEnc<'vir>> = Result<
    vir::ExprGenSnap<'vir, Enc::ExprCurr, Enc::ExprNext>,
    EncodeFullError<'vir, Enc::Encoder>,
>;

pub(crate) struct EncodedCast<'vir, Enc: PureRvalueEnc<'vir> + ?Sized> {
    pub preconditions: Vec<vir::ExprGenBool<'vir, Enc::ExprCurr, Enc::ExprNext>>,
    pub expr: vir::ExprGenSnap<'vir, Enc::ExprCurr, Enc::ExprNext>,
}

pub(crate) trait PureRvalueEnc<'vir> {
    type Encoder: TaskEncoder + 'vir;
    type EncodePlaceCtxt;
    type ExprCurr;
    type ExprNext;
    fn def_id(&self) -> DefId;
    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir, Self::Encoder>;
    fn vcx(&self) -> &'vir vir::VirCtxt<'vir>;
    fn body(&self) -> &mir::Body<'vir>;
    fn ty_use_pure(&mut self, ty: ty::Ty<'vir>) -> TyUsePure<'vir>;

    /// Encodes the snapshot of an operand. In an impure context this may
    /// produce side-effects. Namely, encoding a `Move` operand will generate a
    /// statement that exhales a predicate.
    fn encode_operand_snap(
        &mut self,
        operand: &mir::Operand<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> ExprResult<'vir, Self>;

    fn encode_place_snap(
        &mut self,
        place: Place<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> vir::ExprGenSnap<'vir, Self::ExprCurr, Self::ExprNext>;

    fn encode_cast_snap<'slf>(
        &'slf mut self,
        kind: mir::CastKind,
        operand: &mir::Operand<'vir>,
        ty: ty::Ty<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> Result<EncodedCast<'vir, Self>, EncodeFullError<'vir, Self::Encoder>> {
        match kind {
            mir::CastKind::IntToInt => {
                let encoded_operand = self.encode_operand_snap(operand, ctxt)?;
                let from_ty = operand.ty(self.body(), self.vcx().tcx());
                let from_vir_ty = self.ty_use_pure(from_ty).expect_primitive().expect_native();
                let to_vir_ty = self.ty_use_pure(ty).expect_primitive();
                let from_prim = from_vir_ty.snap_to_prim.call()(encoded_operand.downcast_ty());
                let (to_bits, to_signed) = vir::VirCtxt::get_int_data(ty.kind());
                let (from_bits, from_signed) = vir::VirCtxt::get_int_data(from_ty.kind());

                let needs_min_check = match (from_signed, to_signed) {
                    (true, true) => from_bits > to_bits, // both signed, check required if target has fewer bits
                    (false, false) => false,             // both unsigned, no min check necessary
                    (false, true) => false, // unsigned to signed, no min check necessary
                    (true, false) => false, // signed to unsigned, `from` must be >= 0
                };

                let needs_max_check = match (from_signed, to_signed) {
                    (false, true) => from_bits >= to_bits, // unsigned to signed, must check unless target is bigger
                    _ => from_bits > to_bits, // otherwise check if target has fewer bits
                };

                let mut preconditions = Vec::new();
                if needs_min_check {
                    let to_min = self.vcx().get_min_int(ty.kind());
                    let min_check = self
                        .vcx()
                        .mk_bin_op_expr(
                            vir::BinOpKind::CmpGe,
                            from_prim.as_dyn(),
                            to_min.lazy().as_dyn(),
                        )
                        .downcast_ty::<vir::Bool>();
                    preconditions.push(min_check);
                }

                if needs_max_check {
                    let to_max = self.vcx().get_max_int(ty.kind());
                    let max_check = self
                        .vcx()
                        .mk_bin_op_expr(
                            vir::BinOpKind::CmpLe,
                            from_prim.as_dyn(),
                            to_max.lazy().as_dyn(),
                        )
                        .downcast_ty::<vir::Bool>();
                    preconditions.push(max_check);
                }
                Ok(EncodedCast {
                    preconditions,
                    expr: to_vir_ty.prim_to_snap.call()(from_prim).upcast_ty(),
                })
            }
            _ => todo!("cast kind {kind:?}"),
        }
    }

    fn encode_binop_snap(
        &mut self,
        rvalue_ty: ty::Ty<'vir>,
        op: mir::BinOp,
        l: &mir::Operand<'vir>,
        r: &mir::Operand<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> ExprResult<'vir, Self> {
        let encoded_l = self.encode_operand_snap(l, ctxt)?;
        let encoded_r = self.encode_operand_snap(r, ctxt)?;
        let l_ty = l.ty(self.body(), self.vcx().tcx());
        let r_ty = r.ty(self.body(), self.vcx().tcx());
        use crate::encoders::MirBuiltinEncTask::{BinOp, CheckedBinOp};
        let task = if op.is_overflowing() {
            CheckedBinOp(rvalue_ty, op, l_ty, r_ty)
        } else {
            BinOp(rvalue_ty, op, l_ty, r_ty)
        };
        let binop_function = self
            .deps()
            .require_ref::<MirBuiltinEnc>(task)
            .unwrap()
            .bin_op()
            .unwrap();
        Ok(binop_function.call()(encoded_l.downcast_ty(), encoded_r.downcast_ty()).upcast_ty())
    }

    fn encode_constant_snap(
        &mut self,
        constant: &mir::ConstOperand<'vir>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, Self::Encoder>> {
        let def_id = self.def_id();
        self.deps().require_dep::<ConstEnc>(ConstEncTask::Mir {
            const_: constant.const_,
            encoding_depth: 0,
            def_id,
            span: constant.span,
        })
    }

    fn encode_unary_op_snap(
        &mut self,
        rvalue_ty: ty::Ty<'vir>,
        op: mir::UnOp,
        operand: &mir::Operand<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> ExprResult<'vir, Self> {
        let encoded_operand = self.encode_operand_snap(operand, ctxt)?;
        let operand_ty = operand.ty(self.body(), self.vcx().tcx());
        let un_op_function = self
            .deps()
            .require_ref::<MirBuiltinEnc>(MirBuiltinEncTask::UnOp(rvalue_ty, op, operand_ty))
            .unwrap()
            .un_op()
            .unwrap();
        Ok(un_op_function.call()(encoded_operand.downcast_ty()).upcast_ty())
    }

    fn encode_aggregate_snap(
        &mut self,
        rvalue_ty: ty::Ty<'vir>,
        kind: &mir::AggregateKind<'vir>,
        fields: &IndexVec<abi::FieldIdx, mir::Operand<'vir>>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> ExprResult<'vir, Self> {
        let encoded_fields = fields
            .iter()
            .map(|field| self.encode_operand_snap(field, ctxt))
            .collect::<Result<Vec<_>, _>>()?;
        let e_rvalue_ty = self.ty_use_pure(rvalue_ty);
        let sl = match kind {
            mir::AggregateKind::Adt(_, vidx, _, _, _) => e_rvalue_ty.get_variant_any(*vidx),
            _ => e_rvalue_ty.expect_structlike(),
        };
        Ok(sl.field_snaps_to_snap(encoded_fields).upcast_ty())
    }

    fn encode_len_snap(
        &mut self,
        place: Place<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> vir::ExprGenSnap<'vir, Self::ExprCurr, Self::ExprNext> {
        let encoded_place = self.encode_place_snap(place, ctxt);
        let place_ty = (*place).ty(self.body(), self.vcx().tcx());
        let len_function = self
            .deps()
            .require_ref::<MirBuiltinEnc>(crate::encoders::MirBuiltinEncTask::Len(place_ty.ty))
            .unwrap()
            .len()
            .unwrap();
        len_function.call()(encoded_place.downcast_ty()).upcast_ty()
    }
}
