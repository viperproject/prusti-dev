use pcg::utils::Place;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

use crate::encoders::{
    ConstEnc, MirBuiltinBinOpEnc, MirBuiltinBinOpTask, MirBuiltinUnOpEnc, MirBuiltinUnOpTask,
    MirBuiltinUseCastEnc, MirBuiltinUseCastTask, PrustiBuiltin, PrustiBuiltinEnc,
    PrustiBuiltinTask,
    r#const::ConstEncTask,
    ty::{
        RustTyDecomposition,
        generics::{GArgs, GArgsTyEnc, GParams},
        use_pure::TyUsePure,
    },
};
use prusti_rustc_interface::{
    abi,
    index::IndexVec,
    middle::{mir, ty},
    span::{Span, def_id::DefId, source_map::Spanned, sym},
};

#[allow(type_alias_bounds)]
type ExprOutput<'vir, Enc: PureRvalueEnc<'vir>> =
    vir::ExprGenSnap<'vir, Enc::ExprCurr, Enc::ExprNext>;

#[allow(type_alias_bounds)]
type ExprResult<'vir, Enc: PureRvalueEnc<'vir>> =
    Result<ExprOutput<'vir, Enc>, EncodeFullError<'vir, Enc::Encoder>>;

#[allow(type_alias_bounds)]
type CastSnap<'vir, Enc: PureRvalueEnc<'vir>> = (
    Option<vir::StmtGen<'vir, Enc::ExprCurr, Enc::ExprNext>>,
    ExprOutput<'vir, Enc>,
);

#[derive(Debug, PartialEq, Eq)]
pub(super) enum RustcIntrinsic {
    PtrMetadata,
}

impl RustcIntrinsic {
    pub(super) fn from_intrinsic(intrinsic: ty::IntrinsicDef) -> Option<Self> {
        Some(match intrinsic.name {
            sym::ptr_metadata => RustcIntrinsic::PtrMetadata,
            _ => return None,
        })
    }
}

pub(crate) trait PureRvalueEnc<'vir> {
    type Encoder: TaskEncoder + 'vir;
    type EncodePlaceCtxt;
    type ExprCurr;
    type ExprNext;
    /// Whether this is the pure encoder: builtins in pure code use the
    /// *total* versions of the partial collection operations, since the
    /// (precondition-free) `f_` functions could never discharge their
    /// well-definedness obligations.
    const PURE: bool;
    /// The generic context of the body being encoded. For a body substituted
    /// with usage-site substs (pure/spec bodies), this is the caller's
    /// context, in which the substituted types live - not the encoded def's.
    fn context(&self) -> GParams<'vir>;
    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir, Self::Encoder>;
    fn vcx(&self) -> &'vir vir::VirCtxt<'vir>;
    fn body(&self) -> &mir::Body<'vir>;
    fn ty_use_pure(&mut self, ty: ty::Ty<'vir>) -> TyUsePure<'vir>;

    /// The pointer metadata for a freshly created reference of type `ref_ty`
    /// when no metadata is carried over from the referent place (i.e. a thin
    /// pointer to a sized referent): the snapshot of the referent's metadata
    /// type, which is `()` for all sized types, built with its regular
    /// (zero-field) constructor. Returns `None` for an unsized referent
    /// (slice/`dyn`), whose metadata cannot be conjured here and must instead
    /// be propagated from the wide pointer the place is reached through.
    fn thin_ptr_metadata(
        &mut self,
        ref_ty: ty::Ty<'vir>,
    ) -> Option<vir::ExprGenSnap<'vir, Self::ExprCurr, Self::ExprNext>> {
        let metadata_ty = ref_ty.pointee_metadata_ty_or_projection(self.vcx().tcx());
        self.ty_use_pure(metadata_ty)
            .zst_to_snap()
            .map(|m| m.upcast_ty())
    }

    /// Build an error for an unsupported feature reached during rvalue encoding.
    fn unsupported_rvalue(
        &self,
        message: String,
        span: Span,
    ) -> EncodeFullError<'vir, Self::Encoder> {
        EncodeFullError::DependencyError(vec![(
            <Self::Encoder as TaskEncoder>::ENCODER_NAME,
            message,
            vec![span],
        )])
    }

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

    fn encode_cast_snap(
        &mut self,
        rvalue_ty: ty::Ty<'vir>,
        kind: mir::CastKind,
        operand: &mir::Operand<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> Result<CastSnap<'vir, Self>, EncodeFullError<'vir, Self::Encoder>> {
        let encoded_operand = self.encode_operand_snap(operand, ctxt)?.downcast_ty();
        let operand_ty = operand.ty(self.body(), self.vcx().tcx());
        let rvalue_ty = RustTyDecomposition::from_ty(rvalue_ty, self.context());
        let operand_ty = RustTyDecomposition::from_ty(operand_ty, self.context());
        let cast_output =
            self.deps()
                .require_dep::<MirBuiltinUseCastEnc>(MirBuiltinUseCastTask::new(
                    rvalue_ty, kind, operand_ty,
                ))?;
        let cast = cast_output.cast(encoded_operand).upcast_ty();
        let cast_stmt = cast_output.unsize(encoded_operand);
        Ok((cast_stmt, cast))
    }

    fn encode_binop_snap(
        &mut self,
        rvalue_ty: ty::Ty<'vir>,
        op: mir::BinOp,
        l: &mir::Operand<'vir>,
        r: &mir::Operand<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
        span: Span,
    ) -> ExprResult<'vir, Self> {
        let l_ty = l.ty(self.body(), self.vcx().tcx());
        let r_ty = r.ty(self.body(), self.vcx().tcx());
        let l_ty = RustTyDecomposition::from_ty(l_ty, self.context());
        let r_ty = RustTyDecomposition::from_ty(r_ty, self.context());
        let rvalue_ty = RustTyDecomposition::from_ty(rvalue_ty, self.context());
        let task = MirBuiltinBinOpTask::new(rvalue_ty, op, l_ty, r_ty);
        let op = self
            .deps()
            .require_dep_spanned::<MirBuiltinBinOpEnc>(task, span)?;

        let encoded_l = self.encode_operand_snap(l, ctxt)?;
        let encoded_r = self.encode_operand_snap(r, ctxt)?;
        Ok(op.call()(encoded_l.downcast_ty(), encoded_r.downcast_ty()).upcast_ty())
    }

    fn encode_constant_snap(
        &mut self,
        constant: &mir::ConstOperand<'vir>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, Self::Encoder>> {
        let context = self.context();
        self.deps().require_dep::<ConstEnc>(ConstEncTask::Mir {
            const_: constant.const_,
            encoding_depth: 0,
            context,
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
        let operand_ty = RustTyDecomposition::from_ty(operand_ty, self.context());
        let rvalue_ty = RustTyDecomposition::from_ty(rvalue_ty, self.context());
        let un_op_function = self
            .deps()
            .require_dep::<MirBuiltinUnOpEnc>(MirBuiltinUnOpTask::new(rvalue_ty, op, operand_ty))?;
        Ok(un_op_function.call()(encoded_operand.downcast_ty()))
    }

    /// The generic arguments of a call from this encoder's body: `args`
    /// paired with the body's generic context.
    fn gargs(&self, args: ty::GenericArgsRef<'vir>) -> GArgs<'vir> {
        GArgs::new(self.context(), args)
    }

    /// Encodes a call to a `prusti_contracts` builtin. Returns `None` for the
    /// pure-only builtins (`forall`/`exists`/`spec_block`/mode markers), which
    /// the pure encoder handles itself.
    fn encode_prusti_builtin(
        &mut self,
        builtin: PrustiBuiltin,
        def_id: DefId,
        gargs: GArgs<'vir>,
        args: &[Spanned<mir::Operand<'vir>>],
        span: Span,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> Result<Option<ExprOutput<'vir, Self>>, EncodeFullError<'vir, Self::Encoder>> {
        if matches!(builtin, PrustiBuiltin::Spec(_)) {
            return Ok(None);
        }
        let is_pure = Self::PURE;
        let expr = self
            .deps()
            .require_dep::<PrustiBuiltinEnc>(PrustiBuiltinTask {
                builtin,
                def_id,
                args: gargs,
                is_pure,
                span: Some(span).filter(|_| !is_pure),
            })?;
        let operands = args
            .iter()
            .map(|arg| self.encode_operand_snap(&arg.node, ctxt))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Some(expr.apply(self.vcx(), &operands)))
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

    // TODO: this is removed in the latest rustc version
    fn encode_len_snap(
        &mut self,
        place: Place<'vir>,
        _ctxt: &Self::EncodePlaceCtxt,
    ) -> ExprResult<'vir, Self> {
        let place_ty = (*place).ty(self.body(), self.vcx().tcx());
        assert!(place_ty.variant_index.is_none());
        match place_ty.ty.kind() {
            ty::TyKind::Array(..) => {
                // An array's length is its (static) const generic argument.
                let decomp = RustTyDecomposition::from_ty(place_ty.ty, self.context());
                let generics = self.deps().require_dep::<GArgsTyEnc>(decomp.args)?;
                Ok(generics.get_const()[0].upcast_ty())
            }
            // A slice's length is its fat-pointer metadata, which is carried by the
            // (wide) reference the place is reached through, not by the slice place
            // itself; slice `.len()` is instead handled via `PrustiBuiltin::SliceLen`.
            ty::TyKind::Slice(..) => todo!("Rvalue::Len on a slice place"),
            kind => unreachable!("Rvalue::Len on non-array/slice type {kind:?}"),
        }
    }

    fn encode_intrinsic(
        &mut self,
        intrinsic: RustcIntrinsic,
        arg_tys: ty::GenericArgsRef<'vir>,
        args: &[Spanned<mir::Operand<'vir>>],
        ctxt: &Self::EncodePlaceCtxt,
    ) -> ExprResult<'vir, Self> {
        match intrinsic {
            // pub const fn ptr_metadata<P, M>(ptr: *const P) -> M
            RustcIntrinsic::PtrMetadata => {
                assert_eq!(arg_tys.len(), 2);
                assert_eq!(args.len(), 1);
                let dest_ty = arg_tys[1].expect_ty();
                self.encode_unary_op_snap(dest_ty, mir::UnOp::PtrMetadata, &args[0].node, ctxt)
            }
        }
    }
}
