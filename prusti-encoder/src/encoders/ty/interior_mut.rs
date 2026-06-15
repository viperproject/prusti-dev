use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, OutputRefAny, TaskEncoder};
use vir::CastType;

use crate::encoders::{
    FunctionCallEnc, TyUsePureEnc,
    custom::{PairUse, PairUseEnc},
    mir_fn::CallTaskDescription,
    ty::{
        RustTy, RustTyDatas, RustTyDecomposition,
        data::{EnumData, StructData, TyDatas, TySpecifics},
        generics::{GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc, ty_identity_expr},
        impure::{ImpureTyDatas, TyImpureEnc},
        pure::{PureTyDatas, TyPureEnc},
    },
};

#[derive(Debug, Clone, Copy)]
pub struct TyInteriorMutUseExpr<'vir> {
    func: vir::FunctionIdn<'vir, (vir::Ref, vir::Snap, vir::ManyTyVal, vir::ManyCSnap), vir::Set>,
    args: GArgsTy<'vir>,
}

impl<'vir> TyInteriorMutUseExpr<'vir> {
    pub fn get_all(
        &self,
        addr: vir::ExprRef<'vir>,
        snap: vir::ExprSnap<'vir>,
    ) -> vir::ExprSet<'vir> {
        (self.func)(addr, snap, self.args.get_ty(), self.args.get_const())
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TyInteriorMutError {
    NestedInteriorMut,
}

pub struct TyInteriorMutUseEnc;

impl TaskEncoder for TyInteriorMutUseEnc {
    task_encoder::encoder_cache!(TyInteriorMutUseEnc);
    const ENCODER_NAME: &'static str = "interior mutability use encoder";
    type TaskDescription<'vir> = RustTyDecomposition<'vir>;
    type OutputFullDependency<'vir> = TyInteriorMutUseExpr<'vir>;
    type EncodingError = TyInteriorMutError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let func = deps.require_ref::<TyInteriorMutEnc>(task_key.ty)?.0;
        let args = deps.require_dep::<GArgsTyEnc>(task_key.args)?;
        Ok(((), TyInteriorMutUseExpr { func, args }))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        TyInteriorMutEnc::emit_outputs(program);
        super::generics::interior_mut::InteriorMutGenericsEnc::emit_outputs(program);
    }
}

pub(super) struct TyInteriorMutEnc;

type InteriorMutFn<'vir> =
    vir::FunctionIdn<'vir, (vir::Ref, vir::Snap, vir::ManyTyVal, vir::ManyCSnap), vir::Set>;

#[derive(Debug, Clone, Copy)]
pub(super) struct TyInteriorMutRef<'vir>(pub(super) InteriorMutFn<'vir>);

impl<'vir> OutputRefAny for TyInteriorMutRef<'vir> {}

impl TaskEncoder for TyInteriorMutEnc {
    task_encoder::encoder_cache!(TyInteriorMutEnc);
    const ENCODER_NAME: &'static str = "interior mutability encoder";
    type TaskDescription<'vir> = RustTy<'vir>;

    type OutputRef<'vir> = TyInteriorMutRef<'vir>;
    type OutputFullLocal<'vir> = vir::Function<'vir>;

    type EncodingError = TyInteriorMutError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        // TODO: remove
        let task_key: &RustTy = task_key;
        vir::with_vcx(|vcx| {
            let tuple = deps
                .require_dep::<PairUseEnc>(vec![vir::TYPE_REF.as_dyn(), vir::TYPE_TYVAL.as_dyn()])
                .unwrap();

            let pure = deps.require_dep::<TyPureEnc>(*task_key)?;
            let impure = deps.require_dep::<TyImpureEnc>(*task_key)?;
            let params = deps
                .require_dep::<GenericParamsEnc>(task_key.params)
                .unwrap();
            let idn = vir::vir_format_identifier!(vcx, "s_{}_IM", task_key.name.as_str());
            let addr = vcx.mk_local_decl("addr", vir::TYPE_REF);
            let snap = vcx.mk_local_decl("snap", pure.snapshot);
            let result = vcx.mk_ty_set(tuple.ty);
            let idn = vir::FunctionIdn::new(
                idn,
                (addr.ty, snap.ty, params.ty_args(), params.const_args()),
                result,
            );
            deps.emit_output_ref(*task_key, TyInteriorMutRef(idn))?;

            let addr_ex = vcx.mk_local_ex(addr);
            let snap_ex = vcx.mk_local_ex(snap);
            let mut field_enc = TyInteriorMutField {
                vcx,
                tuple,
                deps,
                params: task_key.params,
                param_exprs: params.ty_exprs(),
                const_exprs: params.const_exprs(),
                addr: addr_ex,
                snap: snap_ex,
            };
            let ty = vcx.alloc(pure.zip(impure));
            let body = match &task_key.zip(ty).specifics {
                // TODO: could by the following also: // None, // Some(field_enc.all_in_uc()),
                _ if task_key.unsafe_cell => Some(vcx.mk_set_literal_expr(&[], field_enc.tuple.ty)),
                TySpecifics::Primitive(_) => Some(vcx.mk_set_literal_expr(&[], field_enc.tuple.ty)),
                // A raw pointer gives no permission to its pointee, so it
                // contributes no interior-mutable objects.
                TySpecifics::Raw(_) => Some(vcx.mk_set_literal_expr(&[], field_enc.tuple.ty)),
                TySpecifics::Param(_) => None,
                TySpecifics::Opaque(_) => None,
                TySpecifics::ImmRef(data) => Some(field_enc.all_in_immref(data)?),
                TySpecifics::MutRef(_) => todo!(),
                TySpecifics::Builtin(_) => todo!(),
                TySpecifics::ArrayLike(_) => todo!(),
                TySpecifics::StructLike(data) => Some(field_enc.all_in_struct(data)?),
                TySpecifics::EnumLike(enum_data) => Some(field_enc.all_in_enum(enum_data)?),
            };
            let im = task_key
                .interior_mut
                .iter()
                .map(|im| {
                    let call = CallTaskDescription::new(
                        task_key.data.params,
                        task_key.data.params.rust_params(),
                        *im,
                    );
                    let signature = vcx.tcx().fn_sig(*im).skip_binder();
                    let input = signature.inputs().skip_binder()[0];
                    let input = RustTyDecomposition::from_ty(input, task_key.data.params);
                    let metadata_ty = input
                        .ty
                        .ref_data()
                        .unwrap()
                        .metadata
                        .decompose_normalize(input.args);
                    let metadata = field_enc
                        .deps
                        .require_dep::<TyUsePureEnc>(metadata_ty)
                        .unwrap()
                        .zst_to_snap()
                        .expect("interior mutability accessor should take a thin reference")
                        .upcast_ty();
                    let input = field_enc
                        .deps
                        .require_dep::<TyUsePureEnc>(input)
                        .unwrap()
                        .expect_immref()
                        .prim_to_snap(addr_ex, metadata, snap_ex);
                    let output = signature.output().skip_binder();
                    let (inner, mut_) = match *output.kind() {
                        ty::TyKind::RawPtr(inner, mut_) => (inner, mut_),
                        _ => panic!(
                            "expected raw pointer output for interior mutability, got {:?}",
                            output
                        ),
                    };
                    let result = field_enc
                        .deps
                        .require_dep::<FunctionCallEnc>(call)
                        .unwrap()
                        .call_pure(vec![input.upcast_ty()]);
                    let raw_ptr_to_ref =
                        field_enc.deps.require_dep::<RawPtrToRefEnc>(mut_).unwrap();
                    let ref_ = raw_ptr_to_ref(result.downcast_ty());
                    let ty_ = RustTyDecomposition::from_ty(inner, task_key.data.params);
                    let ty_expr = ty_identity_expr(field_enc.deps, ty_);
                    (field_enc.tuple.constructor)(&[ref_.as_dyn(), ty_expr.as_dyn()])
                })
                .collect::<Vec<_>>();
            assert!(body.is_some() || im.is_empty());
            let body = body.map(|body| {
                if im.is_empty() {
                    body
                } else {
                    let values = vcx.alloc_slice(&im);
                    let im = vcx.mk_set_literal_expr(values, field_enc.tuple.ty);
                    vcx.mk_anyset_op_expr(vir::CollectionBinOpKind::Union, body, im)
                        .downcast_ty()
                }
            });
            let post = body
                .map(|body| vcx.mk_eq_expr(vcx.mk_result(body.ty()), body))
                .into_iter()
                .collect::<Vec<_>>();
            let post = vcx.alloc_slice(&post);
            let output = vcx.mk_function(
                idn,
                (addr, snap, params.ty_decls(), params.const_decls()),
                &[],
                post,
                Some(&vir::DecreasesGenData::Star),
                None,
            );
            Ok((output, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let outputs = Self::all_outputs_local_no_errors(program);
        for output in outputs {
            program.add_function(output);
        }
        RawPtrToRefEnc::emit_outputs(program);
    }
}

struct TyInteriorMutField<'a, 'vir> {
    vcx: &'vir vir::VirCtxt<'vir>,
    tuple: PairUse<'vir>,
    deps: &'a mut task_encoder::TaskEncoderDependencies<'vir, TyInteriorMutEnc>,
    params: GParams<'vir>,
    param_exprs: &'a [vir::ExprTyVal<'vir>],
    const_exprs: &'a [vir::ExprCSnap<'vir>],
    addr: vir::ExprRef<'vir>,
    snap: vir::ExprSnap<'vir>,
}

impl<'vir> TyInteriorMutField<'_, 'vir> {
    fn all_in_immref(
        &mut self,
        data: &<(RustTyDatas, (PureTyDatas, ImpureTyDatas)) as TyDatas<'vir>>::ImmRefData,
    ) -> Result<vir::ExprSet<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        let (inner, (pure, _)) = *data;
        let ty = inner.referent.decompose(self.params);
        let inner = self.deps.require_dep::<TyInteriorMutUseEnc>(ty)?;

        let addr = pure.deref_access.call()(self.snap.downcast_ty());
        let snap = pure.value_access.call()(self.snap.downcast_ty());
        Ok(inner.get_all(addr, snap.upcast_ty()))
    }

    fn all_in_struct(
        &mut self,
        data: &StructData<'vir, (RustTyDatas, (PureTyDatas, ImpureTyDatas))>,
    ) -> Result<vir::ExprSet<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        data.fields
            .iter()
            .map(|(field, (pure, impure))| {
                let ty = field.decompose(self.params);
                let inner = self.deps.require_dep::<TyInteriorMutUseEnc>(ty)?;

                // The field projection function expects the generics of the
                // containing struct (not those of the field).
                let addr = (impure.ref_to_field_ref)(self.addr, self.param_exprs, self.const_exprs);
                let snap = pure.read.call()(self.snap.downcast_ty());
                Ok(inner.get_all(addr, snap))
            })
            .reduce(|acc, e| {
                Ok(self
                    .vcx
                    .mk_anyset_op_expr(vir::CollectionBinOpKind::Union, acc?, e?)
                    .downcast_ty())
            })
            .unwrap_or_else(|| Ok(self.vcx.mk_set_literal_expr(&[], self.tuple.ty)))
    }

    fn all_in_enum(
        &mut self,
        data: &EnumData<'vir, (RustTyDatas, (PureTyDatas, ImpureTyDatas))>,
    ) -> Result<vir::ExprSet<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        let discr_snap = data.1.0.snap_to_discr_snap.call()(self.snap.downcast_ty());
        let vcx = self.vcx;
        let (_, set) = data
            .variants
            .iter()
            .map(|variant| {
                let inner = self.all_in_struct(&variant.inner)?;
                Ok((self.vcx.mk_eq_expr(discr_snap, variant.1.0.discr), inner))
            })
            .reduce(|acc, e| {
                let (cond, set) = acc?;
                let (next_cond, next_set) = e?;
                Ok((next_cond, vcx.mk_ternary_expr(cond, set, next_set)))
            })
            .unwrap()?;
        Ok(set)
    }

    fn all_in_uc(&mut self) -> vir::ExprSet<'vir> {
        assert_eq!(self.param_exprs.len(), 1);
        let value = (self.tuple.constructor)(&[self.addr.as_dyn(), self.param_exprs[0].as_dyn()]);
        let values = self.vcx.alloc_slice(&[value]);
        self.vcx.mk_set_literal_expr(values, self.tuple.ty)
    }
}

struct RawPtrToRefEnc;

impl TaskEncoder for RawPtrToRefEnc {
    task_encoder::encoder_cache!(RawPtrToRefEnc);
    const ENCODER_NAME: &'static str = "raw pointer to reference encoder";
    type TaskDescription<'vir> = ty::Mutability;
    type OutputFullDependency<'vir> = vir::FunctionIdn<'vir, vir::CSnap, vir::Ref>;
    type OutputFullLocal<'vir> = vir::Function<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let raw_ptr = vcx
                .tcx()
                .mk_ty_from_kind(ty::TyKind::RawPtr(vcx.tcx().types.self_param, *task_key));
            let raw_ptr = RustTyDecomposition::from_ty(raw_ptr, GParams::empty());
            let raw_ptr = deps
                .require_ref::<TyPureEnc>(raw_ptr.ty)?
                .snapshot
                .downcast_ty::<vir::CSnap>();
            let fn_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "C_{}_ptr_to_ref", task_key.ptr_str()),
                raw_ptr,
                vir::TYPE_REF,
            );
            let func = vcx.mk_function(
                fn_idn,
                (vcx.mk_local_decl("ptr", raw_ptr),),
                &[],
                &[],
                None,
                None,
            );
            Ok((func, fn_idn))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for func in Self::all_outputs_local_no_errors(program) {
            program.add_function(func);
        }
    }
}
