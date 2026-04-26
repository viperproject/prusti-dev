use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, CastType, FunctionIdn, HasType, MethodIdn};

use crate::encoders::{
    ConstEnc, TyUseImpureEnc,
    r#const::ConstEncTask,
    ty::{
        RustTyDecomposition, TySpecifics,
        generics::{GParams, GenericParamsEnc},
        interpretation::float::FloatDomain,
        pure::{TyPurePrimData, TyPurePrimDataKind},
        use_pure::TyUsePureEnc,
    },
};

pub struct MirBuiltinEnc;

#[derive(Clone, Debug)]
pub enum MirBuiltinEncError {
    UnsupportedUnsize { src: String, dst: String },
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
#[allow(clippy::enum_variant_names)]
pub enum MirBuiltinEncTask<'tcx> {
    Unsize(ty::Ty<'tcx>, ty::Ty<'tcx>, DefId),
    Len(ty::Ty<'tcx>),
    UnOp(ty::Ty<'tcx>, mir::UnOp, ty::Ty<'tcx>),
    BinOp(ty::Ty<'tcx>, mir::BinOp, ty::Ty<'tcx>, ty::Ty<'tcx>),
    CheckedBinOp(ty::Ty<'tcx>, mir::BinOp, ty::Ty<'tcx>, ty::Ty<'tcx>),
}

#[derive(Copy, Clone, Debug)]
pub struct MirBuiltinEncUnsize<'vir> {
    pub unsize: MethodIdn<'vir, (vir::Ref, vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
    pub undo: MethodIdn<'vir, (vir::Ref, vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
}

#[derive(Copy, Clone, Debug)]
pub enum MirBuiltinEncOutputRef<'vir> {
    Unsize(MirBuiltinEncUnsize<'vir>),
    Len(FunctionIdn<'vir, vir::CSnap, vir::CSnap>),
    UnOp(FunctionIdn<'vir, vir::CSnap, vir::CSnap>),
    BinOp(FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>),
}
impl<'vir> task_encoder::OutputRefAny for MirBuiltinEncOutputRef<'vir> {}
impl<'vir> MirBuiltinEncOutputRef<'vir> {
    pub fn unsize(self) -> Option<MirBuiltinEncUnsize<'vir>> {
        match self {
            MirBuiltinEncOutputRef::Unsize(unsize) => Some(unsize),
            _ => None,
        }
    }

    pub fn len(self) -> Option<FunctionIdn<'vir, vir::CSnap, vir::CSnap>> {
        match self {
            MirBuiltinEncOutputRef::Len(idn) => Some(idn),
            _ => None,
        }
    }

    pub fn un_op(self) -> Option<FunctionIdn<'vir, vir::CSnap, vir::CSnap>> {
        match self {
            MirBuiltinEncOutputRef::UnOp(idn) => Some(idn),
            _ => None,
        }
    }

    pub fn bin_op(self) -> Option<FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>> {
        match self {
            MirBuiltinEncOutputRef::BinOp(idn) => Some(idn),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct MirBuiltinEncOutput<'vir> {
    functions: Vec<vir::Function<'vir>>,
    methods: Vec<vir::Method<'vir>>,
}

impl TaskEncoder for MirBuiltinEnc {
    task_encoder::encoder_cache!(MirBuiltinEnc);
    const ENCODER_NAME: &'static str = "MIR builtin encoder";

    type TaskDescription<'vir> = MirBuiltinEncTask<'vir>;

    type OutputRef<'vir> = MirBuiltinEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirBuiltinEncOutput<'vir>;

    type EncodingError = MirBuiltinEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn describe_error(error: Self::EncodingError) -> String {
        match error {
            MirBuiltinEncError::UnsupportedUnsize { src, dst } => {
                format!("unsizing from `{src}` to `{dst}` is not yet supported")
            }
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let mut functions = Vec::new();
            let mut methods = Vec::new();
            match *task_key {
                MirBuiltinEncTask::Unsize(arg_ty, res_ty, def_id) => {
                    let (method, method_undo) =
                        Self::handle_unsize(vcx, deps, *task_key, arg_ty, res_ty, def_id)?;
                    methods.push(method);
                    methods.push(method_undo);
                }
                MirBuiltinEncTask::Len(arg_ty) => {
                    functions.push(Self::handle_len(vcx, deps, *task_key, arg_ty)?)
                }
                MirBuiltinEncTask::UnOp(res_ty, op, operand_ty) => functions.push(
                    Self::handle_un_op(vcx, deps, *task_key, op, operand_ty, res_ty)?,
                ),
                MirBuiltinEncTask::BinOp(res_ty, op, l_ty, r_ty) => functions.push(
                    Self::handle_bin_op(vcx, deps, *task_key, res_ty, op, l_ty, r_ty)?,
                ),
                MirBuiltinEncTask::CheckedBinOp(res_ty, op, l_ty, r_ty) => functions.push(
                    Self::handle_checked_bin_op(vcx, deps, *task_key, res_ty, op, l_ty, r_ty)?,
                ),
            }
            Ok((MirBuiltinEncOutput { functions, methods }, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            for function in output.functions {
                program.add_function(function);
            }
            for method in output.methods {
                program.add_method(method);
            }
        }
    }
}

// TODO: this function is also useful for the type encoder, extract?
fn int_name(ty: ty::Ty<'_>) -> &'static str {
    match ty.kind() {
        ty::TyKind::Bool => "bool",
        ty::TyKind::Char => "char",
        ty::TyKind::Int(kind) => kind.name_str(),
        ty::TyKind::Uint(kind) => kind.name_str(),
        ty::TyKind::Float(kind) => kind.name_str(),
        _ => unreachable!("non-integer type"),
    }
}

impl MirBuiltinEnc {
    fn handle_unsize<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        key: <Self as TaskEncoder>::TaskKey<'vir>,
        src_ty: ty::Ty<'vir>,
        dst_ty: ty::Ty<'vir>,
        def_id: DefId,
    ) -> Result<(vir::Method<'vir>, vir::Method<'vir>), EncodeFullError<'vir, Self>> {
        let name = vir::vir_format_identifier!(vcx, "mir_unsize_{src_ty:?}_to_{dst_ty:?}");
        let name_undo =
            vir::vir_format_identifier!(vcx, "mir_undo_unsize_{src_ty:?}_to_{dst_ty:?}");

        let params = GParams::from(def_id);
        let generics = deps.require_dep::<GenericParamsEnc>(params)?;

        let src_ty_inner = src_ty.peel_refs();
        let dst_ty_inner = dst_ty.peel_refs();

        let ty_task = RustTyDecomposition::from_ty(src_ty_inner, params);
        let src_inner_pure = deps.require_dep::<TyUsePureEnc>(ty_task)?;

        let src_ty = RustTyDecomposition::from_ty(src_ty, params);
        let src_ref_pure = deps.require_dep::<TyUsePureEnc>(src_ty)?;
        let src_ref_impure = deps.require_dep::<TyUseImpureEnc>(src_ty)?;

        let ty_task = RustTyDecomposition::from_ty(dst_ty_inner, params);
        let dst_inner_pure = deps.require_dep::<TyUsePureEnc>(ty_task)?;

        let dst_ty = RustTyDecomposition::from_ty(dst_ty, params);
        let dst_ref_pure = deps.require_dep::<TyUsePureEnc>(dst_ty)?;
        let dst_ref_impure = deps.require_dep::<TyUseImpureEnc>(dst_ty)?;

        let ref_src_decl = vcx.mk_local_decl("src", vir::TYPE_REF);
        let ref_src_ex = vcx.mk_local_ex(ref_src_decl);
        let ref_dst_decl = vcx.mk_local_decl("dst", vir::TYPE_REF);
        let ref_dst_ex = vcx.mk_local_ex(ref_dst_decl);
        let method = MethodIdn::new(
            name,
            (
                ref_src_decl.ty(),
                ref_dst_decl.ty(),
                generics.ty_args(),
                generics.const_args(),
            ),
        );
        let method_undo = MethodIdn::new(
            name_undo,
            (
                ref_src_decl.ty(),
                ref_dst_decl.ty(),
                generics.ty_args(),
                generics.const_args(),
            ),
        );
        deps.emit_output_ref(
            key,
            MirBuiltinEncOutputRef::Unsize(MirBuiltinEncUnsize {
                unsize: method,
                undo: method_undo,
            }),
        )?;

        let snap_src = src_ref_impure.ref_to_snap(ref_src_ex);
        let snap_dst = dst_ref_impure.ref_to_snap(ref_dst_ex);

        let mut pres = vec![src_ref_impure.ref_to_pred(vcx, ref_src_ex, None)];
        let mut posts = vec![dst_ref_impure.ref_to_pred(vcx, ref_dst_ex, None)];
        let mut pres_undo = vec![dst_ref_impure.ref_to_pred(vcx, ref_dst_ex, None)];
        let mut posts_undo = vec![src_ref_impure.ref_to_pred(vcx, ref_src_ex, None)];
        if src_ty.ty.specifics.is_mutref() && dst_ty.ty.specifics.is_mutref() {
            let ty_task_param = src_ty
                .ty
                .expect_mutref()
                .decompose_context(src_ty.ty.params, src_ty.args);
            let src_param_impure = deps.require_dep::<TyUseImpureEnc>(ty_task_param)?;
            let ty_task_param = dst_ty
                .ty
                .expect_mutref()
                .decompose_context(src_ty.ty.params, dst_ty.args);
            let dst_param_impure = deps.require_dep::<TyUseImpureEnc>(ty_task_param)?;

            pres.push(src_param_impure.ref_to_pred(
                vcx,
                src_ref_impure.expect_mutref().deref(ref_src_ex, None),
                None,
            ));
            posts.push(dst_param_impure.ref_to_pred(
                vcx,
                dst_ref_impure.expect_mutref().deref(ref_dst_ex, None),
                None,
            ));
            posts.push(vir::expr! {
                (old([src_ref_impure.expect_mutref().deref(ref_src_ex, None)]))
                    == ([dst_ref_impure.expect_mutref().deref(ref_dst_ex, None)])
            });
            pres_undo.push(dst_param_impure.ref_to_pred(
                vcx,
                dst_ref_impure.expect_mutref().deref(ref_dst_ex, None),
                None,
            ));
            posts_undo.push(src_param_impure.ref_to_pred(
                vcx,
                src_ref_impure.expect_mutref().deref(ref_src_ex, None),
                None,
            ));
            posts_undo.push(vir::expr! {
                ([src_ref_impure.expect_mutref().deref(ref_src_ex, None)])
                    == (old([dst_ref_impure.expect_mutref().deref(ref_dst_ex, None)]))
            });
        }

        match dst_ty_inner.kind() {
            ty::TyKind::Slice(_) => {
                let src_value = match &src_ref_pure.specifics {
                    TySpecifics::ImmRef(data) => data.value_access(snap_src.downcast_ty()),
                    TySpecifics::MutRef(data) => data.value_access(snap_src.downcast_ty()),
                    _ => unreachable!(),
                }
                .downcast_ty();
                let dst_value = match &dst_ref_pure.specifics {
                    TySpecifics::ImmRef(data) => data.value_access(snap_dst.downcast_ty()),
                    TySpecifics::MutRef(data) => data.value_access(snap_dst.downcast_ty()),
                    _ => unreachable!(),
                }
                .downcast_ty();

                let src_array_pure = src_inner_pure.expect_array();
                let dst_array_pure = dst_inner_pure.expect_array();
                let src_len = match src_ty_inner.kind() {
                    ty::TyKind::Array(_, len) => {
                        let const_enc = deps.require_dep::<ConstEnc>(ConstEncTask::Ty {
                            const_: *len,
                            ty: vcx.tcx().types.usize,
                            context: params,
                        })?;
                        let ty_task = RustTyDecomposition::from_prim_ty(vcx.tcx().types.usize);
                        let usize_out = deps.require_dep::<TyUsePureEnc>(ty_task)?.expect_native();
                        (usize_out.snap_to_prim)(const_enc).downcast_ty()
                    }
                    _ => src_array_pure.len(src_value),
                };
                posts.extend(&[
                    vir::expr! { (src_len) == ([dst_array_pure.len(dst_value)]) },
                    vir::expr! {
                        forall idx: Int :: {[dst_array_pure.index(dst_value, idx)]}
                            ([dst_array_pure.index(dst_value, idx)])
                            == (old([src_array_pure.index(src_value, idx)]))
                    },
                ]);
                posts_undo.push(vir::expr! {
                    forall idx: Int :: {[src_array_pure.index(src_value, idx)]}
                        ([src_array_pure.index(src_value, idx)])
                        == (old([dst_array_pure.index(dst_value, idx)]))
                });
            }
            _ => {
                return Err(EncodeFullError::EncodingError(
                    MirBuiltinEncError::UnsupportedUnsize {
                        src: src_ty_inner.to_string(),
                        dst: dst_ty_inner.to_string(),
                    },
                    None,
                ));
            }
        }

        Ok((
            vcx.mk_method(
                method,
                (
                    ref_src_decl,
                    ref_dst_decl,
                    generics.ty_decls(),
                    generics.const_decls(),
                ),
                &[],
                vcx.alloc_slice(&pres),
                vcx.alloc_slice(&posts),
                None,
            ),
            vcx.mk_method(
                method_undo,
                (
                    ref_src_decl,
                    ref_dst_decl,
                    generics.ty_decls(),
                    generics.const_decls(),
                ),
                &[],
                vcx.alloc_slice(&pres_undo),
                vcx.alloc_slice(&posts_undo),
                None,
            ),
        ))
    }

    fn handle_len<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        key: <Self as TaskEncoder>::TaskKey<'vir>,
        arg_ty: ty::Ty<'vir>,
    ) -> Result<vir::Function<'vir>, EncodeFullError<'vir, Self>> {
        let ty_task = RustTyDecomposition::from_ty(arg_ty, GParams::empty()); // TODO: context ...
        let arg_ty_pure = deps.require_dep::<TyUsePureEnc>(ty_task)?;

        let ty_task = RustTyDecomposition::from_prim_ty(vcx.tcx().types.usize);
        let res_ty_pure = deps.require_dep::<TyUsePureEnc>(ty_task)?;

        let name = vir::vir_format_identifier!(vcx, "mir_len_{arg_ty:?}");
        let arg_ty_snap = arg_ty_pure.snapshot.downcast_ty();
        let res_ty_snap = res_ty_pure.snapshot.downcast_ty();
        let function = FunctionIdn::new(name, arg_ty_snap, res_ty_snap);
        deps.emit_output_ref(key, MirBuiltinEncOutputRef::Len(function))?;

        let snap_arg_decl = vcx.mk_local_decl("arg", arg_ty_snap);
        let snap_arg_ex = vcx.mk_local_ex(snap_arg_decl);
        Ok(vcx.mk_function(
            function,
            (snap_arg_decl,),
            &[],
            &[],
            None,
            Some((res_ty_pure.expect_primitive().prim_to_snap)(
                arg_ty_pure.expect_array().len(snap_arg_ex).upcast_ty(),
            )),
        ))
    }

    fn handle_un_op<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        key: <Self as TaskEncoder>::TaskKey<'vir>,
        op: mir::UnOp,
        operand_ty: ty::Ty<'vir>,
        res_ty: ty::Ty<'vir>,
    ) -> Result<vir::Function<'vir>, EncodeFullError<'vir, Self>> {
        match op {
            mir::UnOp::Neg | mir::UnOp::Not => {
                assert_eq!(res_ty, operand_ty);
                let ty_task = RustTyDecomposition::from_prim_ty(operand_ty);
                let e_ty = deps.require_dep::<TyUsePureEnc>(ty_task)?;

                let name =
                    vir::vir_format_identifier!(vcx, "mir_unop_{op:?}_{}", int_name(operand_ty));
                let e_ty_snap = e_ty.snapshot.downcast_ty();
                let function = FunctionIdn::new(name, e_ty_snap, e_ty_snap);
                deps.emit_output_ref(key, MirBuiltinEncOutputRef::UnOp(function))?;

                let snap_arg_decl = vcx.mk_local_decl("arg", e_ty_snap);
                let prim_res_ty = e_ty.expect_primitive();
                let snap_arg = vcx.mk_local_ex(snap_arg_decl);
                let body = match prim_res_ty.kind {
                    TyPurePrimDataKind::Native(native) => {
                        let prim_arg = (native.snap_to_prim)(snap_arg);
                        let mut val = (prim_res_ty.prim_to_snap)(
                            vcx.mk_unary_op_expr(vir::UnOpKind::from(op), prim_arg),
                        );
                        // Can overflow when doing `- iN::MIN -> iN::MIN`. There is no
                        // `CheckedUnOp`, instead the compiler puts an `TerminatorKind::Assert`
                        // before in debug mode. We should still produce the correct result in
                        // release mode, which the code under this branch does.
                        if op == mir::UnOp::Neg && operand_ty.is_signed() {
                            let bound = vcx.get_min_int(operand_ty.kind());
                            // `snap_to_prim(arg) == -iN::MIN`
                            let cond = vcx.mk_eq_expr(prim_arg.downcast_ty(), bound);
                            // `snap_to_prim(arg) == -iN::MIN ? arg :
                            // prim_to_snap(-snap_to_prim(arg))`
                            val = vcx.mk_ternary_expr(cond, snap_arg, val)
                        }
                        val
                    }
                    TyPurePrimDataKind::Float(float) => {
                        assert!(matches!(op, mir::UnOp::Neg));
                        (float.fp_neg)(snap_arg)
                    }
                };
                Ok(vcx.mk_function(function, (snap_arg_decl,), &[], &[], None, Some(body)))
            }
            mir::UnOp::PtrMetadata => {
                // TODO: the task key for this should not store the region
                //   (e.g. len for &[bool] is currently &'3 [bool] depending on the callsite region)
                let ty_task = RustTyDecomposition::from_ty(operand_ty, GParams::empty());
                let operand_ref_pure = deps.require_dep::<TyUsePureEnc>(ty_task)?;
                let ty_task = RustTyDecomposition::from_prim_ty(res_ty);
                let res_ty_enc = deps.require_dep::<TyUsePureEnc>(ty_task)?;

                let name = vir::vir_format_identifier!(vcx, "mir_unop_{op:?}_{operand_ty:?}");
                let operand_ty_snap = operand_ref_pure.snapshot.downcast_ty();
                let res_ty_snap = res_ty_enc.snapshot.downcast_ty();
                let function = FunctionIdn::new(name, operand_ty_snap, res_ty_snap);
                deps.emit_output_ref(key, MirBuiltinEncOutputRef::UnOp(function))?;

                let snap_arg_decl = vcx.mk_local_decl("arg", operand_ty_snap);

                let body = match operand_ty.peel_refs().kind() {
                    ty::TyKind::Slice(..) | ty::TyKind::Array(..) => {
                        let ty_task =
                            RustTyDecomposition::from_ty(operand_ty.peel_refs(), GParams::empty());
                        let operand_array_pure =
                            deps.require_dep::<TyUsePureEnc>(ty_task)?.expect_array();
                        let snap_arg = vcx.mk_local_ex(snap_arg_decl);
                        let prim_res_ty = res_ty_enc.expect_primitive();
                        let operand_value = match &operand_ref_pure.specifics {
                            TySpecifics::ImmRef(data) => data.value_access(snap_arg),
                            TySpecifics::MutRef(data) => data.value_access(snap_arg),
                            _ => unreachable!(),
                        }
                        .downcast_ty();
                        Some((prim_res_ty.prim_to_snap)(
                            operand_array_pure.len(operand_value).upcast_ty(),
                        ))
                    }
                    _ => None,
                };

                Ok(vcx.mk_function(function, (snap_arg_decl,), &[], &[], None, body))
            }
        }
    }

    fn handle_bin_op<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        key: <Self as TaskEncoder>::TaskKey<'vir>,
        res_ty: ty::Ty<'vir>,
        op: mir::BinOp,
        l_ty: ty::Ty<'vir>,
        r_ty: ty::Ty<'vir>,
    ) -> Result<vir::Function<'vir>, EncodeFullError<'vir, Self>> {
        let l_ty_task = RustTyDecomposition::from_prim_ty(l_ty);
        let e_l_ty = deps.require_dep::<TyUsePureEnc>(l_ty_task)?;
        let r_ty_task = RustTyDecomposition::from_prim_ty(r_ty);
        let e_r_ty = deps.require_dep::<TyUsePureEnc>(r_ty_task)?;
        let res_ty_task = RustTyDecomposition::from_prim_ty(res_ty);
        let e_res_ty = deps.require_dep::<TyUsePureEnc>(res_ty_task)?;
        let prim_l_ty = e_l_ty.expect_primitive();
        let prim_r_ty = e_r_ty.expect_primitive();
        let prim_res_ty = e_res_ty.expect_primitive();
        let e_l_ty_snap = e_l_ty.snapshot.downcast_ty();
        let e_r_ty_snap = e_r_ty.snapshot.downcast_ty();
        let e_res_ty_snap = e_res_ty.snapshot.downcast_ty();

        let name = vir::vir_format_identifier!(
            vcx,
            "mir_binop_{op:?}_{}_{}",
            int_name(l_ty),
            int_name(r_ty)
        );
        let function = FunctionIdn::new(name, (e_l_ty_snap, e_r_ty_snap), e_res_ty_snap);
        deps.emit_output_ref(key, MirBuiltinEncOutputRef::BinOp(function))?;
        let lhs_decl = vcx.mk_local_decl("arg1", e_l_ty_snap);
        let rhs_decl = vcx.mk_local_decl("arg2", e_r_ty_snap);
        let lhs = vcx.mk_local_ex(lhs_decl);
        let rhs = vcx.mk_local_ex(rhs_decl);
        match prim_l_ty.kind {
            TyPurePrimDataKind::Native(prim_l_ty) => {
                let lhs = (prim_l_ty.snap_to_prim)(lhs);
                let rhs = (prim_r_ty.expect_native().snap_to_prim)(rhs);
                let (pres, val) = Self::handle_bin_op_native(vcx, lhs, rhs, res_ty, op, l_ty, r_ty);
                let val = (prim_res_ty.prim_to_snap)(val);
                Ok(vcx.mk_function(
                    function,
                    (lhs_decl, rhs_decl),
                    vcx.alloc_slice(&pres),
                    &[],
                    None,
                    Some(val),
                ))
            }
            TyPurePrimDataKind::Float(float) => {
                assert!(matches!(prim_r_ty.kind, TyPurePrimDataKind::Float(_)));
                let body = Self::handle_bin_op_float(vcx, lhs, rhs, op, float, *prim_res_ty);
                Ok(vcx.mk_function(function, (lhs_decl, rhs_decl), &[], &[], None, Some(body)))
            }
        }
    }

    fn handle_bin_op_native<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        lhs: vir::ExprPrim<'vir>,
        mut rhs: vir::ExprPrim<'vir>,
        res_ty: ty::Ty<'vir>,
        op: mir::BinOp,
        l_ty: ty::Ty<'vir>,
        _r_ty: ty::Ty<'vir>,
    ) -> (Vec<vir::ExprBool<'vir>>, vir::ExprPrim<'vir>) {
        use mir::BinOp::*;
        if matches!(op, Shl | Shr) {
            // RHS must be smaller than the bit width of the LHS, this is
            // implicit in the `Shl` and `Shr` operators.
            rhs = vcx.mk_bin_op_expr(
                vir::BinOpKind::Mod,
                rhs.downcast_ty(),
                vcx.get_bit_width_int(l_ty.kind()),
            );
        }

        if matches!(op, Cmp) {
            // Cmp does not have a direct analogue to VIR binary operations,
            // so we treat it specially.
            // a > b ? 1 : (b > a ? -1 : 0)
            let a_gt_b = vcx
                .mk_bin_op_expr(vir::BinOpKind::CmpGt, lhs, rhs)
                .downcast_ty();
            let b_gt_a = vcx
                .mk_bin_op_expr(vir::BinOpKind::CmpGt, rhs, lhs)
                .downcast_ty();
            let val = vcx
                .mk_ternary_expr(
                    a_gt_b,
                    vcx.mk_int::<1>(),
                    vcx.mk_ternary_expr(b_gt_a, vcx.mk_int::<-1>(), vcx.mk_int::<0>()),
                )
                .upcast_ty();
            (vec![], val)
        } else {
            let op_kind = vir::BinOpKind::from(op);
            let viper_val = vcx
                .mk_bin_op_expr_inner(op_kind, lhs.as_dyn(), rhs.as_dyn())
                .downcast_ty();
            match op {
                // Overflow well defined as wrapping (implicit) and for the shifts
                // the RHS will be masked to the bit width.
                Add | Sub | Mul | Shl | Shr => (
                    Vec::new(),
                    Self::get_wrapped_val(vcx, viper_val.downcast_ty(), res_ty).upcast_ty(),
                ),
                // Undefined behavior to overflow (need precondition)
                AddUnchecked | SubUnchecked | MulUnchecked => {
                    let min = vcx.get_min_int(res_ty.kind());
                    // `(arg1 op arg2) >= -iN::MIN`
                    let lower_bound = vcx
                        .mk_bin_op_expr(vir::BinOpKind::CmpGe, viper_val.downcast_ty(), min)
                        .downcast_ty::<vir::Bool>();
                    let max = vcx.get_max_int(res_ty.kind());
                    // `(arg1 op arg2) <= iN::MAX`
                    let upper_bound = vcx
                        .mk_bin_op_expr(vir::BinOpKind::CmpLe, viper_val.downcast_ty(), max)
                        .downcast_ty::<vir::Bool>();
                    (vec![lower_bound, upper_bound], viper_val)
                }
                // Overflow is well defined as wrapping (implicit), but shifting by
                // more than the bit width (or less than 0) is undefined behavior.
                ShlUnchecked | ShrUnchecked => {
                    let min = vcx.mk_int::<0>();
                    // `arg2 >= 0`
                    let lower_bound = vcx
                        .mk_bin_op_expr(vir::BinOpKind::CmpGe, rhs.downcast_ty(), min)
                        .downcast_ty::<vir::Bool>();
                    let max = vcx.get_bit_width_int(l_ty.kind());
                    // `arg2 < bit_width(arg1)`
                    let upper_bound = vcx
                        .mk_bin_op_expr(vir::BinOpKind::CmpLt, rhs.downcast_ty(), max)
                        .downcast_ty::<vir::Bool>();
                    (
                        vec![lower_bound, upper_bound],
                        Self::get_wrapped_val(vcx, viper_val.downcast_ty(), res_ty).upcast_ty(),
                    )
                }
                // Could divide by zero or overflow if divisor is `-1`
                Div | Rem => {
                    // `0 != arg2 `
                    let pre = vcx
                        .mk_bin_op_expr(vir::BinOpKind::CmpNe, vcx.mk_int::<0>(), rhs.downcast_ty())
                        .downcast_ty::<vir::Bool>();
                    let mut pres = vec![pre];
                    let mut val = viper_val;
                    if res_ty.is_signed() {
                        let min = vcx.get_min_int(res_ty.kind());
                        // `arg1 != -iN::MIN`
                        let arg1_cond =
                            vcx.mk_bin_op_expr(vir::BinOpKind::CmpNe, lhs.downcast_ty(), min);
                        // `-1 != arg2 `
                        let arg2_cond = vcx.mk_bin_op_expr(
                            vir::BinOpKind::CmpNe,
                            vcx.mk_int::<-1>(),
                            rhs.downcast_ty(),
                        );
                        // `-1 != arg2 || arg1 != -iN::MIN`
                        let pre = vcx
                            .mk_bin_op_expr(vir::BinOpKind::Or, arg1_cond, arg2_cond)
                            .downcast_ty::<vir::Bool>();
                        pres.push(pre);

                        // In SMTLib/Viper `\` and `%` round towards negative
                        // infinity, whereas Rust rounds to zero. Therefore, in
                        // the negative case where this matters, we flip the
                        // sign to get the opposite rounding.
                        let lhs_neg = vcx.mk_unary_op_expr(vir::UnOpKind::Neg, lhs);
                        let val_inv_neg = vcx
                            .mk_bin_op_expr_inner(op_kind, lhs_neg.as_dyn(), rhs.as_dyn())
                            .downcast_ty();
                        // -(-arg1 `op` arg2)
                        let val_neg = vcx.mk_unary_op_expr(vir::UnOpKind::Neg, val_inv_neg);
                        let lhs_pos = vcx.mk_bin_op_expr(
                            vir::BinOpKind::CmpGe,
                            lhs.downcast_ty(),
                            vcx.mk_int::<0>(),
                        );
                        // arg1 >= 0 ? arg1 `op` arg2 : -(-arg1 `op` arg2)
                        val = vcx.mk_ternary_expr(lhs_pos.downcast_ty(), val, val_neg);
                    }
                    (pres, val)
                }
                // Cannot overflow and no undefined behavior
                BitXor | BitAnd | BitOr | Eq | Lt | Le | Ne | Ge | Gt | Offset => {
                    (Vec::new(), viper_val)
                }

                // these are handled in `handle_checked_bin_op`
                AddWithOverflow | SubWithOverflow | MulWithOverflow => unreachable!(),

                // this is handled separately, earlier
                Cmp => unreachable!(),
            }
        }
    }

    fn handle_bin_op_float<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        lhs: vir::ExprCSnap<'vir>,
        rhs: vir::ExprCSnap<'vir>,
        op: mir::BinOp,
        float: FloatDomain<'vir>,
        prim_res_ty: TyPurePrimData<'vir>,
    ) -> vir::ExprCSnap<'vir> {
        use mir::BinOp::*;
        match op {
            Add => (float.fp_add)(lhs, rhs),
            AddUnchecked | AddWithOverflow => unreachable!(),
            Sub => (float.fp_sub)(lhs, rhs),
            SubUnchecked | SubWithOverflow => unreachable!(),
            Mul => (float.fp_mul)(lhs, rhs),
            MulUnchecked | MulWithOverflow => unreachable!(),
            Div => (float.fp_div)(lhs, rhs),
            Rem => {
                // SMT uses n = x / y -> round to nearest
                // Rust truncates
                // Therefore we cannot use SMT rem
                let div_res = (float.fp_div)(lhs, rhs);
                let div_trunc = (float.fp_trunc)(div_res);
                let mul_res = (float.fp_mul)(div_trunc, rhs);
                (float.fp_sub)(lhs, mul_res)
            }
            BitXor | BitAnd | BitOr | Shl | ShlUnchecked | Shr | ShrUnchecked => unreachable!(),
            Eq => {
                let prim_res = (float.fp_eq)(lhs, rhs);
                (prim_res_ty.prim_to_snap)(prim_res.upcast_ty())
            }
            Lt => {
                let prim_res = (float.fp_lt)(lhs, rhs);
                (prim_res_ty.prim_to_snap)(prim_res.upcast_ty())
            }
            Le => {
                let prim_res = (float.fp_leq)(lhs, rhs);
                (prim_res_ty.prim_to_snap)(prim_res.upcast_ty())
            }
            Ne => {
                let prim_res = (float.fp_eq)(lhs, rhs);
                let neq = vcx.mk_unary_op_expr(vir::UnOpKind::Not, prim_res.upcast_ty());
                (prim_res_ty.prim_to_snap)(neq)
            }
            Ge => {
                let prim_res = (float.fp_geq)(lhs, rhs);
                (prim_res_ty.prim_to_snap)(prim_res.upcast_ty())
            }
            Gt => {
                let prim_res = (float.fp_gt)(lhs, rhs);
                (prim_res_ty.prim_to_snap)(prim_res.upcast_ty())
            }
            Cmp => todo!(), // maybe don't implement here but as a stdlib specification
            Offset => unreachable!(),
        }
    }

    fn handle_checked_bin_op<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        key: <Self as TaskEncoder>::TaskKey<'vir>,
        res_ty: ty::Ty<'vir>,
        op: mir::BinOp,
        l_ty: ty::Ty<'vir>,
        r_ty: ty::Ty<'vir>,
    ) -> Result<vir::Function<'vir>, EncodeFullError<'vir, Self>> {
        // `op` can only be `Add`, `Sub` or `Mul`, or their overflowing version
        assert!(matches!(
            op,
            mir::BinOp::Add
                | mir::BinOp::Sub
                | mir::BinOp::Mul
                | mir::BinOp::AddWithOverflow
                | mir::BinOp::SubWithOverflow
                | mir::BinOp::MulWithOverflow
        ));
        let l_ty_task = RustTyDecomposition::from_prim_ty(l_ty);
        let e_l_ty = deps.require_dep::<TyUsePureEnc>(l_ty_task)?;
        let r_ty_task = RustTyDecomposition::from_prim_ty(r_ty);
        let e_r_ty = deps.require_dep::<TyUsePureEnc>(r_ty_task)?;
        let e_l_ty_snap = e_l_ty.snapshot.downcast_ty();
        let e_r_ty_snap = e_r_ty.snapshot.downcast_ty();

        let name = vir::vir_format_identifier!(
            vcx,
            "mir_checkedbinop_{op:?}_{}_{}",
            int_name(l_ty),
            int_name(r_ty)
        );
        let res_ty_task = RustTyDecomposition::from_ty(res_ty, GParams::empty());
        let e_res_ty = deps.require_dep::<TyUsePureEnc>(res_ty_task)?;
        let e_res_ty_snap = e_res_ty.snapshot.downcast_ty();
        let function = FunctionIdn::new(name, (e_l_ty_snap, e_r_ty_snap), e_res_ty_snap);
        deps.emit_output_ref(key, MirBuiltinEncOutputRef::BinOp(function))?;

        let lhs_decl = vcx.mk_local_decl("arg1", e_l_ty_snap);
        let rhs_decl = vcx.mk_local_decl("arg2", e_r_ty_snap);

        // The result of a checked add will always be `(T, bool)`, get the `T`
        // type
        let rvalue_pure_ty = res_ty.tuple_fields()[0];
        let bool_ty = res_ty.tuple_fields()[1];
        assert!(bool_ty.is_bool());

        let rvalue_pure_ty_task = RustTyDecomposition::from_prim_ty(rvalue_pure_ty);
        let e_rvalue_pure_ty = deps.require_dep::<TyUsePureEnc>(rvalue_pure_ty_task)?;
        let e_rvalue_pure_ty = e_rvalue_pure_ty.expect_primitive();
        assert_eq!(vir::TYPE_INT.upcast_ty(), e_rvalue_pure_ty.prim_type);
        let prim_type = e_rvalue_pure_ty.prim_type.downcast_ty::<vir::Int>();
        let bool_ty_task = RustTyDecomposition::from_prim_ty(bool_ty);
        let e_bool = deps.require_dep::<TyUsePureEnc>(bool_ty_task)?;
        let bool_cons = e_bool
            .expect_primitive()
            .prim_to_snap
            .cast_args::<vir::Bool>(vir::TYPE_BOOL);

        // Unbounded value
        let val_exp = vcx
            .mk_bin_op_expr(
                vir::BinOpKind::from(op),
                (e_l_ty.expect_native().snap_to_prim)(vcx.mk_local_ex(lhs_decl)),
                (e_r_ty.expect_native().snap_to_prim)(vcx.mk_local_ex(rhs_decl)),
            )
            .downcast_ty();
        let val_decl = vcx.mk_local_decl("val", prim_type);
        let val = vcx.mk_local_ex(val_decl);
        // Wrapped value
        let wrapped_val_decl = vcx.mk_local_decl("wrapped_val", prim_type);
        let wrapped_val_exp = Self::get_wrapped_val(vcx, val, rvalue_pure_ty);
        let wrapped_val = vcx.mk_local_ex(wrapped_val_decl);
        let wrapped_val_snap = (e_rvalue_pure_ty.prim_to_snap)(wrapped_val.upcast_ty());
        // Overflowed?
        let overflowed = vcx
            .mk_bin_op_expr(vir::BinOpKind::CmpNe, wrapped_val, val)
            .downcast_ty();
        let overflowed_snap = bool_cons(overflowed);
        // `tuple(prim_to_snap(wrapped_val), wrapped_val != val)`
        let tuple = e_res_ty.expect_structlike().field_snaps_to_snap(vec![
            wrapped_val_snap.upcast_ty(),
            overflowed_snap.upcast_ty(),
        ]);
        // `let wrapped_val == (val ..) in $tuple`
        let inner_let = vcx.mk_let_expr(wrapped_val_decl, wrapped_val_exp, tuple);

        Ok(vcx.mk_function(
            function,
            (lhs_decl, rhs_decl),
            &[],
            &[],
            None,
            Some(vcx.mk_let_expr(val_decl, val_exp, inner_let)),
        ))
    }

    /// Wrap the value in the range of the type, e.g. `uN` is wrapped in the
    /// range `uN::MIN..=uN::MAX` using modulo. For signed integers, the range
    /// is `iN::MIN..=iN::MAX` and the value is wrapped using two's complement.
    #[allow(clippy::needless_lifetimes)]
    fn get_wrapped_val<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        mut exp: vir::ExprInt<'vir>,
        rust_ty: ty::Ty,
    ) -> vir::ExprInt<'vir> {
        let shift_amount = vcx.get_signed_shift_int(rust_ty.kind());
        if let Some(half) = shift_amount {
            exp = vcx
                .mk_bin_op_expr(vir::BinOpKind::Add, exp, half)
                .downcast_ty();
        }
        let modulo_val = vcx.get_modulo_int(rust_ty.kind());
        exp = vcx
            .mk_bin_op_expr(vir::BinOpKind::Mod, exp, modulo_val)
            .downcast_ty();
        if let Some(half) = shift_amount {
            exp = vcx
                .mk_bin_op_expr(vir::BinOpKind::Sub, exp, half)
                .downcast_ty();
        }
        exp
    }
}
