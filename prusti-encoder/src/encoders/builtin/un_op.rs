use prusti_rustc_interface::middle::mir;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, FunctionIdn};

use crate::encoders::{
    Pure,
    ty::{
        RustTy, RustTyDecomposition, RustTyNormalized, generics::GArgsCastEnc,
        pure::TyPurePrimDataKind, use_pure::TyUsePureEnc,
    },
};

/// Encodes the builtin MIR unary operations (e.g. `Neg`, `Not`, `PtrMetadata`)
/// as Viper functions with the correct semantics.
pub struct MirBuiltinUnOpEnc;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct MirBuiltinUnOpTask<'vir> {
    result_ty: RustTy<'vir>,
    op: mir::UnOp,
    operand_ty: RustTy<'vir>,
}

impl<'vir> MirBuiltinUnOpTask<'vir> {
    pub fn new(
        result_ty: RustTyDecomposition<'vir>,
        op: mir::UnOp,
        operand_ty: RustTyDecomposition<'vir>,
    ) -> Self {
        Self {
            result_ty: result_ty.ty,
            op,
            operand_ty: operand_ty.ty,
        }
    }
}

impl TaskEncoder for MirBuiltinUnOpEnc {
    task_encoder::encoder_cache!(MirBuiltinUnOpEnc);
    const ENCODER_NAME: &'static str = "MIR builtin unary op encoder";

    type TaskDescription<'vir> = MirBuiltinUnOpTask<'vir>;

    type OutputFullDependency<'vir> = vir::FunctionIdn<'vir, vir::CSnap, vir::Snap>;
    type OutputFullLocal<'vir> = vir::Function<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let MirBuiltinUnOpTask {
            result_ty,
            op,
            operand_ty,
        } = *task_key;
        vir::with_vcx(|vcx| {
            let ty_task = RustTyDecomposition::identity(operand_ty);
            let e_ty = deps.require_dep::<TyUsePureEnc>(ty_task)?;
            let ty_task = RustTyDecomposition::identity(result_ty);
            let r_ty = deps.require_ref::<TyUsePureEnc>(ty_task)?;

            // `PtrMetadata` tasks share the operand base type but differ in the
            // metadata `result_ty`, so include it in the name to avoid clashes.
            let mut name = format!("mir_unop_{op:?}_{}", operand_ty.name());
            if matches!(op, mir::UnOp::PtrMetadata) {
                name.push('_');
                name.push_str(result_ty.name());
            }
            let name = vir::vir_format_identifier!(vcx, "{name}");
            let e_ty_snap = e_ty.snapshot.downcast_ty::<vir::CSnap>();
            let fn_idn = FunctionIdn::new(name, e_ty_snap, r_ty.snapshot);

            let snap_arg_decl = vcx.mk_local_decl("arg", e_ty_snap);
            let snap_arg = vcx.mk_local_ex(snap_arg_decl);

            let body = match op {
                // `PtrMetadata` reads the pointer metadata (e.g. a slice's length).
                // The snapshot holds it generically; we need to cast it to the
                // (possibly) concrete `result_ty`.
                mir::UnOp::PtrMetadata => {
                    let normalized = if result_ty.specifics.is_param() {
                        None
                    } else {
                        let ref_data = operand_ty
                            .ref_data()
                            .expect("`PtrMetadata` on a type without pointer metadata");
                        let param = ref_data.metadata.decompose(operand_ty.params).ty;
                        // Should not fail
                        assert!(
                            param.specifics.is_param(),
                            "`PtrMetadata` metadata {param:?} is non-generic"
                        );
                        let concrete = RustTyDecomposition::identity(result_ty);
                        Some(RustTyNormalized { param, concrete })
                    };
                    let caster = deps.require_dep::<GArgsCastEnc<Pure>>(normalized)?;
                    caster.cast_to_caller_ctx(e_ty.metadata_access(snap_arg))
                }
                mir::UnOp::Neg | mir::UnOp::Not => {
                    assert_eq!(result_ty, operand_ty);
                    let prim_res_ty = e_ty.expect_primitive();
                    match prim_res_ty.kind {
                        TyPurePrimDataKind::Native(native) => {
                            let prim_arg = (native.snap_to_prim)(snap_arg);
                            let mut val = (prim_res_ty.prim_to_snap)(
                                vcx.mk_unary_op_expr(vir::UnOpKind::from(op), prim_arg),
                            );
                            // Can overflow when doing `- iN::MIN -> iN::MIN`. There is no
                            // `CheckedUnOp`, instead the compiler puts an `TerminatorKind::Assert`
                            // before in debug mode. We should still produce the correct result in
                            // release mode, which the code under this branch does.
                            let operand_ty = *operand_ty.expect_primitive();
                            if op == mir::UnOp::Neg && operand_ty.is_signed() {
                                let bound = vcx.get_min_int(operand_ty.kind());
                                // `snap_to_prim(arg) == -iN::MIN`
                                let cond = vcx.mk_eq_expr(prim_arg.downcast_ty(), bound);
                                // `snap_to_prim(arg) == -iN::MIN ? arg :
                                // prim_to_snap(-snap_to_prim(arg))`
                                val = vcx.mk_ternary_expr(cond, snap_arg, val)
                            }
                            val.upcast_ty()
                        }
                        TyPurePrimDataKind::Float(float) => {
                            assert!(matches!(op, mir::UnOp::Neg));
                            (float.fp_neg)(snap_arg).upcast_ty()
                        }
                    }
                }
            };
            let function = vcx.mk_function(fn_idn, (snap_arg_decl,), &[], &[], None, Some(body));
            Ok((function, fn_idn))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for function in Self::all_outputs_local_no_errors(program) {
            program.add_function(function);
        }
    }
}
