use prusti_rustc_interface::middle::{mir, ty};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, CastType, FunctionIdn};

use crate::encoders::ty::{
    RustTy, RustTyDecomposition,
    interpretation::float::FloatDomain,
    pure::{TyPurePrimData, TyPurePrimDataKind},
    use_pure::TyUsePureEnc,
};

/// Encodes the builtin MIR binary operations (e.g. `Add`, `Sub`, `Mul`, `Div`,
/// etc.) as Viper functions with the correct semantics.
pub struct MirBuiltinBinOpEnc;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct MirBuiltinBinOpTask<'vir> {
    result_ty: RustTyDecomposition<'vir>,
    op: mir::BinOp,
    lhs_ty: RustTy<'vir>,
    rhs_ty: RustTy<'vir>,
}

impl<'vir> MirBuiltinBinOpTask<'vir> {
    pub fn new(
        mut result_ty: RustTyDecomposition<'vir>,
        op: mir::BinOp,
        lhs_ty: RustTyDecomposition<'vir>,
        rhs_ty: RustTyDecomposition<'vir>,
    ) -> Self {
        // The result type is always the concrete `<int>` or `(<int>, bool)`),
        // remove the context to avoid duplicate keys.
        result_ty.args = result_ty.args.with_empty_context();
        Self {
            result_ty,
            op,
            lhs_ty: lhs_ty.ty,
            rhs_ty: rhs_ty.ty,
        }
    }
}

impl TaskEncoder for MirBuiltinBinOpEnc {
    task_encoder::encoder_cache!(MirBuiltinBinOpEnc);
    const ENCODER_NAME: &'static str = "MIR builtin binary op encoder";

    type TaskDescription<'vir> = MirBuiltinBinOpTask<'vir>;

    type OutputFullDependency<'vir> = vir::FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>;
    type OutputFullLocal<'vir> = vir::Function<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let MirBuiltinBinOpTask {
                result_ty,
                op,
                lhs_ty,
                rhs_ty,
            } = *task_key;
            let mut encode = |ty| {
                let ty = RustTyDecomposition::identity(ty);
                deps.require_dep::<TyUsePureEnc>(ty)
            };
            let res = encode(lhs_ty)?;
            let (l_ty_prim, l_ty_snap) = (res.expect_primitive(), res.snapshot.downcast_ty());
            let res = encode(rhs_ty)?;
            let (r_ty_prim, r_ty_snap) = (res.expect_primitive(), res.snapshot.downcast_ty());
            let res = encode(result_ty.ty)?;
            let res_ty_snap = res.snapshot.downcast_ty();

            let name = vir::vir_format_identifier!(
                vcx,
                "mir_binop_{op:?}_{}_{}",
                lhs_ty.name(),
                rhs_ty.name()
            );
            let fn_idn = FunctionIdn::new(name, (l_ty_snap, r_ty_snap), res_ty_snap);

            let lhs_decl = vcx.mk_local_decl("arg1", l_ty_snap);
            let rhs_decl = vcx.mk_local_decl("arg2", r_ty_snap);
            let lhs = vcx.mk_local_ex(lhs_decl);
            let rhs = vcx.mk_local_ex(rhs_decl);
            let (pres, body) = match l_ty_prim.kind {
                TyPurePrimDataKind::Native(l_ty_prim) => {
                    let lhs = (l_ty_prim.snap_to_prim)(lhs);
                    let rhs = (r_ty_prim.expect_native().snap_to_prim)(rhs);
                    // `l_ty` is the type the operation is performed in. The operands
                    // do not always share a type (e.g. a shift's amount may be a
                    // different integer type than the shifted value), so we do not
                    // require `lhs_ty == rhs_ty` here.
                    let l_ty = *lhs_ty.expect_primitive();

                    if op.is_overflowing() {
                        let val =
                            Self::handle_bin_op_overflowing(vcx, deps, result_ty, op, lhs, rhs)?;
                        (Vec::new(), val)
                    } else {
                        let res_ty = *result_ty.ty.expect_primitive();
                        let (pres, val) =
                            Self::handle_bin_op_native(vcx, lhs, rhs, res_ty, op, l_ty);
                        (pres, (res.expect_primitive().prim_to_snap)(val))
                    }
                }
                TyPurePrimDataKind::Float(float) => {
                    assert!(matches!(r_ty_prim.kind, TyPurePrimDataKind::Float(_)));
                    let res_ty_prim = res.expect_primitive();
                    let body = Self::handle_bin_op_float(vcx, lhs, rhs, op, float, *res_ty_prim);
                    (Vec::new(), body)
                }
            };
            let pres = vcx.alloc_slice(&pres);
            let function =
                vcx.mk_function(fn_idn, (lhs_decl, rhs_decl), pres, &[], None, Some(body));
            Ok((function, fn_idn))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for function in Self::all_outputs_local_no_errors(program) {
            program.add_function(function);
        }
    }
}

impl MirBuiltinBinOpEnc {
    fn handle_bin_op_native<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        lhs: vir::ExprPrim<'vir>,
        mut rhs: vir::ExprPrim<'vir>,
        res_ty: ty::Ty<'vir>,
        op: mir::BinOp,
        in_ty: ty::Ty<'vir>,
    ) -> (Vec<vir::ExprBool<'vir>>, vir::ExprPrim<'vir>) {
        use mir::BinOp::*;
        if matches!(op, Shl | Shr) {
            // RHS must be smaller than the bit width of the LHS, this is
            // implicit in the `Shl` and `Shr` operators.
            rhs = vcx.mk_bin_op_expr(
                vir::BinOpKind::Mod,
                rhs.downcast_ty(),
                vcx.get_bit_width_int(in_ty.kind()),
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
                    vcx.get_wrapped_val(viper_val.downcast_ty(), res_ty.kind())
                        .upcast_ty(),
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
                    let max = vcx.get_bit_width_int(in_ty.kind());
                    // `arg2 < bit_width(arg1)`
                    let upper_bound = vcx
                        .mk_bin_op_expr(vir::BinOpKind::CmpLt, rhs.downcast_ty(), max)
                        .downcast_ty::<vir::Bool>();
                    (
                        vec![lower_bound, upper_bound],
                        vcx.get_wrapped_val(viper_val.downcast_ty(), res_ty.kind())
                            .upcast_ty(),
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
                        // The Rust and Viper (SMT) semantics for `\` and `%` do
                        // not match up when `arg1 < 0`: Rust truncates (`\`
                        // rounds toward zero, `%` takes the sign of the
                        // dividend), whereas Viper's `\`/`%` are euclidean
                        // (always `0 <= arg1 % arg2 < |arg2|`).
                        // `-arg1`
                        let neg_lhs = vcx.mk_unary_op_expr(vir::UnOpKind::Neg, lhs);
                        // `(-arg1) op arg2`
                        let neg_op = vcx.mk_bin_op_expr(op_kind, neg_lhs, rhs);
                        // `-((-arg1) op arg2)`
                        let neg_result = vcx.mk_unary_op_expr(vir::UnOpKind::Neg, neg_op);
                        // `arg1 == 0`
                        let lhs_zero = vcx.mk_eq_expr(lhs.downcast_ty(), vcx.mk_int::<0>());
                        // `arg1 == 0 ? 0 : -((-arg1) op arg2)`
                        let zero_or_neg = vcx.mk_ternary_expr(
                            lhs_zero,
                            vcx.mk_int::<0>().upcast_ty(),
                            neg_result,
                        );
                        // `arg1 > 0`
                        let lhs_pos = vcx
                            .mk_bin_op_expr(
                                vir::BinOpKind::CmpGt,
                                lhs.downcast_ty(),
                                vcx.mk_int::<0>(),
                            )
                            .downcast_ty();
                        // `arg1 > 0 ? arg1 op arg2 : (arg1 == 0 ? 0 : -((-arg1) op arg2))`
                        val = vcx.mk_ternary_expr(lhs_pos, val, zero_or_neg);
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

    fn handle_bin_op_overflowing<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        result_ty: RustTyDecomposition<'vir>,
        op: mir::BinOp,
        lhs: vir::ExprPrim<'vir>,
        rhs: vir::ExprPrim<'vir>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, Self>> {
        // `op` can only be the overflowing version of `Add`, `Sub` or `Mul`
        assert!(op.is_overflowing());

        // The result of a checked add will always be `(T, bool)`, get the `T`
        // type
        assert_eq!(result_ty.ty.name(), "2_Tuple");
        let res_ty_int = result_ty.args.args()[0].expect_ty();
        let bool_ty = result_ty.args.args()[1].expect_ty();
        assert!(bool_ty.is_bool());

        // Re-encode the result tuple with its concrete arguments (always
        // `(<some int>, bool)`) so that the tuple constructor casts the concrete
        // `int`/`bool` field snapshots to the tuple's generic (`Param`) fields.
        // (Encoding it via `identity` would give identity field casters that
        // expect already-generic `Param` snapshots.)
        let e_res_ty = deps.require_dep::<TyUsePureEnc>(result_ty)?;

        let ty = RustTyDecomposition::from_prim_ty(res_ty_int);
        let e_res_ty_int = deps.require_dep::<TyUsePureEnc>(ty)?.expect_primitive();
        assert_eq!(vir::TYPE_INT.upcast_ty(), e_res_ty_int.prim_type);
        let prim_type = e_res_ty_int.prim_type.downcast_ty::<vir::Int>();
        let bool_ty_task = RustTyDecomposition::from_prim_ty(bool_ty);
        let e_bool = deps.require_dep::<TyUsePureEnc>(bool_ty_task)?;
        let bool_cons = e_bool
            .expect_primitive()
            .prim_to_snap
            .cast_args::<vir::Bool>(vir::TYPE_BOOL);

        // Unbounded value
        let val_exp = vcx
            .mk_bin_op_expr(vir::BinOpKind::from(op), lhs, rhs)
            .downcast_ty();
        let val_decl = vcx.mk_local_decl("val", prim_type);
        let val = vcx.mk_local_ex(val_decl);
        // Wrapped value
        let wrapped_val_decl = vcx.mk_local_decl("wrapped_val", prim_type);
        let wrapped_val_exp = vcx.get_wrapped_val(val, res_ty_int.kind());
        let wrapped_val = vcx.mk_local_ex(wrapped_val_decl);
        let wrapped_val_snap = (e_res_ty_int.prim_to_snap)(wrapped_val.upcast_ty());
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
        Ok(vcx.mk_let_expr(val_decl, val_exp, inner_let))
    }
}
