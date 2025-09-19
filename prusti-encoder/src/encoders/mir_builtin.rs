use prusti_rustc_interface::middle::{mir, ty};
use prusti_utils::config;
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, CastType, FunctionIdn};

use crate::encoders::ty::{RustTyDecomposition, use_pure::TyUsePureEnc};

pub struct MirBuiltinEnc;

#[derive(Clone, Debug)]
pub enum MirBuiltinEncError {
    // Unsupported,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
#[allow(clippy::enum_variant_names)]
pub enum MirBuiltinEncTask<'tcx> {
    UnOp(ty::Ty<'tcx>, mir::UnOp, ty::Ty<'tcx>),
    BinOp(ty::Ty<'tcx>, mir::BinOp, ty::Ty<'tcx>, ty::Ty<'tcx>),
    CheckedBinOp(ty::Ty<'tcx>, mir::BinOp, ty::Ty<'tcx>, ty::Ty<'tcx>),
}

#[derive(Copy, Clone, Debug)]
pub enum MirBuiltinEncOutputRef<'vir> {
    UnOp(FunctionIdn<'vir, vir::CSnap, vir::CSnap>),
    BinOp(FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>),
}
impl<'vir> task_encoder::OutputRefAny for MirBuiltinEncOutputRef<'vir> {}
impl<'vir> MirBuiltinEncOutputRef<'vir> {
    pub fn un_op(self) -> Option<FunctionIdn<'vir, vir::CSnap, vir::CSnap>> {
        match self {
            MirBuiltinEncOutputRef::UnOp(idn) => Some(idn),
            MirBuiltinEncOutputRef::BinOp(_) => None,
        }
    }

    pub fn bin_op(self) -> Option<FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>> {
        match self {
            MirBuiltinEncOutputRef::UnOp(_) => None,
            MirBuiltinEncOutputRef::BinOp(idn) => Some(idn),
        }
    }
}

#[derive(Clone, Debug)]
pub struct MirBuiltinEncOutput<'vir> {
    pub function: vir::Function<'vir>,
}

impl TaskEncoder for MirBuiltinEnc {
    task_encoder::encoder_cache!(MirBuiltinEnc);

    type TaskDescription<'vir> = MirBuiltinEncTask<'vir>;

    type OutputRef<'vir> = MirBuiltinEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirBuiltinEncOutput<'vir>;

    type EncodingError = MirBuiltinEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| match *task_key {
            MirBuiltinEncTask::UnOp(res_ty, op, operand_ty) => {
                assert_eq!(res_ty, operand_ty);
                let function = Self::handle_un_op(vcx, deps, *task_key, op, operand_ty)?;
                Ok((MirBuiltinEncOutput { function }, ()))
            }
            MirBuiltinEncTask::BinOp(res_ty, op, l_ty, r_ty) => {
                let function = Self::handle_bin_op(vcx, deps, *task_key, res_ty, op, l_ty, r_ty)?;
                Ok((MirBuiltinEncOutput { function }, ()))
            }
            MirBuiltinEncTask::CheckedBinOp(res_ty, op, l_ty, r_ty) => {
                let function =
                    Self::handle_checked_bin_op(vcx, deps, *task_key, res_ty, op, l_ty, r_ty)?;
                Ok((MirBuiltinEncOutput { function }, ()))
            }
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors() {
            program.add_function(output.function);
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
        _ => unreachable!("non-integer type"),
    }
}

impl MirBuiltinEnc {
    fn handle_un_op<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        key: <Self as TaskEncoder>::TaskKey<'vir>,
        op: mir::UnOp,
        ty: ty::Ty<'vir>,
    ) -> Result<vir::Function<'vir>, EncodeFullError<'vir, Self>> {
        let ty_task = RustTyDecomposition::from_prim_ty(ty);
        let e_ty = deps.require_dep::<TyUsePureEnc>(ty_task)?;

        let name = vir::vir_format_identifier!(vcx, "mir_unop_{op:?}_{}", int_name(ty));
        let e_ty_snap = e_ty.snapshot.downcast_ty();
        let function = FunctionIdn::new(name, e_ty_snap, e_ty_snap);
        deps.emit_output_ref(key, MirBuiltinEncOutputRef::UnOp(function))?;

        let snap_arg_decl = vcx.mk_local_decl("arg", e_ty_snap);
        let prim_res_ty = e_ty.expect_primitive();
        let snap_arg = vcx.mk_local_ex(snap_arg_decl);
        let prim_arg = (prim_res_ty.snap_to_prim)(snap_arg);
        let mut val =
            (prim_res_ty.prim_to_snap)(vcx.mk_unary_op_expr(vir::UnOpKind::from(op), prim_arg));
        // Can overflow when doing `- iN::MIN -> iN::MIN`. There is no
        // `CheckedUnOp`, instead the compiler puts an `TerminatorKind::Assert`
        // before in debug mode. We should still produce the correct result in
        // release mode, which the code under this branch does.
        if op == mir::UnOp::Neg && ty.is_signed() {
            let bound = vcx.get_min_int(ty.kind());
            // `snap_to_prim(arg) == -iN::MIN`
            let cond = vcx.mk_eq_expr(prim_arg.downcast_ty(), bound);
            // `snap_to_prim(arg) == -iN::MIN ? arg :
            // prim_to_snap(-snap_to_prim(arg))`
            val = vcx.mk_ternary_expr(cond, snap_arg, val)
        }

        Ok(vcx.mk_function(function, (snap_arg_decl,), &[], &[], None, Some(val)))
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
        use mir::BinOp::*;
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
        let lhs = (prim_l_ty.snap_to_prim)(vcx.mk_local_ex(lhs_decl));
        let mut rhs = (prim_r_ty.snap_to_prim)(vcx.mk_local_ex(rhs_decl));
        if matches!(op, Shl | Shr) {
            // RHS must be smaller than the bit width of the LHS, this is
            // implicit in the `Shl` and `Shr` operators.
            rhs = vcx.mk_bin_op_expr(
                vir::BinOpKind::Mod,
                rhs.downcast_ty(),
                vcx.get_bit_width_int(l_ty.kind()),
            );
        }

        let (pres, val) = if matches!(op, Cmp) {
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
            let viper_val = vcx.mk_bin_op_expr_inner(op_kind, lhs, rhs);
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
                        // The Rust and Viper (SMT) semantics for `\` and `%` do not
                        // match up when `arg1 < 0`, encode this difference.
                        if matches!(op, Div) {
                            // `arg1 >= 0 ? arg1 \ arg2 : arg2 >= 0 ? (arg1 - 1) \ arg2 + 1 : (arg1 - 1) \ arg2 - 1`
                            let lhs_sub = vcx.mk_bin_op_expr(
                                vir::BinOpKind::Sub,
                                lhs.downcast_ty(),
                                vcx.mk_int::<1>(),
                            );
                            let common_div = vcx
                                .mk_bin_op_expr_inner(op_kind, lhs_sub, rhs)
                                .downcast_ty();
                            let neg_pos = vcx.mk_bin_op_expr(
                                vir::BinOpKind::Add,
                                common_div,
                                vcx.mk_int::<1>(),
                            );
                            let neg_neg = vcx.mk_bin_op_expr(
                                vir::BinOpKind::Sub,
                                common_div,
                                vcx.mk_int::<1>(),
                            );
                            let rhs_pos = vcx
                                .mk_bin_op_expr(
                                    vir::BinOpKind::CmpGe,
                                    rhs.downcast_ty(),
                                    vcx.mk_int::<0>(),
                                )
                                .downcast_ty();
                            let negative = vcx.mk_ternary_expr(rhs_pos, neg_pos, neg_neg);
                            let lhs_pos = vcx
                                .mk_bin_op_expr(
                                    vir::BinOpKind::CmpGe,
                                    lhs.downcast_ty(),
                                    vcx.mk_int::<0>(),
                                )
                                .downcast_ty();
                            val = vcx.mk_ternary_expr(lhs_pos, val, negative);
                        } else {
                            // `arg1 >= 0 ? arg1 % arg2 : (arg1 % arg2) - (arg2 >= 0 ? arg2 : -arg2)`
                            let rhs_pos = vcx
                                .mk_bin_op_expr(
                                    vir::BinOpKind::CmpGe,
                                    rhs.downcast_ty(),
                                    vcx.mk_int::<0>(),
                                )
                                .downcast_ty();
                            let rhs_abs = vcx.mk_ternary_expr(
                                rhs_pos,
                                rhs,
                                vcx.mk_unary_op_expr(vir::UnOpKind::Neg, rhs),
                            );
                            let negative =
                                vcx.mk_bin_op_expr(vir::BinOpKind::Sub, viper_val, rhs_abs);
                            let lhs_pos = vcx
                                .mk_bin_op_expr(
                                    vir::BinOpKind::CmpGe,
                                    lhs.downcast_ty(),
                                    vcx.mk_int::<0>(),
                                )
                                .downcast_ty();
                            val = vcx.mk_ternary_expr(lhs_pos, val, negative);
                        }
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
        };
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
        let res_ty_task = RustTyDecomposition::from_prim_ty(res_ty);
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
                (e_l_ty.expect_primitive().snap_to_prim)(vcx.mk_local_ex(lhs_decl)),
                (e_r_ty.expect_primitive().snap_to_prim)(vcx.mk_local_ex(rhs_decl)),
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
        let overflowed = if config::check_overflows() {
            vcx.mk_bin_op_expr(vir::BinOpKind::CmpNe, wrapped_val, val)
                .downcast_ty()
        } else {
            vcx.mk_bool::<false>()
        };
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
