use prusti_rustc_interface::{
    middle::ty,
    middle::mir,
};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use vir::{UnknownArity, FunctionIdent, CallableIdent};

pub struct MirBuiltinEncoder;

#[derive(Clone, Debug)]
pub enum MirBuiltinEncoderError {
    Unsupported,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum MirBuiltinEncoderTask<'tcx> {
    UnOp(ty::Ty<'tcx>, mir::UnOp, ty::Ty<'tcx>),
    BinOp(ty::Ty<'tcx>, mir::BinOp, ty::Ty<'tcx>, ty::Ty<'tcx>),
    CheckedBinOp(ty::Ty<'tcx>, mir::BinOp, ty::Ty<'tcx>, ty::Ty<'tcx>),
}

#[derive(Clone, Debug)]
pub struct MirBuiltinEncoderOutputRef<'vir> {
    pub function: FunctionIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for MirBuiltinEncoderOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirBuiltinEncoderOutput<'vir> {
    pub function: vir::Function<'vir>,
}

use std::cell::RefCell;

thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirBuiltinEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for MirBuiltinEncoder {
    type TaskDescription<'vir> = MirBuiltinEncoderTask<'vir>;

    type OutputRef<'vir> = MirBuiltinEncoderOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirBuiltinEncoderOutput<'vir>;

    type EncodingError = MirBuiltinEncoderError;

    fn with_cache<'tcx: 'vir, 'vir, F, R>(f: F) -> R
        where F: FnOnce(&'vir task_encoder::CacheRef<'tcx, 'vir, MirBuiltinEncoder>) -> R,
    {
        CACHE.with(|cache| {
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            let cache = unsafe { std::mem::transmute(cache) };
            f(cache)
        })
    }

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.clone()
    }

    fn do_encode_full<'tcx: 'vir, 'vir: 'tcx>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir>>,
    )> {
        vir::with_vcx(|vcx| {
            match *task_key {
                MirBuiltinEncoderTask::UnOp(res_ty, op, operand_ty) => {
                    assert_eq!(res_ty, operand_ty);
                    let function = Self::handle_un_op(vcx, deps, *task_key, op, operand_ty);
                    Ok((MirBuiltinEncoderOutput { function }, ()))
                }
                MirBuiltinEncoderTask::BinOp(res_ty, op, l_ty, r_ty) => {
                    let function = Self::handle_bin_op(vcx, deps, *task_key, res_ty, op, l_ty, r_ty);
                    Ok((MirBuiltinEncoderOutput { function }, ()))
                }
                MirBuiltinEncoderTask::CheckedBinOp(res_ty, op, l_ty, r_ty) => {
                    let function = Self::handle_checked_bin_op(vcx, deps, *task_key, res_ty, op, l_ty, r_ty);
                    Ok((MirBuiltinEncoderOutput { function }, ()))
                }
            }
        })
    }
}

// TODO: this function is also useful for the type encoder, extract?
fn int_name<'tcx>(ty: ty::Ty<'tcx>) -> &'static str {
    match ty.kind() {
        ty::TyKind::Bool => "bool",
        ty::TyKind::Int(kind) => kind.name_str(),
        ty::TyKind::Uint(kind) => kind.name_str(),
        _ => unreachable!("non-integer type"),
    }
}

impl MirBuiltinEncoder {
    fn handle_un_op<'vir: 'tcx, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
        key: <Self as TaskEncoder>::TaskKey<'tcx>,
        op: mir::UnOp,
        ty: ty::Ty<'tcx>
    ) -> vir::Function<'vir> {
        let e_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
            ty,
        ).unwrap();

        let name = vir::vir_format!(vcx, "mir_unop_{op:?}_{}", int_name(ty));
        let arity = UnknownArity::new(vcx.alloc_slice(&[e_ty.snapshot]));
        let function = FunctionIdent::new(name, arity);
        deps.emit_output_ref::<Self>(key, MirBuiltinEncoderOutputRef {
            function,
        });

        let e_res_ty = &e_ty;
        let prim_res_ty = e_res_ty.expect_prim();
        let snap_arg = vcx.mk_local_ex("arg");
        let prim_arg = e_ty.expect_prim().snap_to_prim.apply(vcx, [snap_arg]);
        // `prim_to_snap(-snap_to_prim(arg))`
        let mut val = prim_res_ty.prim_to_snap.apply(vcx,
            [vcx.alloc(vir::ExprData::UnOp(vcx.alloc(vir::UnOpData {
                kind: vir::UnOpKind::from(op),
                expr: prim_arg,
            })))]
        );
        // Can overflow when doing `- iN::MIN -> iN::MIN`. There is no
        // `CheckedUnOp`, instead the compiler puts an `TerminatorKind::Assert`
        // before in debug mode. We should still produce the correct result in
        // release mode, which the code under this branch does.
        if op == mir::UnOp::Neg && ty.is_signed() {
            let bound = vcx.get_min_int(prim_res_ty.prim_type, ty.kind());
            // `snap_to_prim(arg) == -iN::MIN`
            let cond = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                kind: vir::BinOpKind::CmpEq,
                lhs: prim_arg,
                rhs: bound,
            })));
            // `snap_to_prim(arg) == -iN::MIN ? arg :
            // prim_to_snap(-snap_to_prim(arg))`
            val = vcx.alloc(vir::ExprData::Ternary(vcx.alloc(vir::TernaryData {
                cond,
                then: snap_arg,
                else_: val,
            })))
        }

        vcx.alloc(vir::FunctionData {
            name,
            args: vcx.alloc_slice(&[vcx.mk_local_decl("arg", e_ty.snapshot)]),
            ret: e_res_ty.snapshot,
            pres: &[],
            posts: &[],
            expr: Some(val),
        })
    }

    fn handle_bin_op<'vir: 'tcx, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
        key: <Self as TaskEncoder>::TaskKey<'tcx>,
        res_ty: ty::Ty<'tcx>,
        op: mir::BinOp,
        l_ty: ty::Ty<'tcx>,
        r_ty: ty::Ty<'tcx>,
    ) -> vir::Function<'vir> {
        use mir::BinOp::*;
        let e_l_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
            l_ty,
        ).unwrap();
        let e_r_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
            r_ty,
        ).unwrap();
        let e_res_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
            res_ty,
        ).unwrap();
        let prim_res_ty = e_res_ty.expect_prim();

        let name = vir::vir_format!(vcx, "mir_binop_{op:?}_{}_{}", int_name(l_ty), int_name(r_ty));
        let arity = UnknownArity::new(vcx.alloc_slice(&[e_l_ty.snapshot, e_r_ty.snapshot]));
        let function = FunctionIdent::new(name, arity);
        deps.emit_output_ref::<Self>(key, MirBuiltinEncoderOutputRef {
            function,
        });
        let lhs = e_l_ty.expect_prim().snap_to_prim.apply(vcx,
            [vcx.mk_local_ex("arg1")],
        );
        let mut rhs = e_r_ty.expect_prim().snap_to_prim.apply(vcx,
            [vcx.mk_local_ex("arg2")],
        );
        if matches!(op, Shl | Shr) {
            // RHS must be smaller than the bit width of the LHS, this is
            // implicit in the `Shl` and `Shr` operators.
            rhs = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                kind: vir::BinOpKind::Mod,
                lhs: rhs,
                rhs: vcx.get_bit_width_int(e_l_ty.expect_prim().prim_type, l_ty.kind()),
            })));
        }
        let val = prim_res_ty.prim_to_snap.apply(vcx,
            [vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                kind: vir::BinOpKind::from(op),
                lhs,
                rhs,
            })))]
        );
        let (pres, val) = match op {
            // Overflow well defined as wrapping (implicit) and for the shifts
            // the RHS will be masked to the bit width.
            Add | Sub | Mul | Shl | Shr =>
                (Vec::new(), Self::get_wrapped_val(vcx, val, prim_res_ty.prim_type, res_ty)),
            // Undefined behavior to overflow (need precondition)
            AddUnchecked | SubUnchecked | MulUnchecked => {
                let min = vcx.get_min_int(prim_res_ty.prim_type, res_ty.kind());
                // `(arg1 op arg2) >= -iN::MIN`
                let lower_bound = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                    kind: vir::BinOpKind::CmpGe,
                    lhs: val,
                    rhs: min,
                })));
                let max = vcx.get_max_int(prim_res_ty.prim_type, res_ty.kind());
                // `(arg1 op arg2) <= iN::MAX`
                let upper_bound = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                    kind: vir::BinOpKind::CmpLe,
                    lhs: val,
                    rhs: max,
                })));
                (vec![lower_bound, upper_bound], val)
            }
            // Overflow is well defined as wrapping (implicit), but shifting by
            // more than the bit width (or less than 0) is undefined behavior.
            ShlUnchecked | ShrUnchecked => {
                let min = vcx.mk_int::<0>();
                // `arg2 >= 0`
                let lower_bound = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                    kind: vir::BinOpKind::CmpGe,
                    lhs: rhs,
                    rhs: min,
                })));
                let max = vcx.get_bit_width_int(e_l_ty.expect_prim().prim_type, l_ty.kind());
                // `arg2 < bit_width(arg1)`
                let upper_bound = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                    kind: vir::BinOpKind::CmpLt,
                    lhs: rhs,
                    rhs: max,
                })));
                (vec![lower_bound, upper_bound], Self::get_wrapped_val(vcx, val, prim_res_ty.prim_type, res_ty))
            }
            // Could divide by zero or overflow if divisor is `-1`
            Div | Rem => {
                // `0 != arg2 `
                let pre = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                    kind: vir::BinOpKind::CmpNe,
                    lhs: vcx.mk_int::<0>(),
                    rhs,
                })));
                let mut pres = vec![pre];
                if res_ty.is_signed() {
                    let min = vcx.get_min_int(prim_res_ty.prim_type, res_ty.kind());
                    // `arg1 != -iN::MIN`
                    let arg1_cond = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                        kind: vir::BinOpKind::CmpNe,
                        lhs,
                        rhs: min,
                    })));
                    // `-1 != arg2 `
                    let arg2_cond = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                        kind: vir::BinOpKind::CmpNe,
                        lhs: vcx.mk_int::<-1>(),
                        rhs,
                    })));
                    // `-1 != arg2 || arg1 != -iN::MIN`
                    let pre = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                        kind: vir::BinOpKind::Or,
                        rhs: arg2_cond,
                        lhs: arg1_cond,
                    })));
                    pres.push(pre);
                }
                (pres, val)
            }
            // Cannot overflow and no undefined behavior
            BitXor | BitAnd | BitOr | Eq | Lt | Le | Ne | Ge | Gt | Offset =>
                (Vec::new(), val),
        };
        vcx.alloc(vir::FunctionData {
            name,
            args: vcx.alloc_slice(&[
                vcx.mk_local_decl("arg1", e_l_ty.snapshot),
                vcx.mk_local_decl("arg2", e_r_ty.snapshot),
            ]),
            ret: e_res_ty.snapshot,
            pres: vcx.alloc_slice(&pres),
            posts: &[],
            expr: Some(val),
        })
    }

    fn handle_checked_bin_op<'vir: 'tcx, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
        key: <Self as TaskEncoder>::TaskKey<'tcx>,
        res_ty: ty::Ty<'tcx>,
        op: mir::BinOp,
        l_ty: ty::Ty<'tcx>,
        r_ty: ty::Ty<'tcx>,
    ) -> vir::Function<'vir> {
        // `op` can only be `Add`, `Sub` or `Mul`
        assert!(matches!(op, mir::BinOp::Add | mir::BinOp::Sub | mir::BinOp::Mul));
        let e_l_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
            l_ty,
        ).unwrap();
        let e_r_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
            r_ty,
        ).unwrap();

        let name = vir::vir_format!(vcx, "mir_checkedbinop_{op:?}_{}_{}", int_name(l_ty), int_name(r_ty));
        let arity = UnknownArity::new(vcx.alloc_slice(&[e_l_ty.snapshot, e_r_ty.snapshot]));
        let function = FunctionIdent::new(name, arity);
        deps.emit_output_ref::<Self>(key, MirBuiltinEncoderOutputRef {
            function,
        });

        let e_res_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
            res_ty,
        ).unwrap();
        // The result of a checked add will always be `(T, bool)`, get the `T`
        // type
        let rvalue_pure_ty = res_ty.tuple_fields()[0];
        let bool_ty = res_ty.tuple_fields()[1];
        assert!(bool_ty.is_bool());

        let e_rvalue_pure_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
            rvalue_pure_ty,
        ).unwrap();
        let bool_cons = deps.require_ref::<crate::encoders::TypeEncoder>(
            bool_ty,
        ).unwrap().expect_prim().prim_to_snap;

        // Unbounded value
        let val_exp = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
            kind: vir::BinOpKind::from(op),
            lhs: e_l_ty.expect_prim().snap_to_prim.apply(vcx,
                [vcx.mk_local_ex("arg1")],
            ),
            rhs: e_r_ty.expect_prim().snap_to_prim.apply(vcx,
                [vcx.mk_local_ex("arg2")],
            ),
        })));
        let val_str = vir::vir_format!(vcx, "val");
        let val = vcx.mk_local_ex(val_str);
        // Wrapped value
        let wrapped_val_exp = Self::get_wrapped_val(vcx, val, e_rvalue_pure_ty.expect_prim().prim_type, rvalue_pure_ty);
        let wrapped_val_str = vir::vir_format!(vcx, "wrapped_val");
        let wrapped_val = vcx.mk_local_ex(wrapped_val_str);
        let wrapped_val_snap = e_rvalue_pure_ty.expect_prim().prim_to_snap.apply(vcx,
            [wrapped_val],
        );
        // Overflowed?
        let overflowed = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
            kind: vir::BinOpKind::CmpNe,
            lhs: wrapped_val,
            rhs: val,
        })));
        let overflowed_snap = bool_cons.apply(vcx, [overflowed]);
        // `tuple(prim_to_snap(wrapped_val), wrapped_val != val)`
        let tuple = e_res_ty.expect_structlike().field_snaps_to_snap.apply(vcx,
            &[wrapped_val_snap, overflowed_snap]
        );
        // `let wrapped_val == (val ..) in $tuple`
        let inner_let = vcx.alloc(vir::ExprData::Let(vcx.alloc(vir::LetGenData {
            name: wrapped_val_str,
            val: wrapped_val_exp,
            expr: tuple,
        })));

        vcx.alloc(vir::FunctionData {
            name,
            args: vcx.alloc_slice(&[
                vcx.mk_local_decl("arg1", e_l_ty.snapshot),
                vcx.mk_local_decl("arg2", e_r_ty.snapshot),
            ]),
            ret: e_res_ty.snapshot,
            pres: &[],
            posts: &[],
            expr: Some(vcx.alloc(vir::ExprData::Let(vcx.alloc(vir::LetGenData {
                name: val_str,
                val: val_exp,
                expr: inner_let,
            })))),
        })
    }

    /// Wrap the value in the range of the type, e.g. `uN` is wrapped in the
    /// range `uN::MIN..=uN::MAX` using modulo. For signed integers, the range
    /// is `iN::MIN..=iN::MAX` and the value is wrapped using two's complement.
    fn get_wrapped_val<'vir, 'tcx>(vcx: &'vir vir::VirCtxt<'tcx>, mut exp: &'vir vir::ExprData<'vir>, ty: vir::Type, rust_ty: ty::Ty) -> &'vir vir::ExprData<'vir> {
        let shift_amount = vcx.get_signed_shift_int(ty, rust_ty.kind());
        if let Some(half) = shift_amount {
            exp = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                kind: vir::BinOpKind::Add,
                lhs: exp,
                rhs: half,
            })));
        }
        let modulo_val = vcx.get_modulo_int(ty, rust_ty.kind());
        exp = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
            kind: vir::BinOpKind::Mod,
            lhs: exp,
            rhs: modulo_val,
        })));
        if let Some(half) = shift_amount {
            exp = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                kind: vir::BinOpKind::Sub,
                lhs: exp,
                rhs: half,
            })));
        }
        exp
    }
}
