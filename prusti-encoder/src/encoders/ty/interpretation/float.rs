use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{BackendInterpretationPair, CallableIdn, CastType, FunctionIdn, VirCtxt};

use crate::encoders::ty::{
    RustTyDecomposition,
    interpretation::bitvec::{BitVecEnc, BitVecSize},
    pure::{DomainBuilder, TyPureEnc},
    use_pure::TyUsePureEnc,
};

pub type FloatDomain<'vir> = &'vir FloatDomainData<'vir>;

#[derive(Debug, Clone, Copy)]
pub struct FloatDomainData<'vir> {
    /// Viper primitive value (the raw bits) as argument. Returns domain.
    pub prim_to_snap: FunctionIdn<'vir, vir::Prim, vir::CSnap>,
    #[allow(unused)]
    pub from_bv: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    pub fp_eq: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub fp_add: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub fp_sub: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub fp_mul: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub fp_div: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub fp_trunc: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    pub fp_is_nan: FunctionIdn<'vir, vir::CSnap, vir::Bool>,
    pub fp_is_infinite: FunctionIdn<'vir, vir::CSnap, vir::Bool>,
    pub fp_lt: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub fp_leq: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub fp_gt: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub fp_geq: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub fp_neg: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    pub fp_abs: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    pub fp_to_real: FunctionIdn<'vir, vir::CSnap, vir::Perm>,
}

pub(crate) fn ty_pure_float<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut DomainBuilder<'vir>,
    float: ty::FloatTy,
    prim_to_snap: FunctionIdn<'vir, vir::Prim, vir::CSnap>,
) -> Result<FloatDomainData<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let i = match float {
        ty::FloatTy::F16 => vcx.alloc_slice(&[
            vcx.alloc(BackendInterpretationPair {
                key: "SMTLIB",
                value: "(_ FloatingPoint 5 11)",
            }),
            vcx.alloc(BackendInterpretationPair {
                key: ("Boogie"),
                value: ("float11e5"),
            }),
        ]),
        ty::FloatTy::F32 => vcx.alloc_slice(&[
            vcx.alloc(BackendInterpretationPair {
                key: "SMTLIB",
                value: "(_ FloatingPoint 8 24)",
            }),
            vcx.alloc(BackendInterpretationPair {
                key: ("Boogie"),
                value: ("float24e8"),
            }),
        ]),
        ty::FloatTy::F64 => vcx.alloc_slice(&[
            vcx.alloc(BackendInterpretationPair {
                key: "SMTLIB",
                value: "(_ FloatingPoint 11 53)",
            }),
            vcx.alloc(BackendInterpretationPair {
                key: ("Boogie"),
                value: ("float53e11"),
            }),
        ]),
        ty::FloatTy::F128 => vcx.alloc_slice(&[
            vcx.alloc(BackendInterpretationPair {
                key: "SMTLIB",
                value: "(_ FloatingPoint 15 113)",
            }),
            vcx.alloc(BackendInterpretationPair {
                key: ("Boogie"),
                value: ("float113e15"),
            }),
        ]),
    };
    builder.set_interpretation(i);

    let self_type = builder.self_type();
    let fp_eq = wrapped_binary(vcx, builder, "eq", vir::TYPE_BOOL, "fp.eq");
    let fp_add = wrapped_binary(vcx, builder, "add", self_type, "fp.add RNE");
    let fp_sub = wrapped_binary(vcx, builder, "sub", self_type, "fp.sub RNE");

    let fp_mul = builder.backend_func(
        "mul",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        Some("fp.mul RNE"),
    );

    let fp_div = builder.backend_func(
        "div",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        Some("fp.div RNE"),
    );

    let fp_trunc = builder.backend_func(
        "trunc",
        builder.self_type(),
        builder.self_type(),
        Some("fp.roundToIntegral RTZ"),
    );

    let fp_is_nan = builder.backend_func(
        "is_nan",
        builder.self_type(),
        vir::TYPE_BOOL,
        Some("fp.isNaN"),
    );

    let fp_is_infinite = builder.backend_func(
        "is_infinite",
        builder.self_type(),
        vir::TYPE_BOOL,
        Some("fp.isInfinite"),
    );

    let fp_lt = wrapped_binary(vcx, builder, "lt", vir::TYPE_BOOL, "fp.lt");
    let fp_leq = wrapped_binary(vcx, builder, "leq", vir::TYPE_BOOL, "fp.leq");
    let fp_geq = wrapped_binary(vcx, builder, "geq", vir::TYPE_BOOL, "fp.geq");
    let fp_gt = wrapped_binary(vcx, builder, "gt", vir::TYPE_BOOL, "fp.gt");
    let fp_neg = wrapped_unary(vcx, builder, "neg", "fp.neg");
    let fp_abs = wrapped_unary(vcx, builder, "abs", "fp.abs");

    let bit_vec = deps.require_dep::<BitVecEnc>(match float {
        ty::FloatTy::F16 => BitVecSize::BitVec16,
        ty::FloatTy::F32 => BitVecSize::BitVec32,
        ty::FloatTy::F64 => BitVecSize::BitVec64,
        ty::FloatTy::F128 => BitVecSize::BitVec128,
    })?;

    let i = match float {
        ty::FloatTy::F16 => "(_ to_fp 5 11)",
        ty::FloatTy::F32 => "(_ to_fp 8 24)",
        ty::FloatTy::F64 => "(_ to_fp 11 53)",
        ty::FloatTy::F128 => "(_ to_fp 15 113)",
    };
    let from_bv = builder.backend_func("from_bv", (bit_vec.domain)(), builder.self_type(), Some(i));

    // Not `fp.to_real`: Z3 cannot reason about it on symbolic floats, and
    // versions before 5.0 can answer `unsat` for satisfiable queries containing
    // it (Z3Prover/z3#9022). The axioms below relate it to the operations.
    let fp_to_real = builder.backend_func("to_real", builder.self_type(), vir::TYPE_PERM, None);

    builder.axiom("prim_to_snap", vir::expr! {
        forall i: [prim_to_snap.arity()] :: {[prim_to_snap](i)} ([prim_to_snap](i)) == ([from_bv]([bit_vec.from_int](i)))
    });

    let data = FloatDomainData {
        prim_to_snap,
        from_bv,
        fp_eq,
        fp_add,
        fp_sub,
        fp_mul,
        fp_div,
        fp_trunc,
        fp_is_nan,
        fp_is_infinite,
        fp_lt,
        fp_leq,
        fp_gt,
        fp_geq,
        fp_neg,
        fp_abs,
        fp_to_real,
    };
    real_value_axioms(vcx, builder, &data, float);
    Ok(data)
}

/// An uninterpreted wrapper around a binary backend operation, so that axioms
/// can trigger on it (Viper rejects interpreted functions in triggers).
fn wrapped_binary<'vir, T: vir::CompType>(
    vcx: &'vir VirCtxt<'vir>,
    builder: &mut DomainBuilder<'vir>,
    name: &str,
    ret: vir::Type<'vir, T>,
    interpretation: &'static str,
) -> FunctionIdn<'vir, (vir::CSnap, vir::CSnap), T> {
    let ty = builder.self_type();
    let backend: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), T> =
        builder.backend_func(&format!("{name}_ieee"), (ty, ty), ret, Some(interpretation));
    let wrapper = builder.function(name, (ty, ty), ret);
    let x = vcx.mk_local_decl("x", ty);
    let y = vcx.mk_local_decl("y", ty);
    let app = wrapper(vcx.mk_local_ex(x), vcx.mk_local_ex(y));
    builder.axiom(
        &format!("{name}_def"),
        vcx.mk_forall_expr(
            vcx.alloc_slice(&[x, y]),
            vcx.alloc_slice(&[vcx.mk_trigger(&[app])]),
            vcx.mk_eq_expr(app, backend(vcx.mk_local_ex(x), vcx.mk_local_ex(y))),
        ),
    );
    wrapper
}

/// Like [`wrapped_binary`], for a unary operation on the float itself.
fn wrapped_unary<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    builder: &mut DomainBuilder<'vir>,
    name: &str,
    interpretation: &'static str,
) -> FunctionIdn<'vir, vir::CSnap, vir::CSnap> {
    let ty = builder.self_type();
    let backend: FunctionIdn<'vir, vir::CSnap, vir::CSnap> =
        builder.backend_func(&format!("{name}_ieee"), ty, ty, Some(interpretation));
    let wrapper = builder.function(name, ty, ty);
    let x = vcx.mk_local_decl("x", ty);
    let app = wrapper(vcx.mk_local_ex(x));
    builder.axiom(
        &format!("{name}_def"),
        vcx.mk_forall_expr(
            vcx.alloc_slice(&[x]),
            vcx.alloc_slice(&[vcx.mk_trigger(&[app])]),
            vcx.mk_eq_expr(app, backend(vcx.mk_local_ex(x))),
        ),
    );
    wrapper
}

/// The precision `p` (significand bits, including the implicit one) and the
/// maximum exponent `emax` of an IEEE 754 binary format.
fn ieee_params(float: ty::FloatTy) -> (u32, u32) {
    match float {
        ty::FloatTy::F16 => (11, 15),
        ty::FloatTy::F32 => (24, 127),
        ty::FloatTy::F64 => (53, 1023),
        ty::FloatTy::F128 => (113, 16383),
    }
}

fn int_const<'vir>(vcx: &'vir VirCtxt<'vir>, value: u128) -> vir::ExprInt<'vir> {
    vcx.mk_const_expr(vir::ConstData::Int(value)).downcast_ty()
}

/// `2^k`, as a product of factors that fit into an integer constant.
fn pow2<'vir>(vcx: &'vir VirCtxt<'vir>, k: u32) -> vir::ExprInt<'vir> {
    const CHUNK: u32 = 120;
    let mut res = int_const(vcx, 1 << (k % CHUNK));
    for _ in 0..k / CHUNK {
        res = vcx
            .mk_bin_op_expr(vir::BinOpKind::Mul, res, int_const(vcx, 1 << CHUNK))
            .downcast_ty();
    }
    res
}

fn rational<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    num: vir::ExprInt<'vir>,
    den: vir::ExprInt<'vir>,
) -> vir::ExprPerm<'vir> {
    vcx.mk_bin_op_expr(vir::BinOpKind::IntIntPermDiv, num, den)
        .downcast_ty()
}

fn perm_bin<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    kind: vir::BinOpKind,
    lhs: vir::ExprPerm<'vir>,
    rhs: vir::ExprPerm<'vir>,
) -> vir::ExprPerm<'vir> {
    vcx.mk_bin_op_expr(kind, lhs, rhs).downcast_ty()
}

fn perm_neg<'vir>(vcx: &'vir VirCtxt<'vir>, e: vir::ExprPerm<'vir>) -> vir::ExprPerm<'vir> {
    vcx.mk_unary_op_expr(vir::UnOpKind::PermNeg, e.upcast_ty())
        .downcast_ty()
}

fn cmp<'vir, T: vir::CompType>(
    vcx: &'vir VirCtxt<'vir>,
    kind: vir::BinOpKind,
    lhs: vir::Expr<'vir, T>,
    rhs: vir::Expr<'vir, T>,
) -> vir::ExprBool<'vir> {
    if kind == vir::BinOpKind::CmpEq {
        vcx.mk_eq_expr(lhs, rhs)
    } else {
        vcx.mk_bin_op_expr(kind, lhs, rhs).downcast_ty()
    }
}

fn implies<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    lhs: vir::ExprBool<'vir>,
    rhs: vir::ExprBool<'vir>,
) -> vir::ExprBool<'vir> {
    vcx.mk_bin_op_expr(vir::BinOpKind::Implies, lhs, rhs)
        .downcast_ty()
}

/// Axioms giving `to_real` the IEEE 754 semantics of round-to-nearest-even:
/// comparisons of finite floats are comparisons of their values, and a sum or
/// difference of finite floats is finite and within a relative error of
/// `2^-p` of the exact result, unless that exceeds the overflow threshold.
/// (Subnormal results of additions are exact, so no absolute error term is
/// needed.) This keeps the reasoning in linear real arithmetic.
fn real_value_axioms<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    builder: &mut DomainBuilder<'vir>,
    data: &FloatDomainData<'vir>,
    float: ty::FloatTy,
) {
    let (p, emax) = ieee_params(float);
    let ty = builder.self_type();
    let real = |e| (data.fp_to_real)(e);
    let finite = |e| {
        vcx.mk_conj(&[
            vcx.mk_unary_op_expr(vir::UnOpKind::Not, (data.fp_is_nan)(e).upcast_ty())
                .downcast_ty(),
            vcx.mk_unary_op_expr(vir::UnOpKind::Not, (data.fp_is_infinite)(e).upcast_ty())
                .downcast_ty(),
        ])
    };
    let zero = vcx.mk_const_expr(vir::ConstData::NoPerm).downcast_ty();
    let abs = |e: vir::ExprPerm<'vir>| {
        vcx.mk_ternary_expr(
            cmp(vcx, vir::BinOpKind::CmpGe, e, zero),
            e,
            perm_neg(vcx, e),
        )
    };
    let eps = rational(vcx, int_const(vcx, 1), pow2(vcx, p));
    // Halfway between the largest finite value and the next power of two.
    let overflow = rational(
        vcx,
        vcx.mk_bin_op_expr(
            vir::BinOpKind::Sub,
            pow2(vcx, emax + 1),
            pow2(vcx, emax - p),
        )
        .downcast_ty(),
        int_const(vcx, 1),
    );
    let x = vcx.mk_local_decl("x", ty);
    let y = vcx.mk_local_decl("y", ty);
    let (xe, ye) = (vcx.mk_local_ex(x), vcx.mk_local_ex(y));

    for (name, op, kind) in [
        ("eq", data.fp_eq, vir::BinOpKind::CmpEq),
        ("lt", data.fp_lt, vir::BinOpKind::CmpLt),
        ("leq", data.fp_leq, vir::BinOpKind::CmpLe),
        ("geq", data.fp_geq, vir::BinOpKind::CmpGe),
        ("gt", data.fp_gt, vir::BinOpKind::CmpGt),
    ] {
        let app = op(xe, ye);
        let body = implies(
            vcx,
            vcx.mk_conj(&[finite(xe), finite(ye)]),
            vcx.mk_eq_expr(app, cmp(vcx, kind, real(xe), real(ye))),
        );
        builder.axiom(&format!("{name}_real"), forall(vcx, &[x, y], app, body));
    }

    for (name, op, kind) in [
        ("add", data.fp_add, vir::BinOpKind::PermAdd),
        ("sub", data.fp_sub, vir::BinOpKind::PermSub),
    ] {
        let app = op(xe, ye);
        let exact = perm_bin(vcx, kind, real(xe), real(ye));
        let error = perm_bin(vcx, vir::BinOpKind::PermSub, real(app), exact);
        let bound = perm_bin(vcx, vir::BinOpKind::PermMul, eps, abs(exact));
        let body = implies(
            vcx,
            vcx.mk_conj(&[
                finite(xe),
                finite(ye),
                cmp(vcx, vir::BinOpKind::CmpLt, abs(exact), overflow),
            ]),
            vcx.mk_conj(&[
                finite(app),
                cmp(vcx, vir::BinOpKind::CmpLe, perm_neg(vcx, bound), error),
                cmp(vcx, vir::BinOpKind::CmpLe, error, bound),
            ]),
        );
        builder.axiom(&format!("{name}_real"), forall(vcx, &[x, y], app, body));
    }

    for (name, op, value) in [
        ("neg", data.fp_neg, perm_neg(vcx, real(xe))),
        ("abs", data.fp_abs, abs(real(xe))),
    ] {
        let app = op(xe);
        let body = implies(
            vcx,
            finite(xe),
            vcx.mk_conj(&[finite(app), vcx.mk_eq_expr(real(app), value)]),
        );
        builder.axiom(&format!("{name}_real"), forall(vcx, &[x], app, body));
    }
}

fn forall<'vir, T: vir::CompType>(
    vcx: &'vir VirCtxt<'vir>,
    qvars: &[vir::LocalDecl<'vir, vir::CSnap>],
    trigger: vir::Expr<'vir, T>,
    body: vir::ExprBool<'vir>,
) -> vir::ExprBool<'vir> {
    vcx.mk_forall_expr(
        vcx.alloc_slice(qvars),
        vcx.alloc_slice(&[vcx.mk_trigger(&[trigger])]),
        body,
    )
}

/// The exact value of the float with the given bits, or `None` for NaN and the
/// infinities.
fn float_value<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    float: ty::FloatTy,
    bits: u128,
) -> Option<vir::ExprPerm<'vir>> {
    let (p, emax) = ieee_params(float);
    let width = float.bit_width() as u32;
    let mant_bits = p - 1;
    let exp_bits = width - p;
    let mant = bits & ((1 << mant_bits) - 1);
    let exp = (bits >> mant_bits) & ((1 << exp_bits) - 1);
    if exp == (1 << exp_bits) - 1 {
        return None;
    }
    // The value is `mant * 2^shift`; subnormals have the minimum exponent.
    let (mant, shift) = if exp == 0 {
        (mant, 1 - emax as i64 - mant_bits as i64)
    } else {
        (
            mant | (1 << mant_bits),
            exp as i64 - emax as i64 - mant_bits as i64,
        )
    };
    let shift_abs = shift.unsigned_abs() as u32;
    let value = if shift >= 0 {
        rational(
            vcx,
            vcx.mk_bin_op_expr(
                vir::BinOpKind::Mul,
                int_const(vcx, mant),
                pow2(vcx, shift_abs),
            )
            .downcast_ty(),
            int_const(vcx, 1),
        )
    } else {
        rational(vcx, int_const(vcx, mant), pow2(vcx, shift_abs))
    };
    Some(if (bits >> (width - 1)) & 1 == 1 {
        perm_neg(vcx, value)
    } else {
        value
    })
}

/// Emits the exact value of a float constant: `to_real(prim_to_snap(bits))`.
pub struct FloatLitEnc;

impl TaskEncoder for FloatLitEnc {
    task_encoder::encoder_cache!(FloatLitEnc);
    const ENCODER_NAME: &'static str = "float literal encoder";

    type TaskDescription<'vir> = (ty::FloatTy, u128);

    type OutputFullLocal<'vir> = Option<&'vir vir::DomainData<'vir>>;

    type OutputFullDependency<'vir> = ();

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let (float, bits) = *task_key;
            let ty = match float {
                ty::FloatTy::F16 => vcx.tcx().types.f16,
                ty::FloatTy::F32 => vcx.tcx().types.f32,
                ty::FloatTy::F64 => vcx.tcx().types.f64,
                ty::FloatTy::F128 => vcx.tcx().types.f128,
            };
            let domain = *deps
                .require_dep::<TyUsePureEnc>(RustTyDecomposition::from_prim_ty(ty))?
                .expect_float();
            let Some(value) = float_value(vcx, float, bits) else {
                return Ok((None, ()));
            };
            let snap = (domain.prim_to_snap)(int_const(vcx, bits).upcast_ty());
            let name = vir::vir_format!(vcx, "s_Float_{}_lit_{bits:x}", float.name_str());
            let axiom = vcx.mk_domain_axiom(
                vir::ViperIdent::new(vir::vir_format!(vcx, "{name}_value")),
                vcx.mk_eq_expr((domain.fp_to_real)(snap), value),
            );
            Ok((
                Some(vcx.mk_domain(
                    vir::ViperIdent::new(name),
                    &[],
                    vcx.alloc_slice(&[axiom]),
                    &[],
                    None,
                )),
                (),
            ))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program)
            .into_iter()
            .flatten()
        {
            program.add_domain(output);
        }
    }
}
