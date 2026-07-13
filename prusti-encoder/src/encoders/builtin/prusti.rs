use prusti_interface::environment::EnvQuery;
use prusti_rustc_interface::{abi, middle::ty, span::def_id::DefId};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

use crate::encoders::ty::{
    RustTyDecomposition, generics::GArgs, interpretation::float::FloatDomain,
    use_pure::TyUsePureEnc,
};

/// Marker for the "mode" spec builtins (`old`/`rel`/`before_expiry`); these
/// are pure-only and handled by the pure encoder.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum Mode {
    Old,
    Rel(usize),
    BeforeExpiry,
}

/// A `prusti_contracts` builtin, classified from the callee. The operand-based
/// ones are encoded by [`PrustiBuiltinEnc`]; the rest (quantifiers, spec
/// blocks, mode markers) are pure-only.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum PrustiBuiltin {
    Forall,
    Exists,
    SpecBlock,
    SnapshotEquality,
    GhostNew,
    GhostEq,
    GhostNe,
    ModeStart(Mode),
    ModeEnd(Mode),
    IsNaN(ty::FloatTy),
    IsInfinite(ty::FloatTy),
    FlAbs(ty::FloatTy),
    FlToReal,
    RealMul,
    RealEq,
    RealNe,
    RealSub,
    RealAdd,
    RealDiv,
    RealNeg,
    RealLt,
    RealLe,
    RealGt,
    RealGe,
    RealCmp,
    RealPartialCmp,
    IntFrom,
    IntMul,
    IntEq,
    IntNe,
    IntSub,
    IntAdd,
    IntDiv,
    IntRem,
    IntNeg,
    IntLt,
    IntLe,
    IntGt,
    IntGe,
    IntCmp,
    IntPartialCmp,
}

impl PrustiBuiltin {
    /// Classifies the call to `def_id`. Returns `None` iff the called function
    /// does not belong to the `prusti_contracts` crate (a trait method call is
    /// attributed to the crate of the `impl` it relies on, e.g. `PartialOrd::le`
    /// on `Int` belongs to `prusti_contracts` even though the default `le` body
    /// lives in `core`).
    pub fn new(def_id: DefId, args: GArgs<'_>) -> Option<Self> {
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let env_query = EnvQuery::new(tcx);
            // The trait impl the call relies on (if any), used both to
            // attribute the call to a crate and to name the impl's self type.
            let impl_def_id = env_query.find_trait_impl_of_method_call(
                args.context().typing_env(),
                def_id,
                tcx.mk_args(args.args()),
            );
            if tcx.crate_name(impl_def_id.unwrap_or(def_id).krate).as_str() != "prusti_contracts" {
                return None;
            }

            let item_name = tcx.item_name(def_id);
            // The self type of the impl the call relies on: the selected
            // trait impl for trait method calls (whether or not it overrides
            // the method), or the enclosing inherent impl otherwise.
            let impl_type_name = impl_def_id
                .map(|impl_def_id| env_query.find_impl_self_type_name(impl_def_id))
                .or_else(|| env_query.find_impl_type_name(def_id));
            let rel_index = || {
                args.args()[0]
                    .expect_const()
                    .to_value()
                    .valtree
                    .try_to_scalar_int()
                    .unwrap()
                    .to_target_usize(tcx) as usize
            };
            Some(match (impl_type_name.as_deref(), item_name.as_str()) {
                (None, "forall") => Self::Forall,
                (None, "exists") => Self::Exists,
                (None, "spec_block") => Self::SpecBlock,
                (None, "snapshot_equality") => Self::SnapshotEquality,
                (Some("prusti_contracts::Ghost<T>"), "new") => Self::GhostNew,
                (Some("prusti_contracts::Ghost<T>"), "eq") => Self::GhostEq,
                (Some("prusti_contracts::Ghost<T>"), "ne") => Self::GhostNe,
                (None, "old_start") => Self::ModeStart(Mode::Old),
                (None, "old_end") => Self::ModeEnd(Mode::Old),
                (None, "rel_start") => Self::ModeStart(Mode::Rel(rel_index())),
                (None, "rel_end") => Self::ModeEnd(Mode::Rel(rel_index())),
                (None, "before_expiry_start") => Self::ModeStart(Mode::BeforeExpiry),
                (None, "before_expiry_end") => Self::ModeEnd(Mode::BeforeExpiry),
                (None, "f16_is_nan") => Self::IsNaN(ty::FloatTy::F16),
                (None, "f32_is_nan") => Self::IsNaN(ty::FloatTy::F32),
                (None, "f64_is_nan") => Self::IsNaN(ty::FloatTy::F64),
                (None, "f128_is_nan") => Self::IsNaN(ty::FloatTy::F128),
                (None, "f16_is_infinite") => Self::IsInfinite(ty::FloatTy::F16),
                (None, "f32_is_infinite") => Self::IsInfinite(ty::FloatTy::F32),
                (None, "f64_is_infinite") => Self::IsInfinite(ty::FloatTy::F64),
                (None, "f128_is_infinite") => Self::IsInfinite(ty::FloatTy::F128),
                (None, "f16_abs") => Self::FlAbs(ty::FloatTy::F16),
                (None, "f32_abs") => Self::FlAbs(ty::FloatTy::F32),
                (None, "f64_abs") => Self::FlAbs(ty::FloatTy::F64),
                (None, "f128_abs") => Self::FlAbs(ty::FloatTy::F128),
                (Some("prusti_contracts::Int"), "from") => Self::IntFrom,
                (Some("prusti_contracts::Int"), "mul") => Self::IntMul,
                (Some("prusti_contracts::Int"), "eq") => Self::IntEq,
                (Some("prusti_contracts::Int"), "ne") => Self::IntNe,
                (Some("prusti_contracts::Int"), "sub") => Self::IntSub,
                (Some("prusti_contracts::Int"), "add") => Self::IntAdd,
                (Some("prusti_contracts::Int"), "div") => Self::IntDiv,
                (Some("prusti_contracts::Int"), "rem") => Self::IntRem,
                (Some("prusti_contracts::Int"), "neg") => Self::IntNeg,
                (Some("prusti_contracts::Int"), "lt") => Self::IntLt,
                (Some("prusti_contracts::Int"), "le") => Self::IntLe,
                (Some("prusti_contracts::Int"), "gt") => Self::IntGt,
                (Some("prusti_contracts::Int"), "ge") => Self::IntGe,
                (Some("prusti_contracts::Int"), "cmp") => Self::IntCmp,
                (Some("prusti_contracts::Int"), "partial_cmp") => Self::IntPartialCmp,
                (Some("prusti_contracts::Real"), "from") => Self::FlToReal,
                (Some("prusti_contracts::Real"), "mul") => Self::RealMul,
                (Some("prusti_contracts::Real"), "eq") => Self::RealEq,
                (Some("prusti_contracts::Real"), "ne") => Self::RealNe,
                (Some("prusti_contracts::Real"), "sub") => Self::RealSub,
                (Some("prusti_contracts::Real"), "add") => Self::RealAdd,
                (Some("prusti_contracts::Real"), "div") => Self::RealDiv,
                (Some("prusti_contracts::Real"), "neg") => Self::RealNeg,
                (Some("prusti_contracts::Real"), "lt") => Self::RealLt,
                (Some("prusti_contracts::Real"), "le") => Self::RealLe,
                (Some("prusti_contracts::Real"), "gt") => Self::RealGt,
                (Some("prusti_contracts::Real"), "ge") => Self::RealGe,
                (Some("prusti_contracts::Real"), "cmp") => Self::RealCmp,
                (Some("prusti_contracts::Real"), "partial_cmp") => Self::RealPartialCmp,
                // TODO: support the remaining builtins (e.g. `Ghost`
                // dereferencing, `Seq`, `Map`, `Set`).
                (impl_type_name, other) => todo!(
                    "unsupported `prusti_contracts` function {}{other}",
                    impl_type_name.map(|n| format!("{n}::")).unwrap_or_default(),
                ),
            })
        })
    }
}

/// Encodes the operand-based `prusti_contracts` builtins (`Int`/`Real`
/// arithmetic and comparisons, the float classification functions, and
/// `snapshot_equality`) as snapshot expressions with one hole per operand.
/// The holes are filled by `reify`ing the expression with the operand
/// snapshots encoded by the caller, so the same (cached) output serves both
/// the pure and the impure encoder.
pub struct PrustiBuiltinEnc;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct PrustiBuiltinTask<'vir> {
    pub builtin: PrustiBuiltin,
    pub def_id: DefId,
    pub args: GArgs<'vir>,
}

/// The operand snapshots filling the holes of a [`PrustiBuiltinExpr`].
type PrustiBuiltinOperands<'vir> = &'vir [vir::ExprSnap<'vir>];

/// A snapshot expression with one hole (`Lazy` node) per operand; the holes
/// are filled with [`PrustiBuiltinExpr::apply`].
#[derive(Clone, Copy, Debug)]
pub struct PrustiBuiltinExpr<'vir>(
    vir::ExprGenSnap<'vir, PrustiBuiltinOperands<'vir>, vir::ExprKind<'vir>>,
);

impl<'vir> PrustiBuiltinExpr<'vir> {
    /// Fills the operand holes with `operands`, in the caller's
    /// `Curr`/`Next` expression domain.
    pub fn apply<Curr: 'vir, Next: 'vir>(
        self,
        vcx: &'vir vir::VirCtxt<'vir>,
        operands: &[vir::ExprGenSnap<'vir, Curr, Next>],
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        // SAFETY: reinterpret the kind of the operand holes (and thus of the
        // expression itself) from hole-free operands to operands in the
        // caller's domain: the `Lazy` operand holes only index into the
        // operand slice and splice the operand's `kind` verbatim, so they are
        // oblivious to any holes the operands themselves may carry.
        let expr = unsafe {
            std::mem::transmute::<
                vir::ExprGen<'vir, &'vir [vir::ExprSnap<'vir>], vir::ExprKind<'vir>, vir::Snap>,
                vir::ExprGen<
                    'vir,
                    &'vir [vir::ExprGenSnap<'vir, Curr, Next>],
                    vir::ExprKindGen<'vir, Curr, Next>,
                    vir::Snap,
                >,
            >(self.0)
        };
        use vir::Reify;
        expr.reify(vcx, vcx.alloc_slice(operands))
    }
}

type ExprRet<'vir, T> = vir::ExprGen<'vir, PrustiBuiltinOperands<'vir>, vir::ExprKind<'vir>, T>;

type EncResult<'vir, T> = Result<T, EncodeFullError<'vir, PrustiBuiltinEnc>>;

impl TaskEncoder for PrustiBuiltinEnc {
    task_encoder::encoder_cache!(PrustiBuiltinEnc);
    const ENCODER_NAME: &'static str = "prusti builtin encoder";

    type TaskDescription<'vir> = PrustiBuiltinTask<'vir>;

    type OutputFullDependency<'vir> = PrustiBuiltinExpr<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let PrustiBuiltinTask {
                builtin,
                def_id,
                args,
            } = *task_key;
            let tcx = vcx.tcx();
            let sig = tcx
                .fn_sig(def_id)
                .instantiate(tcx, args.args())
                .skip_binder();

            // One hole per operand, typed with the operand's snapshot type.
            let operands = (0..sig.inputs().len())
                .map(|i| {
                    let ty = RustTyDecomposition::from_ty(sig.inputs()[i], args.context());
                    let snap_ty = deps.require_ref::<TyUsePureEnc>(ty)?.snapshot;
                    Ok(vcx.mk_lazy_expr(
                        vir::vir_format!(vcx, "prusti_builtin_operand_{i}"),
                        snap_ty,
                        Box::new(move |_vcx, lctx: PrustiBuiltinOperands<'vir>| {
                            assert_eq!(lctx.len(), sig.inputs().len());
                            lctx[i].kind
                        }),
                    ))
                })
                .collect::<EncResult<'vir, Vec<ExprRet<'vir, vir::Snap>>>>()?;
            let operands = &operands;

            let e_input = |deps: &mut TaskEncoderDependencies<'vir, Self>, i: usize| {
                deps.require_dep::<TyUsePureEnc>(RustTyDecomposition::from_ty(
                    sig.inputs()[i],
                    args.context(),
                ))
            };

            let res: ExprRet<'vir, vir::CSnap> = match builtin {
                PrustiBuiltin::Forall
                | PrustiBuiltin::Exists
                | PrustiBuiltin::SpecBlock
                | PrustiBuiltin::ModeStart(_)
                | PrustiBuiltin::ModeEnd(_) => {
                    unreachable!("pure-only builtin in `PrustiBuiltinEnc`: {builtin:?}")
                }
                PrustiBuiltin::SnapshotEquality => {
                    let lhs = e_input(deps, 0)?
                        .expect_immref()
                        .value_access(operands[0].downcast_ty());
                    let rhs = e_input(deps, 1)?
                        .expect_immref()
                        .value_access(operands[1].downcast_ty());
                    vcx.mk_eq_expr(lhs, rhs).upcast_ty()
                }
                PrustiBuiltin::GhostNew => {
                    let ghost = deps.require_dep::<TyUsePureEnc>(RustTyDecomposition::from_ty(
                        sig.output(),
                        args.context(),
                    ))?;
                    ghost
                        .expect_structlike()
                        .field_snaps_to_snap(vec![operands[0]])
                }
                PrustiBuiltin::GhostEq | PrustiBuiltin::GhostNe => {
                    let bin_op = match builtin {
                        PrustiBuiltin::GhostEq => vir::BinOpKind::CmpEq,
                        PrustiBuiltin::GhostNe => vir::BinOpKind::CmpNe,
                        _ => unreachable!(),
                    };
                    let lhs = e_input(deps, 0)?
                        .expect_immref()
                        .value_access(operands[0].downcast_ty());
                    let rhs = e_input(deps, 1)?
                        .expect_immref()
                        .value_access(operands[1].downcast_ty());
                    Self::native_cmp(vcx, bin_op, lhs, rhs).upcast_ty()
                }
                PrustiBuiltin::IsNaN(fl) => {
                    let is_nan = Self::float_domain(deps, fl)?.fp_is_nan;
                    is_nan.call()(operands[0].downcast_ty()).upcast_ty()
                }
                PrustiBuiltin::IsInfinite(fl) => {
                    let is_infinite = Self::float_domain(deps, fl)?.fp_is_infinite;
                    is_infinite.call()(operands[0].downcast_ty()).upcast_ty()
                }
                PrustiBuiltin::FlAbs(fl) => {
                    let abs = Self::float_domain(deps, fl)?.fp_abs;
                    abs.call()(operands[0].downcast_ty())
                }
                PrustiBuiltin::FlToReal => {
                    let fp_to_real = e_input(deps, 0)?.expect_float().fp_to_real;
                    fp_to_real.call()(operands[0].downcast_ty()).upcast_ty()
                }
                PrustiBuiltin::RealMul => Self::real_op(vcx, vir::BinOpKind::PermMul, operands),
                PrustiBuiltin::RealSub => Self::real_op(vcx, vir::BinOpKind::PermSub, operands),
                PrustiBuiltin::RealAdd => Self::real_op(vcx, vir::BinOpKind::PermAdd, operands),
                PrustiBuiltin::RealDiv => Self::real_op(vcx, vir::BinOpKind::PermPermDiv, operands),
                PrustiBuiltin::RealEq
                | PrustiBuiltin::RealNe
                | PrustiBuiltin::RealLt
                | PrustiBuiltin::RealLe
                | PrustiBuiltin::RealGt
                | PrustiBuiltin::RealGe => {
                    let (v1, v2) = Self::deref_operands::<vir::Perm>(deps, sig, args, operands)?;
                    let bin_op = match builtin {
                        PrustiBuiltin::RealEq => vir::BinOpKind::CmpEq,
                        PrustiBuiltin::RealNe => vir::BinOpKind::CmpNe,
                        PrustiBuiltin::RealLt => vir::BinOpKind::CmpLt,
                        PrustiBuiltin::RealLe => vir::BinOpKind::CmpLe,
                        PrustiBuiltin::RealGt => vir::BinOpKind::CmpGt,
                        PrustiBuiltin::RealGe => vir::BinOpKind::CmpGe,
                        _ => unreachable!(),
                    };
                    Self::native_cmp(vcx, bin_op, v1, v2).upcast_ty()
                }
                PrustiBuiltin::RealCmp => {
                    let (v1, v2) = Self::deref_operands::<vir::Perm>(deps, sig, args, operands)?;
                    Self::encode_cmp(vcx, deps, sig.output(), args, v1, v2)?
                }
                PrustiBuiltin::RealPartialCmp => {
                    let (v1, v2) = Self::deref_operands::<vir::Perm>(deps, sig, args, operands)?;
                    Self::encode_partial_cmp(vcx, deps, sig.output(), args, v1, v2)?
                }
                PrustiBuiltin::RealNeg => vcx
                    .mk_unary_op_expr(
                        vir::UnOpKind::PermNeg,
                        operands[0].downcast_ty::<vir::Perm>().upcast_ty(),
                    )
                    .downcast_ty::<vir::Perm>()
                    .upcast_ty(),
                PrustiBuiltin::IntFrom => {
                    let prim = e_input(deps, 0)?.expect_primitive();
                    let val = prim.snap_to_prim(operands[0].downcast_ty());
                    val.downcast_ty::<vir::Int>().upcast_ty()
                }
                PrustiBuiltin::IntMul => Self::int_op(vcx, vir::BinOpKind::Mul, operands),
                PrustiBuiltin::IntSub => Self::int_op(vcx, vir::BinOpKind::Sub, operands),
                PrustiBuiltin::IntAdd => Self::int_op(vcx, vir::BinOpKind::Add, operands),
                PrustiBuiltin::IntDiv => Self::int_op(vcx, vir::BinOpKind::Div, operands),
                PrustiBuiltin::IntRem => Self::int_op(vcx, vir::BinOpKind::Mod, operands),
                PrustiBuiltin::IntEq
                | PrustiBuiltin::IntNe
                | PrustiBuiltin::IntLt
                | PrustiBuiltin::IntLe
                | PrustiBuiltin::IntGt
                | PrustiBuiltin::IntGe => {
                    let (v1, v2) = Self::deref_operands::<vir::Int>(deps, sig, args, operands)?;
                    let bin_op = match builtin {
                        PrustiBuiltin::IntEq => vir::BinOpKind::CmpEq,
                        PrustiBuiltin::IntNe => vir::BinOpKind::CmpNe,
                        PrustiBuiltin::IntLt => vir::BinOpKind::CmpLt,
                        PrustiBuiltin::IntLe => vir::BinOpKind::CmpLe,
                        PrustiBuiltin::IntGt => vir::BinOpKind::CmpGt,
                        PrustiBuiltin::IntGe => vir::BinOpKind::CmpGe,
                        _ => unreachable!(),
                    };
                    Self::native_cmp(vcx, bin_op, v1, v2).upcast_ty()
                }
                PrustiBuiltin::IntCmp => {
                    let (v1, v2) = Self::deref_operands::<vir::Int>(deps, sig, args, operands)?;
                    Self::encode_cmp(vcx, deps, sig.output(), args, v1, v2)?
                }
                PrustiBuiltin::IntPartialCmp => {
                    let (v1, v2) = Self::deref_operands::<vir::Int>(deps, sig, args, operands)?;
                    Self::encode_partial_cmp(vcx, deps, sig.output(), args, v1, v2)?
                }
                PrustiBuiltin::IntNeg => vcx
                    .mk_unary_op_expr(
                        vir::UnOpKind::Neg,
                        operands[0].downcast_ty::<vir::Int>().upcast_ty(),
                    )
                    .downcast_ty::<vir::Int>()
                    .upcast_ty(),
            };
            Ok(((), PrustiBuiltinExpr(res.upcast_ty())))
        })
    }
}

impl PrustiBuiltinEnc {
    /// The float snapshot domain for a `FloatTy`.
    fn float_domain<'vir>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        fl: ty::FloatTy,
    ) -> EncResult<'vir, FloatDomain<'vir>> {
        vir::with_vcx(|vcx| {
            let ty = match fl {
                ty::FloatTy::F16 => vcx.tcx().types.f16,
                ty::FloatTy::F32 => vcx.tcx().types.f32,
                ty::FloatTy::F64 => vcx.tcx().types.f64,
                ty::FloatTy::F128 => vcx.tcx().types.f128,
            };
            let ty = deps.require_dep::<TyUsePureEnc>(RustTyDecomposition::from_prim_ty(ty))?;
            Ok(*ty.expect_float())
        })
    }

    /// Arithmetic on two `Real` (native `Perm`) operands.
    fn real_op<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        bin_op: vir::BinOpKind,
        operands: &[ExprRet<'vir, vir::Snap>],
    ) -> ExprRet<'vir, vir::CSnap> {
        vcx.mk_bin_op_expr(
            bin_op,
            operands[0].downcast_ty::<vir::Perm>(),
            operands[1].downcast_ty::<vir::Perm>(),
        )
        .downcast_ty::<vir::Perm>()
        .upcast_ty()
    }

    /// Arithmetic on two `Int` (native `Int`) operands.
    fn int_op<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        bin_op: vir::BinOpKind,
        operands: &[ExprRet<'vir, vir::Snap>],
    ) -> ExprRet<'vir, vir::CSnap> {
        vcx.mk_bin_op_expr(
            bin_op,
            operands[0].downcast_ty::<vir::Int>(),
            operands[1].downcast_ty::<vir::Int>(),
        )
        .downcast_ty::<vir::Int>()
        .upcast_ty()
    }

    /// Dereferences the two `&self`/`&other` operand holes to their native
    /// value `T` (the `PartialOrd`/`PartialEq` methods take `&self`).
    fn deref_operands<'vir, T: vir::CompType>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        sig: ty::FnSig<'vir>,
        args: GArgs<'vir>,
        operands: &[ExprRet<'vir, vir::Snap>],
    ) -> EncResult<'vir, (ExprRet<'vir, T>, ExprRet<'vir, T>)>
    where
        vir::Snap: vir::TransmuteFrom<T>,
    {
        let deref = |deps: &mut TaskEncoderDependencies<'vir, Self>, i: usize| {
            let ty = RustTyDecomposition::from_ty(sig.inputs()[i], args.context());
            let e_ty = deps.require_dep::<TyUsePureEnc>(ty)?;
            Ok(e_ty
                .expect_immref()
                .value_access(operands[i].downcast_ty::<vir::CSnap>())
                .downcast_ty::<T>())
        };
        Ok((deref(deps, 0)?, deref(deps, 1)?))
    }

    /// Comparison of two natively-represented builtin values (`Int`/`Real`).
    fn native_cmp<'vir, T: vir::CompType>(
        vcx: &'vir vir::VirCtxt<'vir>,
        bin_op: vir::BinOpKind,
        val1: ExprRet<'vir, T>,
        val2: ExprRet<'vir, T>,
    ) -> ExprRet<'vir, vir::Bool> {
        vcx.mk_bin_op_expr_inner(bin_op, val1.as_dyn(), val2.as_dyn())
            .downcast_ty()
    }

    /// Encodes `Ord::cmp` on a native builtin: builds the `Ordering` snapshot
    /// `if a < b { Less } else if a == b { Equal } else { Greater }`.
    fn encode_cmp<'vir, T: vir::CompType>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        ordering_ty: ty::Ty<'vir>,
        args: GArgs<'vir>,
        val1: ExprRet<'vir, T>,
        val2: ExprRet<'vir, T>,
    ) -> EncResult<'vir, ExprRet<'vir, vir::CSnap>> {
        let cmp = |bin_op| Self::native_cmp(vcx, bin_op, val1, val2);

        // `core::cmp::Ordering`'s variants in definition order: Less, Equal, Greater.
        let ord = deps.require_dep::<TyUsePureEnc>(RustTyDecomposition::from_ty(
            ordering_ty,
            args.context(),
        ))?;
        let variant = |idx: usize| {
            ord.expect_variant_opt(Some(abi::VariantIdx::from_usize(idx)))
                .field_snaps_to_snap(Vec::new())
        };
        let (less, equal, greater) = (variant(0), variant(1), variant(2));

        let else_ = vcx.mk_ternary_expr(cmp(vir::BinOpKind::CmpEq), equal, greater);
        Ok(vcx.mk_ternary_expr(cmp(vir::BinOpKind::CmpLt), less, else_))
    }

    /// Encodes `PartialOrd::partial_cmp` on a native builtin: `Some(a.cmp(b))`.
    fn encode_partial_cmp<'vir, T: vir::CompType>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        option_ty: ty::Ty<'vir>,
        args: GArgs<'vir>,
        val1: ExprRet<'vir, T>,
        val2: ExprRet<'vir, T>,
    ) -> EncResult<'vir, ExprRet<'vir, vir::CSnap>> {
        let ty::TyKind::Adt(_, option_args) = option_ty.kind() else {
            unreachable!("partial_cmp does not return an `Option`: {option_ty:?}");
        };
        let ordering_ty = option_args.type_at(0);
        let ordering = Self::encode_cmp(vcx, deps, ordering_ty, args, val1, val2)?;

        // Wrap in `Option::Some` (variant 1, one field).
        let option = deps
            .require_dep::<TyUsePureEnc>(RustTyDecomposition::from_ty(option_ty, args.context()))?;
        Ok(option
            .expect_variant_opt(Some(abi::VariantIdx::from_usize(1)))
            .field_snaps_to_snap(vec![ordering.upcast_ty()]))
    }
}
