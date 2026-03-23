use prusti_rustc_interface::{
    abi::HasDataLayout,
    const_eval::interpret::AllocRange,
    middle::{
        mir::{
            self, ConstValue,
            interpret::{GlobalAlloc, Scalar},
        },
        ty,
    },
    span::{Span, def_id::DefId},
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

use crate::encoders::{
    MirPureEnc, MirPureEncTask, PureKind,
    addr::RefDataEnc,
    ty::{
        RustTyDecomposition,
        generics::{GParams, GenericParamsEnc},
        use_pure::TyUsePureEnc,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ConstEncTask<'vir> {
    Ty {
        const_: ty::Const<'vir>,
        ty: ty::Ty<'vir>,
        context: GParams<'vir>,
    },
    Mir {
        const_: mir::Const<'vir>,
        encoding_depth: usize, // current encoding depth
        def_id: DefId,         // DefId of the current function
        span: Span,
    },
}

/// Encodes constants into snapshot expressions. The evaluation of a constant
/// is assumed to be side-effect free, as enforced by the compiler. This encoder
/// handles two different kinds of constants: ones coming from the MIR and ones
/// coming from the type system.
///
/// See "Representing constants" in the rustc dev guide for an overview:
/// https://rustc-dev-guide.rust-lang.org/mir/index.html#representing-constants
pub struct ConstEnc;

impl ConstEnc {
    fn encode_ty_const<'vir>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        const_: ty::Const<'vir>,
        ty: ty::Ty<'vir>,
        context: GParams<'vir>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, Self>> {
        match const_.kind() {
            ty::ConstKind::Param(param) => {
                let params = deps.require_dep::<GenericParamsEnc>(context)?;
                Ok(params.const_expr(param))
            }
            ty::ConstKind::Value(val) => {
                let val = vir::with_vcx(|vcx| vcx.tcx().valtree_to_const_val(val));
                Self::encode_const_val(deps, val, ty, context, None)
            }
            k => todo!("const kind {k:?}"),
        }
    }

    fn encode_scalar<'vir>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        val: Scalar,
        ty: ty::Ty<'vir>,
        context: GParams<'vir>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, Self>> {
        let ty_task = RustTyDecomposition::from_ty(ty, context);
        let kind = deps.require_dep::<TyUsePureEnc>(ty_task)?;
        vir::with_vcx(|vcx| {
            Ok(match val {
                Scalar::Int(int) => {
                    // TODO: Aggregates like structs will also show up as scalars
                    // This means that the scalar doesn't contain all the data
                    // and that it doesn't match the type of ty, which will lead
                    // to a panic. We would have to encode these by looking at
                    // the memory layout and iterating over the individual fields
                    let prim = kind.expect_primitive();
                    let val = int.to_bits(int.size());
                    let val = prim.expr_from_bits(ty, val);
                    (prim.prim_to_snap)(val)
                }
                Scalar::Ptr(ptr, _) => match vcx.tcx().global_alloc(ptr.provenance.alloc_id()) {
                    GlobalAlloc::Function { .. } => todo!(),
                    GlobalAlloc::VTable(_, _) => todo!(),
                    GlobalAlloc::Static(_) => todo!(),
                    GlobalAlloc::Memory(mem) => {
                        let (prov, offset) = ptr.prov_and_relative_offset();

                        let inner_ty = ty.builtin_deref(true).unwrap();

                        let size = if inner_ty.is_any_ptr() {
                            vcx.tcx().data_layout().pointer_size()
                        } else {
                            mem.0.size()
                        };

                        // TODO: the unwrap can fail, e.g., for zero-sized types or empty strs/slices
                        let bytes = mem
                            .0
                            .read_scalar(
                                &vcx.tcx(),
                                AllocRange {
                                    start: offset,
                                    size,
                                },
                                inner_ty.is_any_ptr(),
                            )
                            .unwrap();
                        let alloc_id = prov.alloc_id().0;
                        let rel_addr = ((alloc_id.get() as u128) << 64) | offset.bytes() as u128;

                        let addr_to_ref = deps.require_dep::<RefDataEnc>(())?.addr_to_ref;
                        kind.expect_immref().prim_to_snap(
                            addr_to_ref(
                                vcx.mk_const_expr(vir::ConstData::Int(rel_addr))
                                    .downcast_ty(),
                            ),
                            Self::encode_scalar(deps, bytes, inner_ty, context)?.upcast_ty(),
                        )
                    }
                    GlobalAlloc::TypeId { .. } => todo!(),
                },
            })
        })
    }

    fn encode_const_val<'vir>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        val: ConstValue,
        ty: ty::Ty<'vir>,
        context: GParams<'vir>,
        _span: Option<Span>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, Self>> {
        let ty_task = RustTyDecomposition::from_ty(ty, context);
        let kind = deps.require_dep::<TyUsePureEnc>(ty_task)?;
        Ok(match val {
            ConstValue::Scalar(scalar) => Self::encode_scalar(deps, scalar, ty, context)?,
            ConstValue::ZeroSized => {
                let s = kind.expect_structlike();
                s.field_snaps_to_snap(Vec::new())
            }
            // Encode `&str` constants to an opaque domain. If we ever want to perform string reasoning
            // we will need to revisit this encoding, but for the moment this allows assertions to avoid
            // crashing Prusti.
            ConstValue::Slice { .. } if ty.peel_refs().is_str() => {
                let ref_ty = kind.expect_immref();
                let str_ty = ty.peel_refs();
                let str_ty_task = RustTyDecomposition::from_ty(str_ty, context);
                let str_snap = deps.require_dep::<TyUsePureEnc>(str_ty_task)?;
                let str_snap = str_snap.expect_opaque();
                // first, we create a string snapshot
                let snap = (str_snap.arbitrary)().upcast_ty();
                // wrap it in a ref
                vir::with_vcx(|vcx| ref_ty.prim_to_snap(vcx.mk_null(), snap))
            }
            ConstValue::Slice { .. } => todo!("ConstValue::Slice: {ty:?}"),
            ConstValue::Indirect { .. } => todo!("ConstValue::Indirect"),
        })
    }
}

impl TaskEncoder for ConstEnc {
    task_encoder::encoder_cache!(ConstEnc);
    const ENCODER_NAME: &'static str = "const encoder";

    type TaskDescription<'vir> = ConstEncTask<'vir>;
    type OutputFullDependency<'vir> = vir::ExprCSnap<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let res = match *task_key {
            ConstEncTask::Ty {
                const_,
                ty,
                context,
            } => Self::encode_ty_const(deps, const_, ty, context)?,
            ConstEncTask::Mir {
                const_,
                encoding_depth,
                def_id,
                span,
            } => match const_ {
                mir::Const::Val(val, ty) => {
                    Self::encode_const_val(deps, val, ty, def_id.into(), Some(span))?
                }
                mir::Const::Unevaluated(uneval, ty) => vir::with_vcx(|vcx| {
                    let resolved = {
                        let typing_env = ty::TypingEnv::post_analysis(vcx.tcx(), def_id);
                        vcx.tcx()
                            .const_eval_resolve(typing_env, uneval, vcx.tcx().def_span(def_id))
                    };
                    if let Ok(val) = resolved {
                        Self::encode_const_val(deps, val, ty, def_id.into(), Some(span))
                    } else if let Some(promoted) = uneval.promoted {
                        let task = MirPureEncTask {
                            encoding_depth: encoding_depth + 1,
                            parent_def_id: uneval.def,
                            param_env: vcx.tcx().param_env(uneval.def),
                            substs: ty::List::identity_for_item(vcx.tcx(), uneval.def),
                            kind: PureKind::Constant(promoted),
                            caller_def_id: Some(def_id),
                        };
                        let expr = deps.require_dep::<MirPureEnc>(task)?.expr;
                        use vir::Reify;
                        Ok(expr.reify(vcx, (uneval.def, &[])).downcast_ty())
                    } else {
                        todo!("const too generic")
                    }
                })?,
                mir::Const::Ty(ty, const_) => {
                    Self::encode_ty_const(deps, const_, ty, def_id.into())?
                }
            },
        };
        Ok(((), res))
    }
}
