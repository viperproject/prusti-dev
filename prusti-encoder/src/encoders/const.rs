use prusti_rustc_interface::{
    middle::{
        mir::{
            self,
            interpret::{GlobalAlloc, Scalar},
            ConstValue,
        },
        ty,
    },
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, CastType};

pub struct ConstEnc;

use crate::encoders::{mir_pure::PureKind, MirPureEnc, MirPureEncTask};

use super::{
    lifted::{casters::CastTypePure, rust_ty_cast::RustTyCastersEnc},
    rust_ty_snapshots::RustTySnapshotsEnc,
};

impl TaskEncoder for ConstEnc {
    task_encoder::encoder_cache!(ConstEnc);

    type TaskDescription<'vir> = (
        mir::Const<'vir>,
        usize, // current encoding depth
        DefId, // DefId of the current function
    );
    type OutputFullLocal<'vir> = vir::ExprCSnap<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let (const_, encoding_depth, def_id) = *task_key;
        let res = match const_ {
            mir::Const::Val(val, ty) => {
                let kind = deps
                    .require_local::<RustTySnapshotsEnc>(ty)?
                    .generic_snapshot
                    .specifics;
                match val {
                    ConstValue::Scalar(Scalar::Int(int)) => {
                        let prim = kind.expect_primitive();
                        let val = int.to_bits(int.size());
                        let val = prim.expr_from_bits(ty, val);
                        (prim.prim_to_snap)(val)
                    }
                    ConstValue::Scalar(Scalar::Ptr(ptr, _)) => vir::with_vcx(|vcx| {
                        match vcx.tcx().global_alloc(ptr.provenance.alloc_id()) {
                            GlobalAlloc::Function { .. } => todo!(),
                            GlobalAlloc::VTable(_, _) => todo!(),
                            GlobalAlloc::Static(_) => todo!(),
                            GlobalAlloc::Memory(_mem) => {
                                // If the `unwrap` ever panics we need a different way to get the inner type
                                // let inner_ty = ty.builtin_deref(true).map(|t| t.ty).unwrap_or(ty);
                                let _inner_ty = ty.builtin_deref(true).unwrap();
                                todo!()
                            }
                            GlobalAlloc::TypeId { .. } => todo!(),
                        }
                    }),
                    ConstValue::ZeroSized => {
                        let s = kind.expect_structlike();
                        assert_eq!(s.field_snaps_to_snap.arity().len(), 0);
                        (s.field_snaps_to_snap)(&[])
                    }
                    // Encode `&str` constants to an opaque domain. If we ever want to perform string reasoning
                    // we will need to revisit this encoding, but for the moment this allows assertions to avoid
                    // crashing Prusti.
                    ConstValue::Slice { .. } if ty.peel_refs().is_str() => {
                        let ref_ty = kind.expect_immref();
                        let str_ty = ty.peel_refs();
                        let str_snap = deps
                            .require_local::<RustTySnapshotsEnc>(str_ty)?
                            .generic_snapshot
                            .specifics
                            .expect_structlike();
                        let cast = deps.require_local::<RustTyCastersEnc<CastTypePure>>(str_ty)?;
                        vir::with_vcx(|vcx| {
                            // first, we create a string snapshot
                            let snap = (str_snap.field_snaps_to_snap)(&[]);
                            // upcast it to a param
                            let snap = cast.cast_to_generic_if_necessary(vcx, snap.upcast_ty());
                            // wrap it in a ref
                            (ref_ty.prim_to_snap)(vcx.mk_null(), snap)
                        })
                    }
                    ConstValue::Slice { .. } => todo!("ConstValue::Slice : {:?}", const_.ty()),
                    ConstValue::Indirect { .. } => todo!("ConstValue::Indirect"),
                }
            }
            mir::Const::Unevaluated(uneval, _) => vir::with_vcx(|vcx| {
                let task = MirPureEncTask {
                    encoding_depth: encoding_depth + 1,
                    parent_def_id: uneval.def,
                    param_env: vcx.tcx().param_env(uneval.def),
                    substs: ty::List::identity_for_item(vcx.tcx(), uneval.def),
                    kind: PureKind::Constant(uneval.promoted.unwrap()),
                    caller_def_id: Some(def_id),
                };
                let expr = deps.require_local::<MirPureEnc>(task)?.expr;
                use vir::Reify;
                Ok(expr.reify(vcx, (uneval.def, &[])).downcast_ty())
            })?,
            mir::Const::Ty(_, _) => todo!("ConstantKind::Ty"),
        };
        Ok((res, ()))
    }
}
