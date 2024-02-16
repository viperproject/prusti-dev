use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};
use rustc_middle::mir::interpret::{ConstValue, Scalar, GlobalAlloc};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use vir::{CallableIdent, Arity};

pub struct ConstEnc;

#[derive(Clone, Debug)]
pub struct ConstEncOutputRef<'vir> {
    pub base_name: String,
    pub snap_inst: vir::Type<'vir>,
}
impl<'vir> task_encoder::OutputRefAny for ConstEncOutputRef<'vir> {}

use crate::encoders::{MirPureEnc, mir_pure::PureKind, MirPureEncTask, SnapshotEnc};

impl TaskEncoder for ConstEnc {
    task_encoder::encoder_cache!(ConstEnc);

    type TaskDescription<'tcx> = (
        mir::ConstantKind<'tcx>,
        usize, // current encoding depth
        DefId, // DefId of the current function
    );
    type OutputFullLocal<'vir> = vir::Expr<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir>>,
    )> {
        deps.emit_output_ref::<Self>(*task_key, ());
        let (const_, encoding_depth, def_id) = *task_key;
        let res = match const_ {
            mir::ConstantKind::Val(val, ty) => {
                let kind = deps.require_local::<SnapshotEnc>(ty).unwrap().specifics;
                match val {
                    ConstValue::Scalar(Scalar::Int(int)) => {
                        let prim = kind.expect_primitive();
                        let val = int.to_bits(int.size()).unwrap();
                        let val = prim.expr_from_bits(ty, val);
                        vir::with_vcx(|vcx| prim.prim_to_snap.apply(vcx, [val]))
                    }
                    ConstValue::Scalar(Scalar::Ptr(ptr, _)) => vir::with_vcx(|vcx| {
                        match vcx.tcx.global_alloc(ptr.provenance) {
                            GlobalAlloc::Function(_) => todo!(),
                            GlobalAlloc::VTable(_, _) => todo!(),
                            GlobalAlloc::Static(_) => todo!(),
                            GlobalAlloc::Memory(_mem) => {
                                // If the `unwrap` ever panics we need a different way to get the inner type
                                // let inner_ty = ty.builtin_deref(true).map(|t| t.ty).unwrap_or(ty);
                                let _inner_ty = ty.builtin_deref(true).unwrap().ty;
                                todo!()
                            }
                        }
                    }),
                    ConstValue::ZeroSized => {
                        let s = kind.expect_structlike();
                        assert_eq!(s.field_snaps_to_snap.arity().args().len(), 0);
                        vir::with_vcx(|vcx| s.field_snaps_to_snap.apply(vcx, &[]))
                    }
                    ConstValue::Slice { .. } => todo!(),
                    ConstValue::Indirect { .. } => todo!(),
                }
            }
            mir::ConstantKind::Unevaluated(uneval, _) => vir::with_vcx(|vcx| {
                let task = MirPureEncTask {
                    encoding_depth: encoding_depth + 1,
                    parent_def_id: uneval.def,
                    param_env: vcx.tcx.param_env(uneval.def),
                    substs: ty::List::identity_for_item(vcx.tcx, uneval.def),
                    kind: PureKind::Constant(uneval.promoted.unwrap()), 
                    caller_def_id: def_id
                };
                let expr = deps.require_local::<MirPureEnc>(task).unwrap().expr;
                use vir::Reify;
                expr.reify(vcx, (uneval.def, &[]))
            }),
            mir::ConstantKind::Ty(_) => todo!(),
        };
        Ok((res, ()))
    }
}
