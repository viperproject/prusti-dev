use prusti_rustc_interface::{
    middle::ty,
    middle::mir,
};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use crate::vir;

pub struct MirBuiltinEncoder;

#[derive(Clone, Debug)]
pub enum MirBuiltinEncoderError {
    Unsupported,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum MirBuiltinEncoderTask<'tcx> {
    UnOp(mir::UnOp, ty::Ty<'tcx>),
}

#[derive(Clone, Debug)]
pub struct MirBuiltinEncoderOutputRef<'vir> {
    pub name: &'vir str,
}
impl<'vir, 'tcx> task_encoder::OutputRefAny<'vir, 'tcx> for MirBuiltinEncoderOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirBuiltinEncoderOutput<'vir> {
    pub function: vir::Function<'vir>,
}

use std::cell::RefCell;
thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirBuiltinEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for MirBuiltinEncoder {
    type TaskDescription<'vir, 'tcx> = MirBuiltinEncoderTask<'tcx> where 'tcx: 'vir;

    type OutputRef<'vir, 'tcx> = MirBuiltinEncoderOutputRef<'vir> where 'tcx: 'vir;
    type OutputFullLocal<'vir, 'tcx> = MirBuiltinEncoderOutput<'vir> where 'tcx: 'vir;

    type EncodingError = MirBuiltinEncoderError;

    fn with_cache<'vir, 'tcx, F, R>(f: F) -> R
        where 'tcx: 'vir, F: FnOnce(&'vir task_encoder::CacheRef<'vir, 'tcx, MirBuiltinEncoder>) -> R,
    {
        CACHE.with(|cache| {
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            let cache = unsafe { std::mem::transmute(cache) };
            f(cache)
        })
    }

    fn task_to_key<'vir, 'tcx>(task: &Self::TaskDescription<'vir, 'tcx>) -> Self::TaskKey<'vir, 'tcx>
        where 'tcx: 'vir
    {
        task.clone()
    }

    fn do_encode_full<'vir, 'tcx>(
        task_key: &Self::TaskKey<'vir, 'tcx>,
        deps: &mut TaskEncoderDependencies<'vir, 'tcx>,
    ) -> Result<(
        Self::OutputFullLocal<'vir, 'tcx>,
        Self::OutputFullDependency<'vir, 'tcx>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir, 'tcx>>,
    )> {
        crate::with_vcx(|vcx| {
            match task_key {
                MirBuiltinEncoderTask::UnOp(mir::UnOp::Not, ty) => {
                    assert_eq!(*ty.kind(), ty::TyKind::Bool);

                    let name = "mir_unop_not";
                    deps.emit_output_ref::<Self>(task_key.clone(), MirBuiltinEncoderOutputRef {
                        name,
                    });
                    /* function mir_unop_not(arg: s_Bool): s_Bool {
                        s_Bool$cons(!s_Bool$val(val))
                    } */

                    let ty_s = deps.require_ref::<crate::encoders::TypeEncoder>(
                        *ty,
                    ).unwrap().snapshot;

                    Ok((MirBuiltinEncoderOutput {
                        function: vcx.alloc(vir::FunctionData {
                            name,
                            args: vir::bvec![in &vcx.arena; vcx.alloc(vir::LocalDeclData {
                                name: "arg",
                                ty: ty_s,
                                expr: None,
                            })],
                            ret: ty_s,
                            pres: vir::bvec![in &vcx.arena],
                            posts: vir::bvec![in &vcx.arena],
                            expr: Some(vcx.alloc(vir::ExprData::FuncApp(vcx.alloc(vir::FuncAppData {
                                target: "s_Bool_cons",
                                args: vir::bvec![in &vcx.arena; vcx.alloc(vir::ExprData::UnOp(vcx.alloc(vir::UnOpData {
                                    kind: vir::UnOpKind::Not,
                                    expr: vcx.alloc(vir::ExprData::FuncApp(vcx.alloc(vir::FuncAppData {
                                        target: "s_Bool_val",
                                        args: vir::bvec![in &vcx.arena; vcx.mk_local_ex("arg")],
                                    }))),
                                })))]
                            })))),
                        }),
                    }, ()))
                }

                MirBuiltinEncoderTask::UnOp(mir::UnOp::Neg, ty) => {
                    let name = match ty.kind() {
                        ty::TyKind::Int(ty::IntTy::Isize) => "mir_unop_neg_isize",
                        ty::TyKind::Int(ty::IntTy::I8) => "mir_unop_neg_i8",
                        ty::TyKind::Int(ty::IntTy::I16) => "mir_unop_neg_i16",
                        ty::TyKind::Int(ty::IntTy::I32) => "mir_unop_neg_i32",
                        ty::TyKind::Int(ty::IntTy::I64) => "mir_unop_neg_i64",
                        ty::TyKind::Int(ty::IntTy::I128) => "mir_unop_neg_i128",
                        ty::TyKind::Uint(ty::UintTy::Usize) => "mir_unop_neg_usize",
                        ty::TyKind::Uint(ty::UintTy::U8) => "mir_unop_neg_u8",
                        ty::TyKind::Uint(ty::UintTy::U16) => "mir_unop_neg_u16",
                        ty::TyKind::Uint(ty::UintTy::U32) => "mir_unop_neg_u32",
                        ty::TyKind::Uint(ty::UintTy::U64) => "mir_unop_neg_u64",
                        ty::TyKind::Uint(ty::UintTy::U128) => "mir_unop_neg_u128",
                        _ => unreachable!("MIR negation on non-integer type"),
                    };
                    deps.emit_output_ref::<Self>(task_key.clone(), MirBuiltinEncoderOutputRef {
                        name,
                    });
                    /* function mir_unop_neg(arg: s_I32): s_I32 {
                        cons(-val(arg))
                    } */

                    let ty_out = deps.require_ref::<crate::encoders::TypeEncoder>(
                        *ty,
                    ).unwrap();
                    let ty_s = ty_out.snapshot;

                    Ok((MirBuiltinEncoderOutput {
                        function: vcx.alloc(vir::FunctionData {
                            name,
                            args: vir::bvec![in &vcx.arena; vcx.alloc(vir::LocalDeclData {
                                name: "arg",
                                ty: ty_s,
                                expr: None,
                            })],
                            ret: ty_s,
                            pres: vir::bvec![in &vcx.arena],
                            posts: vir::bvec![in &vcx.arena],
                            expr: Some(vcx.alloc(vir::ExprData::FuncApp(vcx.alloc(vir::FuncAppData {
                                target: crate::vir_format!(vcx, "{}_cons", ty_out.snapshot_name),
                                args: vir::bvec![in &vcx.arena; vcx.alloc(vir::ExprData::UnOp(vcx.alloc(vir::UnOpData {
                                    kind: vir::UnOpKind::Neg,
                                    expr: vcx.alloc(vir::ExprData::FuncApp(vcx.alloc(vir::FuncAppData {
                                        target: crate::vir_format!(vcx, "{}_val", ty_out.snapshot_name),
                                        args: vir::bvec![in &vcx.arena; vcx.mk_local_ex("arg")],
                                    }))),
                                })))]
                            })))),
                        }),
                    }, ()))
                }
            }

        })
    }
}
