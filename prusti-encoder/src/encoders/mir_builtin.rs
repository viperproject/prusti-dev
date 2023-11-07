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

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum MirBuiltinEncoderTask<'tcx> {
    // TODO: which type? input or output? -> best to store both?
    UnOp(mir::UnOp, ty::Ty<'tcx>),
    BinOp(mir::BinOp, ty::Ty<'tcx>),
    CheckedBinOp(mir::BinOp, ty::Ty<'tcx>),
}

#[derive(Clone, Debug)]
pub struct MirBuiltinEncoderOutputRef<'vir> {
    pub function: FunctionIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny<'vir> for MirBuiltinEncoderOutputRef<'vir> {}

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

    fn with_cache<'vir, F, R>(f: F) -> R
        where F: FnOnce(&'vir task_encoder::CacheRef<'vir, MirBuiltinEncoder>) -> R,
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

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir>>,
    )> {
        // TODO: this function is also useful for the type encoder, extract?
        fn int_name<'tcx>(ty: ty::Ty<'tcx>) -> &'static str {
            match ty.kind() {
                ty::TyKind::Int(kind) => kind.name_str(),
                ty::TyKind::Uint(kind) => kind.name_str(),
                _ => unreachable!("non-integer type"),
            }
        }

        vir::with_vcx(|vcx| {
            match task_key {
                MirBuiltinEncoderTask::UnOp(mir::UnOp::Not, ty) => {
                    assert_eq!(*ty.kind(), ty::TyKind::Bool);

                    let ty_ref = deps.require_ref::<crate::encoders::TypeEncoder>(
                        *ty,
                    ).unwrap();

                    let name = "mir_unop_not";
                    let ty_s = ty_ref.snapshot;
                    let arity = UnknownArity::new(vcx.alloc_slice(&[ty_s]));
                    let function = FunctionIdent::new(name, arity);
                    deps.emit_output_ref::<Self>(task_key.clone(), MirBuiltinEncoderOutputRef {
                        function,
                    });
                    /* function mir_unop_not(arg: s_Bool): s_Bool {
                        s_Bool$cons(!s_Bool$val(val))
                    } */

                    Ok((MirBuiltinEncoderOutput {
                        function: vcx.alloc(vir::FunctionData {
                            name,
                            args: vcx.alloc_slice(&[vcx.mk_local_decl("arg", ty_s)]),
                            ret: ty_s,
                            pres: &[],
                            posts: &[],
                            expr: Some(
                                ty_ref.expect_prim().prim_to_snap.apply(vcx,
                                    [vcx.alloc(vir::ExprData::UnOp(vcx.alloc(vir::UnOpData {
                                        kind: vir::UnOpKind::Not,
                                        expr:  ty_ref.expect_prim().snap_to_prim.apply(vcx, [vcx.mk_local_ex("arg")])
                                    })))]
                                )
                            ),
                        }),
                    }, ()))
                }

                MirBuiltinEncoderTask::UnOp(mir::UnOp::Neg, ty) => {
                    let ty_out = deps.require_ref::<crate::encoders::TypeEncoder>(
                        *ty,
                    ).unwrap();

                    let name = vir::vir_format!(vcx, "mir_unop_neg_{}", int_name(*ty));
                    let arity = UnknownArity::new(vcx.alloc_slice(&[ty_out.snapshot]));
                    let function = FunctionIdent::new(name, arity);
                    deps.emit_output_ref::<Self>(task_key.clone(), MirBuiltinEncoderOutputRef {
                        function,
                    });
                    /* function mir_unop_neg(arg: s_I32): s_I32 {
                        cons(-val(arg))
                    } */

                    Ok((
                        MirBuiltinEncoderOutput {
                            function: vcx.alloc(vir::FunctionData {
                                name,
                                args: vcx.alloc_slice(&[vcx.mk_local_decl("arg", ty_out.snapshot)]),
                                ret: ty_out.snapshot,
                                pres: &[],
                                posts: &[],
                                expr: Some(
                                    ty_out.expect_prim().prim_to_snap.apply(vcx, [vcx.alloc(vir::ExprData::UnOp(
                                        vcx.alloc(vir::UnOpData {
                                            kind: vir::UnOpKind::Neg,
                                            expr: ty_out
                                                .expect_prim()
                                                .snap_to_prim.apply(vcx, [vcx.mk_local_ex("arg")]),
                                        }),
                                    ))]),
                                ),
                            }),
                        },
                        (),
                    ))
                }

                // TODO: should these be two different functions? precondition?
                MirBuiltinEncoderTask::BinOp(mir::BinOp::Add | mir::BinOp::AddUnchecked, ty) => {
                    let ty_out = deps.require_ref::<crate::encoders::TypeEncoder>(
                        *ty,
                    ).unwrap();

                    let name = vir::vir_format!(vcx, "mir_binop_add_{}", int_name(*ty));
                    let arity = UnknownArity::new(vcx.alloc_slice(&[ty_out.snapshot, ty_out.snapshot]));
                    let function = FunctionIdent::new(name, arity);
                    deps.emit_output_ref::<Self>(task_key.clone(), MirBuiltinEncoderOutputRef {
                        function,
                    });

                    Ok((
                        MirBuiltinEncoderOutput {
                            function: vcx.alloc(vir::FunctionData {
                                name,
                                args: vcx.alloc_slice(&[
                                    vcx.mk_local_decl("arg1", ty_out.snapshot),
                                    vcx.mk_local_decl("arg2", ty_out.snapshot),
                                ]),
                                ret: ty_out.snapshot,
                                pres: &[],
                                posts: &[],
                                expr: Some(
                                    ty_out.expect_prim().prim_to_snap.apply(vcx, [vcx.alloc(vir::ExprData::BinOp(
                                        vcx.alloc(vir::BinOpData {
                                            kind: vir::BinOpKind::Add,
                                            lhs: ty_out
                                                .expect_prim()
                                                .snap_to_prim.apply(vcx, [vcx.mk_local_ex("arg1")]),
                                            rhs: ty_out
                                                .expect_prim()
                                                .snap_to_prim.apply(vcx, [vcx.mk_local_ex("arg2")]),
                                        }),
                                    ))]),
                                ),
                            }),
                        },
                        (),
                    ))
                }

                MirBuiltinEncoderTask::CheckedBinOp(mir::BinOp::Add | mir::BinOp::AddUnchecked, ty) => {
                    let ty_in = deps.require_ref::<crate::encoders::TypeEncoder>(
                        *ty,
                    ).unwrap();

                    let name = vir::vir_format!(vcx, "mir_checkedbinop_add_{}", int_name(*ty));
                    let arity = UnknownArity::new(vcx.alloc_slice(&[ty_in.snapshot, ty_in.snapshot]));
                    let function = FunctionIdent::new(name, arity);
                    deps.emit_output_ref::<Self>(task_key.clone(), MirBuiltinEncoderOutputRef {
                        function,
                    });

                    let ty_out = deps.require_ref::<crate::encoders::TypeEncoder>(
                        vcx.tcx.mk_ty_from_kind(ty::TyKind::Tuple(vcx.tcx.mk_type_list(&[
                            *ty,
                            vcx.tcx.types.bool,
                        ]))),
                    ).unwrap();
                    let bool_cons = deps.require_ref::<crate::encoders::TypeEncoder>(
                        vcx.tcx.types.bool,
                    ).unwrap().expect_prim().prim_to_snap;
                    Ok((
                        MirBuiltinEncoderOutput {
                            function: vcx.alloc(vir::FunctionData {
                                name,
                                args: vcx.alloc_slice(&[
                                    vcx.mk_local_decl("arg1", ty_in.snapshot),
                                    vcx.mk_local_decl("arg2", ty_in.snapshot),
                                ]),
                                ret: ty_out.snapshot,
                                pres: &[],
                                posts: &[],
                                expr: Some(
                                    ty_out.expect_structlike().field_snaps_to_snap.apply(vcx, &[
                                        ty_in.expect_prim().prim_to_snap.apply(vcx, [vcx.alloc(vir::ExprData::BinOp(
                                            vcx.alloc(vir::BinOpData {
                                                kind: vir::BinOpKind::Add,
                                                lhs: ty_in
                                                    .expect_prim()
                                                    .snap_to_prim.apply(vcx, [vcx.mk_local_ex("arg1")]),
                                                rhs: ty_in
                                                    .expect_prim()
                                                    .snap_to_prim.apply(vcx, [vcx.mk_local_ex("arg2")]),
                                            }),
                                        ))]),
                                        // TODO: overflow condition!
                                        bool_cons.apply(vcx, [&vir::ExprData::Const(&vir::ConstData::Bool(
                                            false,
                                        ))]),
                                    ]),
                                ),
                            }),
                        },
                        (),
                    ))
                }

                _ => todo!(),
            }

        })
    }
}
