use crate::encoders::{
    TyUseImpureEnc,
    ty::{
        RustTyDatas,
        data::{ArrayData, TyData},
        impure::{ImpureTyDatas, PredicateBuilder, TyImpureArrayData, TyImpureEnc},
        kinds::opaque::set_opaque,
        pure::{DomainBuilder, PureTyDatas, TyPureArrayData, TyPureEnc},
    },
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, HasType};

pub(crate) fn ty_pure<'vir>(
    data: &ArrayData<'vir, RustTyDatas>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<ArrayData<'vir, PureTyDatas>, EncodeFullError<'vir, TyPureEnc>> {
    let index_access = builder.function(
        "index",
        (builder.self_type(), vir::TYPE_INT),
        vir::TYPE_PSNAP,
    );
    let args = (vir::TYPE_REF, vir::TYPE_INT, builder.params.ty_args());
    let ref_to_index_ref = builder.function("index_ref", args, vir::TYPE_REF);
    Ok(ArrayData::new(
        TyPureArrayData {
            index_access,
            ref_to_index_ref,
        },
        data.slice,
    ))
}

pub(crate) fn ty_impure<'vir>(
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &ArrayData<'vir, (RustTyDatas, PureTyDatas)>,
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<ArrayData<'vir, ImpureTyDatas>, EncodeFullError<'vir, TyImpureEnc>> {
    set_opaque(builder);
    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);
    let index_decl = builder.vcx.mk_local_decl("index", vir::TYPE_INT);
    let index = builder.vcx.mk_local_ex(index_decl);
    let index_predicate = builder
        .inner
        .predicate::<(vir::Ref, vir::Int, vir::ManyTyVal, vir::ManyCSnap)>(
            "index",
            (
                ref_self_decl.ty(),
                index_decl.ty(),
                builder.params.ty_args(),
                builder.params.const_args(),
            ),
            (
                ref_self_decl,
                index_decl,
                builder.params.ty_decls(),
                builder.params.const_decls(),
            ),
            None,
        );

    let ref_to_index_ref = data.1.ref_to_index_ref;
    let index_ref = ref_to_index_ref(ref_self, index, builder.params.ty_exprs());

    let index_frame = builder.inner.function(
        "index_frame",
        (
            ref_self_decl.ty(),
            index_decl.ty(),
            builder.params.ty_args(),
            builder.params.const_args(),
        ),
        (task_key.1.domain)().downcast_ty(),
        (
            ref_self_decl,
            index_decl,
            builder.params.ty_decls(),
            builder.params.const_decls(),
        ),
        &[
            vir::expr! { [index_predicate](ref_self, index, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]]) },
        ],
        &[],
        None,
    );

    let element_ty = data.0.decompose(task_key.0.params);
    let element_ty_out = deps.require_dep::<TyUseImpureEnc>(element_ty)?;
    let element_pred = element_ty_out.ref_to_pred(builder.vcx, index_ref, None);

    let array_snap = vir::expr! { [builder.ref_to_snap](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]]) }.downcast_ty();
    let array_index = data.1.index_access.call()(array_snap, index);
    let method_fold = builder
        .inner
        .method::<(vir::Int, vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>(
            "fold_index",
            (
                vir::TYPE_INT,
                ref_self_decl.ty(),
                builder.params.ty_args(),
                builder.params.const_args(),
            ),
            &[],
            (
                index_decl,
                ref_self_decl,
                builder.params.ty_decls(),
                builder.params.const_decls(),
            ),
            &[
                element_pred,
                vir::expr! { [index_predicate](ref_self, index, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]]) },
            ],
            &[
                vir::expr! { [builder.ref_to_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]]) },
                vir::expr! {
                    forall idx: Int :: {[data.1.index_access](array_snap, idx)}
                        ([data.1.index_access](array_snap, idx)) == (
                            ((idx) == (index))
                            ? ([builder.vcx.mk_old_expr(element_ty_out.ref_to_snap(index_ref).downcast_ty())])
                            : (old([data.1.index_access](([index_frame](ref_self, index, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])), idx)))
                        )
                },
            ],
        );
    let method_unfold = builder
        .inner
        .method::<(vir::Int, vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>(
            "unfold_index",
            (
                vir::TYPE_INT,
                ref_self_decl.ty(),
                builder.params.ty_args(),
                builder.params.const_args(),
            ),
            &[],
            (
                index_decl,
                ref_self_decl,
                builder.params.ty_decls(),
                builder.params.const_decls(),
            ),
            &[
                vir::expr! { [builder.ref_to_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]]) },
            ],
            &[
                element_pred,
                vir::expr! { [index_predicate](ref_self, index, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]]) },
                vir::expr! {
                    ([element_ty_out.ref_to_snap(index_ref)])
                    == ([builder.vcx.mk_old_expr(array_index).upcast_ty()])
                },
                vir::expr! {
                    ([index_frame](ref_self, index, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]]))
                    == (old(array_snap))
                }
            ],
        );

    Ok(ArrayData::new(
        TyImpureArrayData {
            ref_to_index_ref,
            index_frame,
            index_predicate,
            method_fold,
            method_unfold,
        },
        data.slice,
    ))
}
