use crate::encoders::ty::{
    RustOpaque,
    impure::{PredicateBuilder, TyImpureEnc, TyImpureOpaque},
    pure::{DomainBuilder, TyPureEnc, TyPureOpaque, TyPureOpaqueData},
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};

pub(crate) fn ty_pure<'vir>(
    _data: &RustOpaque<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<TyPureOpaque<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let arbitrary = builder.function("arbitrary", (), builder.self_type());
    Ok(TyPureOpaqueData { arbitrary })
}

pub(crate) fn ty_impure<'vir>(
    _data: &(&RustOpaque<'vir>, &TyPureOpaque<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureOpaque<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    set_opaque(builder);
    Ok(())
}

pub(super) fn set_opaque<'vir>(builder: &mut PredicateBuilder<'vir>) {
    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);
    let self_pred = builder
        .inner
        .predicate::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>(
            "",
            (
                ref_self_decl.ty,
                builder.params.ty_args(),
                builder.params.const_args(),
            ),
            (
                ref_self_decl,
                builder.params.ty_decls(),
                builder.params.const_decls(),
            ),
            None,
        );
    builder.function_snap = Some(
        builder
            .mk_function::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap), _>(
                "snap",
                (ref_self_decl.ty, builder.params.ty_args(), builder.params.const_args()),
                builder.snap_type(),
                (ref_self_decl, builder.params.ty_decls(), builder.params.const_decls()),
                &[vir::expr! { acc([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) }],
                &[],
                None,
            )
            .1,
    );
}
