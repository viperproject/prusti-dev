use crate::encoders::ty::{
    impure::{ImpureTyDatas, PredicateBuilder, TyImpureEnc, TyImpureOpaque}, pure::{DomainBuilder, PureTyDatas, TyPureEnc, TyPureOpaque, TyPureOpaqueData}, RustTyDatas, RustOpaque
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
    builder.inner.predicate::<(vir::Ref, vir::ManyTyVal)>(
        "",
        (ref_self_decl.ty, builder.params.ty_args()),
        (ref_self_decl, builder.params.ty_decls()),
        None,
    );
    builder.function_snap = Some(
        builder
            .mk_function::<(vir::Ref, vir::ManyTyVal), _>(
                "snap",
                (ref_self_decl.ty, builder.params.ty_args()),
                builder.snap_type(),
                (ref_self_decl, builder.params.ty_decls()),
                &[],
                &[],
                None,
            )
            .1,
    );
}
