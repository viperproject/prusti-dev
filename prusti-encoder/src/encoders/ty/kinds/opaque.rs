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
    builder.mk_predicate("", None);
    builder.mk_snap_function(None);
}
