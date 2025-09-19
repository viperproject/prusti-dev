use crate::encoders::ty::{
    RustParam,
    impure::{PredicateBuilder, TyImpureEnc, TyImpureParam},
    pure::{DomainBuilder, TyPureEnc, TyPureParam},
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};

pub(crate) fn ty_pure<'vir>(
    _data: &RustParam<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    _builder: &mut DomainBuilder<'vir>,
) -> Result<TyPureParam<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    Ok(())
}

pub(crate) fn ty_impure<'vir>(
    _data: &(&RustParam<'vir>, &TyPureParam<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureParam<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    super::opaque::set_opaque(builder);
    Ok(())
}
