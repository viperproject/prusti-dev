use task_encoder::EncodeFullError;

use crate::encoders::ty::{
    RustBuiltin, RustBuiltinData, impure,
    interpretation::real,
    pure::{AdtBuilder, TyPureBuiltin, TyPureEnc},
};

pub(crate) fn ty_pure<'vir>(
    data: &RustBuiltin<'vir>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureBuiltin<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    match data {
        RustBuiltinData::BuiltinReal => real::ty_pure(builder),
        RustBuiltinData::BuiltinGhost => {
            builder.constructor::<()>("", (), None);
            Ok(TyPureBuiltin::TyPureBuiltinGhost)
        }
    }
}

pub(crate) fn ty_impure<'vir>(
    data: &(&RustBuiltin<'vir>, &TyPureBuiltin<'vir>),
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, impure::TyImpureEnc>,
    builder: &mut impure::PredicateBuilder<'vir>,
) -> Result<impure::TyImpureBuiltin<'vir>, EncodeFullError<'vir, impure::TyImpureEnc>> {
    match data.0 {
        RustBuiltinData::BuiltinReal => real::ty_impure((), deps, builder),
        RustBuiltinData::BuiltinGhost => {
            super::opaque::set_opaque(builder);
            Ok(())
        }
    }
}
