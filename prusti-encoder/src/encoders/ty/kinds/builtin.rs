use task_encoder::EncodeFullError;

use crate::encoders::ty::{
    RustBuiltin, RustBuiltinData, impure,
    pure::{TyPureBuilder, TyPureBuiltin, TyPureBuiltinData, TyPureEnc},
};

pub(crate) fn ty_pure<'vir>(
    data: &RustBuiltin<'vir>,
    _builder: &mut TyPureBuilder<'vir>,
) -> Result<TyPureBuiltin<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    match data {
        // Represented directly by the native Viper `Int`/`Perm` types (see
        // `TyPureBuilder::new`); there is nothing to emit.
        RustBuiltinData::Int => Ok(TyPureBuiltinData::Int),
        RustBuiltinData::Real => Ok(TyPureBuiltinData::Real),
    }
}

pub(crate) fn ty_impure<'vir>(
    data: &(&RustBuiltin<'vir>, &TyPureBuiltin<'vir>),
    _deps: &mut task_encoder::TaskEncoderDependencies<'vir, impure::TyImpureEnc>,
    builder: &mut impure::PredicateBuilder<'vir>,
) -> Result<impure::TyImpureBuiltin<'vir>, EncodeFullError<'vir, impure::TyImpureEnc>> {
    match data.0 {
        RustBuiltinData::Int | RustBuiltinData::Real => {
            super::primitive::set_primitive(builder);
            Ok(())
        }
    }
}
