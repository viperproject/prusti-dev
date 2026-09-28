use crate::encoders::ty::{
    RustParam, RustParamData,
    generics::ParamTypEnc,
    impure::{PredicateBuilder, TyImpureEnc, TyImpureParam},
    pure::{TyPureBuilder, TyPureEnc, TyPureParam},
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};

pub(crate) fn ty_pure<'vir>(
    data: &RustParam<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut TyPureBuilder<'vir>,
) -> Result<TyPureParam<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    // Only generic params share the `s_Param` adt; `dyn` keeps its own
    // domain.
    if let RustParamData::Dyn = data {
        builder.set_domain_builder();
    }
    Ok(())
}

pub(crate) fn ty_impure<'vir>(
    data: &(&RustParam<'vir>, &TyPureParam<'vir>),
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureParam<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    if let RustParamData::Dyn = data.0 {
        super::opaque::set_opaque(builder);
        return Ok(());
    }
    let typ = deps.require_dep::<ParamTypEnc>(())?.typ;
    builder.mk_predicate("", None);
    // The intended invariant of the predicate: its snapshot is a value of the
    // type the predicate is instantiated at. Everywhere a param is read out
    // of one, this is what lets the variant bridge recover its `s_Param`
    // variant, and with it the reconstruction from a concrete value.
    //
    // This is assumed rather than checked: a param nested in a struct, enum
    // or reference has its snapshot set by that type's assign method, so
    // constraining `p_Param_assign` alone would not cover the producers.
    builder.mk_snap_function(
        None,
        &[builder.vcx.mk_eq_expr(
            typ(builder.vcx.mk_result(vir::TYPE_PSNAP)),
            builder.params.ty_exprs()[0],
        )],
    );
    Ok(())
}
