use crate::encoders::{
    domain::{DomainBuilder, DomainEnc, DomainEncOutputRef, DomainEncSpecifics},
    most_generic_ty::get_vir_base_name_kind,
    GenericEnc,
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, CastType};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    assert!(matches!(ty_kind, ty::TyKind::Param(..)));

    let base_name = get_vir_base_name_kind(&ty_kind, builder.vcx);
    let out = deps.require_ref::<GenericEnc>(())?;
    deps.emit_output_ref(
        task_key,
        DomainEncOutputRef {
            base_name,
            domain: out.domain_param_name.cast_ty(),
            ty_param_accessors: &[],
            typeof_function: out
                .param_type_function
                .cast_ty(out.param_type_function.arity().upcast_ty()),
        },
    )?;
    Ok(DomainEncSpecifics::Param)
}
