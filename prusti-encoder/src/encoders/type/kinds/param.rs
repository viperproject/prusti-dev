use crate::encoders::{
    domain::{DomainBuilder, DomainEnc, DomainEncOutputRef, DomainEncSpecifics, PureTypeBuilder, PureTypeCommon},
    most_generic_ty::get_vir_base_name_kind,
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, CastType};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: PureTypeCommon<'vir>,
) -> Result<(DomainEncSpecifics<'vir>, PureTypeBuilder<'vir>), EncodeFullError<'vir, DomainEnc>> {
    Ok((DomainEncSpecifics::Param, Err(DomainBuilder::new(builder))))
}
