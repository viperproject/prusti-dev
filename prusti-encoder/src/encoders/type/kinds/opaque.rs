use crate::encoders::domain::{DomainBuilder, DomainEnc, DomainEncSpecifics, PureTypeBuilder, PureTypeCommon};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};

pub(crate) fn domain<'vir>(
    _task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: PureTypeCommon<'vir>,
) -> Result<(DomainEncSpecifics<'vir>, PureTypeBuilder<'vir>), EncodeFullError<'vir, DomainEnc>> {
    Ok((DomainEncSpecifics::Opaque, Err(DomainBuilder::new(builder))))
}
