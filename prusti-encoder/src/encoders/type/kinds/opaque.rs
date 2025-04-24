use crate::encoders::domain::{DomainBuilder, DomainEnc, DomainEncSpecifics};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};

pub(crate) fn domain<'vir>(
    _task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    _builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    Ok(DomainEncSpecifics::Opaque)
}
