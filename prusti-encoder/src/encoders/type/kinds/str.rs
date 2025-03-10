use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use crate::encoders::domain::{DomainBuilder, DomainDataStruct, DomainEnc, DomainEncSpecifics};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    assert_eq!(*ty_kind, ty::TyKind::Str);

    let dummy_cons_ident = builder.function("cons", &[], builder.self_type());

    Ok(DomainEncSpecifics::StructLike(DomainDataStruct {
        field_snaps_to_snap: dummy_cons_ident,
        field_access: &[],
    }))
}
