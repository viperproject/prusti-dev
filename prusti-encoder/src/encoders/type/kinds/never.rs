use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::ToKnownArity;

use crate::encoders::domain::{DomainBuilder, DomainDataEnum, DomainDataStruct, DomainEnc, DomainEncSpecifics};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    assert_eq!(*ty_kind, ty::TyKind::Never);

    let base_name = "Never".to_string();
    builder.set_name(&base_name);

    let typeof_ident = builder.function("typeof", &[builder.self_type()], builder.type_type());
    let dummy_cons_ident = builder.function("cons", &[], builder.self_type());

    deps.emit_output_ref(task_key, builder.output_ref(base_name, typeof_ident.to_known()))?;

    //Ok(DomainEncSpecifics::EnumLike(DomainDataEnum {
    //    discr_ty: &vir::TypeData::Int,
    //    discr_prim: 
    //}))

    Ok(DomainEncSpecifics::StructLike(DomainDataStruct {
        field_snaps_to_snap: dummy_cons_ident,
        field_access: &[],
    }))
}
