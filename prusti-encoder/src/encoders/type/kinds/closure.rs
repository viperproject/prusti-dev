use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use crate::encoders::domain::{DomainBuilder, DomainDataStruct, DomainEnc, DomainEncSpecifics, FieldTy};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Closure(_def_id, args) = ty_kind else { unreachable!(); };

    let cl_args = args.as_closure();
    let fields = cl_args
        .upvar_tys()
        .iter()
        .map(|ty| FieldTy::from_ty(builder.vcx, deps, ty))
        .collect::<Result<Vec<_>, _>>()?;

    let (field_snaps_to_snap, field_access, _) = super::structlike::domain("", &fields, builder)?;

    Ok(DomainEncSpecifics::StructLike(DomainDataStruct {
        field_snaps_to_snap,
        field_access,
    }))

/*
let cl_args = args.as_closure();
let params = cl_args.parent_args();
let generics = params
    .iter()
    .filter_map(|p| p.as_type())
    .map(|ty| {
        deps.require_local::<LiftedTyEnc<EncodeGenericsAsParamTy>>(ty)
            .unwrap()
            .expect_generic()
    })
    .collect();
let fields = cl_args
    .upvar_tys()
    .iter()
    .map(|ty| FieldTy::from_ty(vcx, deps, ty))
    .collect::<Result<Vec<_>, _>>()?;
let mut enc = DomainEncData::new(vcx, task_key, generics, deps);
enc.deps
    .emit_output_ref(*task_key, enc.output_ref(base_name))?;
let specifics = enc.mk_struct_specifics(fields);
return Ok((Some(enc.finalize(task_key)), specifics));
*/
}
