use crate::encoders::{
    domain::{
        AdtBuilder, DomainDataStruct, DomainEnc, DomainEncOutput, DomainEncOutputRef, DomainEncSpecifics, FieldTy, PureTypeBuilder, PureTypeCommon
    },
    predicate::{PredicateBuilder, PredicateEnc, PredicateEncData, PredicateEncDataStruct},
    ty_impure::TyImpureEnc, ty_pure::TyPureEncOutput,
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    output_ref: &DomainEncOutputRef<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: PureTypeCommon<'vir>,
) -> Result<(DomainEncSpecifics<'vir>, PureTypeBuilder<'vir>), EncodeFullError<'vir, DomainEnc>> {
    let mut builder = AdtBuilder::new(builder);
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Closure(_def_id, args) = ty_kind else {
        unreachable!();
    };

    let cl_args = args.as_closure();
    let fields = cl_args
        .upvar_tys()
        .iter()
        .map(|ty| FieldTy::from_ty(deps, ty))
        .collect::<Result<Vec<_>, _>>()?;

    let (field_snaps_to_snap, field_access) =
        super::structlike::domain("", &fields, &mut builder, None);

    Ok((DomainEncSpecifics::StructLike(DomainDataStruct::new(
        field_snaps_to_snap,
        field_access,
    )), Ok(builder)))

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

pub(crate) fn predicate<'vir>(
    task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: DomainEncOutput<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<PredicateEncData<'vir>, EncodeFullError<'vir, PredicateEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Closure(_def_id, args) = ty_kind else {
        unreachable!();
    };

    let snap_type = (snap.domain)().downcast_ty::<vir::CSnap>();
    let snap_data = snap.specifics.expect_structlike();

    let ref_self = builder.vcx.mk_local("self", vir::TYPE_REF);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);
    //let ref_self_ex = builder.vcx.mk_local_ex_local(ref_self);

    let cl_args = args.as_closure();
    let fields = cl_args
        .upvar_tys()
        .iter()
        .map(|ty| deps.require_local::<TyImpureEnc>(ty))
        .collect::<Result<Vec<_>, _>>()?;

    let (field_accessors, self_pred, snap_expr) = super::structlike::predicate(
        "",
        &fields,
        task_key,
        &snap,
        snap_data,
        deps,
        builder,
    )?;

    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function::<(vir::Ref, vir::ManyTyVal), vir::CSnap>(
                "snap",
                (ref_self_decl.ty(), builder.generic_tys),
                snap_type,
                (ref_self_decl, &builder.generic_decls),
                &[vir::expr! { acc([self_pred](ref_self, ..[&builder.generic_exprs])) }],
                &[],
                Some(snap_expr),
            )
            .1,
    );

    Ok(PredicateEncData::StructLike(PredicateEncDataStruct {
        snap_data,
        ref_to_field_refs: builder.vcx.alloc_slice(field_accessors.as_slice()),
    }))
}
