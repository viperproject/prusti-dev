use crate::encoders::{
    domain::{AdtBuilder, DomainDataImmRef, DomainEnc, DomainEncOutput, DomainEncOutputRef, DomainEncSpecifics, PureTypeBuilder, PureTypeCommon}, lifted::TypeOfEnc, predicate::{PredicateBuilder, PredicateEnc, PredicateEncData, PredicateEncDataImmRef, RefToIndirectPred}
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
    let ty::TyKind::Ref(_, inner_ty, ty::Mutability::Not) = ty_kind else {
        unreachable!();
    };

    let inner_type = vir::TYPE_PSNAP;
    let (field_snaps_to_snap, field_access) = builder.constructor("", (vir::TYPE_REF, inner_type), None);

    Ok((DomainEncSpecifics::ImmRef(DomainDataImmRef {
        prim_to_snap: field_snaps_to_snap,
        deref_access: field_access[0].downcast_ty(),
        value_access: field_access[1].downcast_ty(),
    }), Ok(builder)))
}

pub(crate) fn predicate<'vir>(
    task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: DomainEncOutput<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<
    (PredicateEncData<'vir>, Option<RefToIndirectPred<'vir>>),
    EncodeFullError<'vir, PredicateEnc>,
> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Ref(_, _inner_ty, ty::Mutability::Not) = ty_kind else {
        unreachable!();
    };

    let snap_type = (snap.domain)().downcast_ty::<vir::CSnap>();

    let ref_self = builder.vcx.mk_local("self", vir::TYPE_REF);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);
    //let ref_self_ex = builder.vcx.mk_local_ex_local(ref_self);

    let snap_data = snap.specifics.expect_immref();
    let generic_typeof = TypeOfEnc::generic_typeof(deps);

    // fields
    let ref_field = builder.field("val", snap_type);

    // main predicate
    let self_pred = builder.inner.predicate::<(vir::Ref, vir::ManyTyVal)>(
        "",
        (ref_self_decl.ty(), builder.generic_tys),
    (ref_self_decl, &builder.generic_decls),
        Some(vir::expr! {
            (acc((ref_self).[ref_field]))
            && (([generic_typeof]([snap_data.value_access]([ref_field](ref_self)))) == ([builder.generic_exprs[0]]))
        }), // TODO: use generic args?
    );

    // Ref-to-snap
    builder.function_snap = Some(builder.mk_function::<(vir::Ref, vir::ManyTyVal), _>(
        "snap",
        (ref_self_decl.ty(), builder.generic_tys),
        snap_type,
        (ref_self_decl, &builder.generic_decls),
        &[vir::expr! { acc([self_pred](ref_self, ..[&builder.generic_exprs])) }],
        &[vir::expr! { ([generic_typeof]([snap_data.value_access](result: [snap_type]))) == ([builder.generic_exprs[0]]) }],
        Some(vir::expr! {
            unfolding ([self_pred](ref_self, ..[&builder.generic_exprs])) in ([ref_field](ref_self))
        }),
    ).1);

    // Ref-to-Ref
    let deref_func = builder.inner.function::<(vir::Ref, vir::ManyTyVal), _>(
        "deref",
        (ref_self_decl.ty(), builder.generic_tys),
        vir::TYPE_REF,
        (ref_self_decl, &builder.generic_decls),
        &[vir::expr! { acc([self_pred](ref_self, ..[&builder.generic_exprs])) }],
        &[],
        Some(vir::expr! {
            unfolding ([self_pred](ref_self, ..[&builder.generic_exprs])) in ([snap_data.deref_access]([ref_field](ref_self)))
        }),
    );

    Ok((
        PredicateEncData::ImmRef(PredicateEncDataImmRef {
            deref_func: deref_func,
            perm: None,
            snap_data,
        }),
        None,
    ))
}
