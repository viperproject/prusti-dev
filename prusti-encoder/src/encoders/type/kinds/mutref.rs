use crate::encoders::{
    domain::{DomainBuilder, DomainDataMutRef, DomainEnc, DomainEncSpecifics},
    predicate::{PredicateBuilder, PredicateEncData, PredicateEncDataMutRef, RefToIndirectPred},
    rust_ty_snapshots::RustTySnapshotsEnc,
    snapshot::SnapshotEncOutput,
    PredicateEnc,
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Ref(_, inner_ty, ty::Mutability::Mut) = ty_kind else {
        unreachable!();
    };

    let inner_ty_out = deps.require_ref::<RustTySnapshotsEnc>(*inner_ty)?;
    let inner_type = inner_ty_out.generic_snapshot.snapshot.downcast_ty();
    let (field_snaps_to_snap, field_access) = builder.constructor("", (vir::TYPE_REF, inner_type), None);

    Ok(DomainEncSpecifics::MutRef(DomainDataMutRef {
        prim_to_snap: field_snaps_to_snap,
        deref_access: field_access[0].downcast_ty(),
        value_access: field_access[1].downcast_ty(),
    }))
}

pub(crate) fn predicate<'vir>(
    _task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: SnapshotEncOutput<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<
    (PredicateEncData<'vir>, Option<RefToIndirectPred<'vir>>),
    EncodeFullError<'vir, PredicateEnc>,
> {
    //let ty = task_key.ty();
    //let ty_kind = ty.kind();
    //let ty::TyKind::Ref(_, _, _) = ty_kind else { unreachable!(); };

    let snap_type = snap.snapshot;

    let ref_self = builder.vcx.mk_local("self", vir::TYPE_REF);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);
    //let ref_self_ex = builder.vcx.mk_local_ex_local(ref_self);

    let snap_data = snap.specifics.expect_mutref();

    // fields
    let ref_field = builder.field("val", snap_type);

    // main predicate
    let self_pred = builder.predicate::<vir::Ref>(
        "",
        ref_self_decl.ty(),
        (ref_self_decl,),
        Some(vir::expr! { acc((ref_self).[ref_field]) }),
    );

    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function::<vir::Ref, _>(
                "snap",
                ref_self_decl.ty(),
                snap_type,
                (ref_self_decl,),
                &[vir::expr! { acc([self_pred](ref_self)) }],
                &[],
                Some(vir::expr! {
                    unfolding ([self_pred](ref_self)) in ([ref_field](ref_self))
                }),
            )
            .1,
    );

    // Ref-to-Ref
    let deref_func = builder.function(
        "deref",
        ref_self_decl.ty(),
        vir::TYPE_REF,
        (ref_self_decl,),
        &[vir::expr! { acc([self_pred](ref_self)) }],
        &[],
        Some(vir::expr! {
            unfolding ([self_pred](ref_self)) in ([snap_data.deref_access](([ref_field](ref_self)) as CSnap))
        }),
    );

    Ok((
        PredicateEncData::MutRef(PredicateEncDataMutRef {
            deref_func: deref_func,
            perm: None,
            snap_data,
        }),
        None,
    ))
}
