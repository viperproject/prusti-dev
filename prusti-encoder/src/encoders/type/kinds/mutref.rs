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

    let deref_ident = builder.function("deref", builder.self_type(), vir::TYPE_REF);
    let value_ident = builder.function("value", builder.self_type(), inner_type);
    let cons_ident = builder.function("cons", (vir::TYPE_REF, inner_type), builder.self_type());

    builder.axiom("deref", vir::expr! {
        forall r: Ref, value: [inner_type] :: {[cons_ident](r, value)} ([deref_ident]([cons_ident](r, value))) == (r)
    });
    builder.axiom("value", vir::expr! {
        forall r: Ref, value: [inner_type] :: {[cons_ident](r, value)} ([value_ident]([cons_ident](r, value))) == (value)
    });
    // builder.axiom("cons", vir::expr! {
    //     forall s: [builder.self_type()] :: {[deref_ident](s)} ([cons_ident]([deref_ident](s))) == (s)
    // });

    // TODO: was this an axiom we had???
    /*
    match ty_kind {
        ty::TyKind::Int(_) => {
            let min = builder.vcx.get_min_int(&ty_kind);
            let max = builder.vcx.get_max_int(&ty_kind);
            builder.axiom("bounds", vir::expr! {
                forall s: [builder.self_type()] :: {[deref_ident](s)} (([min]) <= ([deref_ident](s))) && (([deref_ident](s)) <= ([max]))
            });
        }
        _ => (),
    }
    */

    Ok(DomainEncSpecifics::MutRef(DomainDataMutRef {
        prim_to_snap: cons_ident,
        deref_access: deref_ident,
        value_access: value_ident,
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
