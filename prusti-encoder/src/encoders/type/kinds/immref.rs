use crate::encoders::{
    domain::{DomainBuilder, DomainDataImmRef, DomainEnc, DomainEncSpecifics, DomainEncOutputRef},
    predicate::{PredicateBuilder, PredicateEncData, PredicateEncDataImmRef, RefToIndirectPred},
    rust_ty_snapshots::RustTySnapshotsEnc,
    snapshot::SnapshotEncOutput,
    GenericEnc, PredicateEnc,
};
use crate::TyConstructorEnc;
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    output_ref: &DomainEncOutputRef<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Ref(_, inner_ty, ty::Mutability::Not) = ty_kind else {
        unreachable!();
    };

    let inner_ty_out = deps.require_ref::<RustTySnapshotsEnc>(*inner_ty)?;
    let inner_type = inner_ty_out.generic_snapshot.snapshot.downcast_ty();

    let deref_ident = builder.function("deref", builder.self_type(), vir::TYPE_REF);
    let value_ident = builder.function("value", builder.self_type(), inner_type);
    let cons_ident = builder.function("cons", (vir::TYPE_REF, inner_type), builder.self_type());

    let generic_enc = deps.require_ref::<GenericEnc>(())?;
    let ty_type_func = deps.require_ref::<TyConstructorEnc>(task_key)?;
    builder.axiom("deref", vir::expr! {
        forall r: Ref, value: [inner_type] :: {[cons_ident](r, value)} ([deref_ident]([cons_ident](r, value))) == (r)
    });
    builder.axiom("value", vir::expr! {
        forall r: Ref, value: [inner_type] :: {[cons_ident](r, value)} ([value_ident]([cons_ident](r, value))) == (value)
    });
    builder.axiom("typeof", vir::expr! {
        forall r: [vir::TYPE_REF], p: [inner_type] ::
            {[output_ref.typeof_function](([cons_ident](r, p)) as Snap)}
            ([output_ref.typeof_function](([cons_ident](r, p)) as Snap)) == ([ty_type_func.ty_constructor]([[generic_enc.param_type_function](p)]))
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

    Ok(DomainEncSpecifics::ImmRef(DomainDataImmRef {
        prim_to_snap: cons_ident,
        deref_access: deref_ident,
        value_access: value_ident,
    }))
}

pub(crate) fn predicate<'vir>(
    task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: SnapshotEncOutput<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    generic_decls: &[vir::LocalDeclTyVal<'vir>],
    generic_exprs: &[vir::ExprTyVal<'vir>],
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

    let snap_type = snap.snapshot.downcast_ty::<vir::CSnap>();

    let ref_self = builder.vcx.mk_local("self", vir::TYPE_REF);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);
    //let ref_self_ex = builder.vcx.mk_local_ex_local(ref_self);

    let snap_data = snap.specifics.expect_immref();
    let generic = deps.require_ref::<GenericEnc>(())?;

    // fields
    let ref_field = builder.field("val", snap_type);

    let generic_tys = generic_decls
        .iter()
        .copied()
        .map(vir::LocalDeclData::ty)
        .collect::<Vec<_>>();
    let generic_tys = builder.vcx.alloc_slice(&generic_tys);

    // main predicate
    let self_pred = builder.predicate::<(vir::Ref, vir::ManyTyVal)>(
        "",
        (ref_self_decl.ty(), generic_tys),
    (ref_self_decl, generic_decls),
        Some(vir::expr! {
            (acc((ref_self).[ref_field]))
            && (([generic.param_type_function]([snap_data.value_access]([ref_field](ref_self)))) == ([generic_exprs[0]]))
        }), // TODO: use generic args?
    );

    // Ref-to-snap
    builder.function_snap = Some(builder.mk_function::<(vir::Ref, vir::ManyTyVal), _>(
        "snap",
        (ref_self_decl.ty(), generic_tys),
        snap_type,
        (ref_self_decl, generic_decls),
        &[vir::expr! { acc([self_pred](ref_self, ..[generic_exprs])) }],
        &[vir::expr! { ([generic.param_type_function]([snap_data.value_access](result: [snap_type]))) == ([generic_exprs[0]]) }],
        Some(vir::expr! {
            unfolding ([self_pred](ref_self, ..[generic_exprs])) in ([ref_field](ref_self))
        }),
    ).1);

    // Ref-to-Ref
    let deref_func = builder.function::<(vir::Ref, vir::ManyTyVal), _>(
        "deref",
        (ref_self_decl.ty(), generic_tys),
        vir::TYPE_REF,
        (ref_self_decl, generic_decls),
        &[vir::expr! { acc([self_pred](ref_self, ..[generic_exprs])) }],
        &[],
        Some(vir::expr! {
            unfolding ([self_pred](ref_self, ..[generic_exprs])) in ([snap_data.deref_access]([ref_field](ref_self)))
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
