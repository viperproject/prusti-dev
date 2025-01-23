use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::ToKnownArity;
use crate::encoders::{domain::{DomainBuilder, DomainDataPrim, DomainEnc, DomainEncSpecifics}, most_generic_ty::get_vir_base_name_kind, predicate::{PredicateBuilder, PredicateEncData, PredicateEncOutput}, snapshot::SnapshotEncOutput, PredicateEnc, PredicateEncOutputRef};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let prim_type = match ty_kind {
        ty::TyKind::Bool => &vir::TypeData::Bool,
        ty::TyKind::Char
        | ty::TyKind::Int(_)
        | ty::TyKind::Uint(_) => &vir::TypeData::Int,
        ty::TyKind::Float(_) => todo!(),
        _ => unreachable!(),
    };

    let base_name = get_vir_base_name_kind(&ty_kind, builder.vcx);
    builder.set_name(&base_name);

    let typeof_ident = builder.function("typeof", &[builder.self_type()], builder.type_type());

    deps.emit_output_ref(task_key, builder.output_ref(base_name, typeof_ident.to_known()))?;

    let value_ident = builder.function("value", &[builder.self_type()], prim_type);
    let cons_ident = builder.function("cons", &[prim_type], builder.self_type());

    builder.axiom("value", vir::expr! {
        forall value: [prim_type] :: {[cons_ident](value)} ([value_ident]([cons_ident](value))) == (value)
    });
    builder.axiom("cons", vir::expr! {
        forall s: [builder.self_type()] :: {[value_ident](s)} ([cons_ident]([value_ident](s))) == (s)
    });

    match ty_kind {
        ty::TyKind::Int(_) => {
            let min = builder.vcx.get_min_int(&ty_kind);
            let max = builder.vcx.get_max_int(&ty_kind);
            builder.axiom("bounds", vir::expr! {
                forall s: [builder.self_type()] :: {[value_ident](s)} (([min]) <= ([value_ident](s))) && (([value_ident](s)) <= ([max]))
            });
        }
        _ => (),
    }

    Ok(DomainEncSpecifics::Primitive(DomainDataPrim {
        prim_type,
        snap_to_prim: value_ident.to_known(),
        prim_to_snap: cons_ident.to_known(),
    }))
}

pub(crate) fn predicate<'vir>(
    task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: SnapshotEncOutput<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<(usize, usize), EncodeFullError<'vir, PredicateEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();

    let base_name = get_vir_base_name_kind(&ty_kind, builder.vcx);
    builder.set_name(&base_name);

    let snap_type = snap.snapshot;

    let snap_self = builder.vcx.mk_local("self", snap_type);

    let ref_self = builder.vcx.mk_local("self", &vir::TypeData::Ref);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);

    let self_pred_ident = builder.predicate_ident(
        "",
        &[ref_self_decl],
    );
    let snap_func_ident = builder.function_ident(
        "snap",
        &[ref_self_decl],
        snap_type,
    );

    // unreachable (requires false) to snap (TODO: move to domain enc)
    let unr_idx = builder.functions.len();
    let unreachable_to_snap = builder.function(
        "unreachable",
        &[],
        snap_type,
        &[builder.vcx.mk_bool::<false>()],
        &[builder.vcx.mk_bool::<false>()], // TODO: is this necessary?
        None,
    );

    // assign method
    let value = builder.vcx.mk_local("value", snap_type);
    let method_assign = builder.method(
        "assign",
        &[
            ref_self_decl,
            builder.vcx.mk_local_decl_local(value),
        ],
        &[],
        &[],
        &[
            vir::expr! { [self_pred_ident](ref_self) },
            vir::expr! { ([snap_func_ident](ref_self)) == (value) },
        ],
    );

    let snap_data = snap.specifics.expect_primitive();

    // fields
    let prim_field = builder.field(
        "val",
        snap_type,
    );

    // main predicate
    let self_pred = builder.predicate(
        "",
        &[ref_self_decl],
        Some(vir::expr! { acc_field([prim_field](ref_self)) }),
    );

    // Ref-to-snap
    let snap_idx = builder.functions.len();
    let snap_func = builder.function(
        "snap",
        &[ref_self_decl],
        snap_type,
        &[vir::expr! { acc_wildcard([self_pred](ref_self)) }],
        &[],
        Some(vir::expr! {
            unfolding_wildcard ([self_pred](ref_self)) in ([prim_field](ref_self))
        }),
    );

    deps.emit_output_ref(
        task_key,
        PredicateEncOutputRef {
            ref_to_pred: self_pred,
            ref_to_snap: snap_func,
            unreachable_to_snap: unreachable_to_snap.to_known(),
            method_assign,
            snapshot: snap_type,
            specifics: PredicateEncData::Primitive(snap_data),
            generics: &[],
        },
    )?;

    Ok((unr_idx, snap_idx))
}
