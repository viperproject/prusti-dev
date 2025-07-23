use crate::encoders::{
    domain::{
        AdtBuilder, DomainDataStruct, DomainEnc, DomainEncOutputRef, DomainEncSpecifics, FieldTy, PureTypeBuilder, PureTypeCommon
    },
    lifted::ty::{EncodeGenericsAsParamTy, LiftedTyEnc},
    predicate::{PredicateBuilder, PredicateEncData, PredicateEncDataStruct},
    rust_ty_predicates::RustTyPredicatesEnc,
    snapshot::SnapshotEncOutput,
    PredicateEnc,
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
    let ty::TyKind::Tuple(params) = ty_kind else {
        unreachable!();
    };

    let generics = params
        .iter()
        .map(|ty| {
            deps.require_local::<LiftedTyEnc<EncodeGenericsAsParamTy>>(ty)
                .unwrap()
                .expect_generic()
        })
        .collect::<Vec<_>>();

    let fields = params
        .iter()
        .map(|ty| FieldTy::from_ty(deps, ty))
        .collect::<Result<Vec<_>, _>>()?;

    let (field_snaps_to_snap, field_access) = super::structlike::domain(
        "", &fields, &mut builder, None,
    );

    Ok((DomainEncSpecifics::StructLike(DomainDataStruct {
        field_snaps_to_snap,
        field_access,
    }), Ok(builder)))

    /*
        let generics = params
        .iter()
        .map(|ty| {
            deps.require_local::<LiftedTyEnc<EncodeGenericsAsParamTy>>(ty)
                .unwrap()
                .expect_generic()
        })
        .collect();
    let mut enc = DomainEncData::new(vcx, task_key, generics, deps);
    enc.deps
        .emit_output_ref(*task_key, enc.output_ref(base_name))?;
    let field_tys = params
        .iter()
        .map(|ty| FieldTy::from_ty(vcx, enc.deps, ty))
        .collect::<Result<Vec<_>, _>>()?;
    let specifics = enc.mk_struct_specifics(field_tys);
    return Ok((Some(enc.finalize(task_key)), specifics));
    */
}

// for struct X<'a, 'b> {
//   o: i32,
//   a: &'a mut i32,
//   b: &'b mut i32,
// }
// we should emit:
// fields accessors
// - function p_X_field_0(self: Ref): Ref
// - function p_X_field_1(self: Ref): Ref
// - function p_X_field_2(self: Ref): Ref
// predicates
// - p_X(self: Ref) { // owned fields
//     p_Int_i32(p_X_field_0(self))
//     && p_Ref_mutable(p_X_field_1(self), s_Int_i32_type())
//     && p_Ref_mutable(p_X_field_2(self), s_Int_i32_type())
//   }
// - p_X_lft0(self: s_X) { // projection through 'a
//     p_Int_i32(s_Ref_deref(s_X_read_1(self)))
//   }
// - p_X_lft0(self: s_X) { // projection through 'a
//     p_Int_i32(s_Ref_deref(s_X_read_2(self)))
//   }
// functions
// - function p_X_unreachable(): s_X // for now; should be moved to domain encoder
// - function p_X_snap(self: Ref): s_X { .. }
// methods
// - method assign_p_X(self: Ref, value: s_X)

pub(crate) fn predicate<'vir>(
    task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: SnapshotEncOutput<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    generic_decls: &[vir::LocalDeclTyVal<'vir>],
    generic_exprs: &[vir::ExprTyVal<'vir>],
    builder: &mut PredicateBuilder<'vir>,
) -> Result<PredicateEncData<'vir>, EncodeFullError<'vir, PredicateEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Tuple(params) = ty_kind else {
        unreachable!();
    };

    let snap_type = snap.snapshot.downcast_ty::<vir::CSnap>();
    let snap_data = snap.specifics.expect_structlike();

    //let snap_self = builder.vcx.mk_local("self", snap_type);
    //let snap_self_decl = builder.vcx.mk_local_decl_local(snap_self);
    //let snap_self_ex: vir::Expr = builder.vcx.mk_local_ex_local(snap_self);

    let ref_self = builder.vcx.mk_local("self", vir::TYPE_REF);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);
    //let ref_self_ex = builder.vcx.mk_local_ex_local(ref_self);

    let fields = params
        .iter()
        .map(|ty| deps.require_ref::<RustTyPredicatesEnc>(ty))
        .collect::<Result<Vec<_>, _>>()?;

    let (field_accessors, self_pred, snap_expr) = super::structlike::predicate(
        "",
        &fields,
        task_key,
        &snap,
        snap_data.field_snaps_to_snap,
        deps,
        generic_decls,
        generic_exprs,
        builder,
    )?;

    let generic_decls_tys = builder.vcx.alloc_slice(
        generic_decls
            .iter()
            .copied()
            .map(vir::LocalDeclData::ty)
            .collect::<Vec<_>>()
            .as_slice(),
    );
    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function::<(vir::Ref, vir::ManyTyVal), vir::CSnap>(
                "snap",
                (ref_self_decl.ty(), generic_decls_tys),
                snap_type,
                (ref_self_decl, generic_decls),
                &[vir::expr! { acc([self_pred](ref_self, ..[generic_exprs])) }],
                &[],
                Some(snap_expr),
            )
            .1,
    );

    Ok(PredicateEncData::StructLike(PredicateEncDataStruct {
        snap_data,
        ref_to_field_refs: builder.vcx.alloc_slice(&field_accessors),
    }))
}
