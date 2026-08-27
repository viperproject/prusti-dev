//! The hardcoded extras of `Box` on top of its regular struct encoding: the
//! address/metadata of (and permission to) the boxed `T` at the raw pointer it
//! stores, exposed as its `value` field (see `RustTySpecial::Box`).

use prusti_rustc_interface::abi;

use crate::encoders::ty::{
    RustTyDatas, RustTyDecomposition,
    data::{StructData, TyData},
    impure::{PredicateBuilder, TyImpureBoxData},
    pure::{AdtBuilder, PureTyDatas, TyPureBoxData, TyPureEnc, TyPureFieldRef},
    use_impure::TyUseImpure,
    use_pure::TyUsePureEnc,
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, HasType};

/// The address/metadata of the boxed `T` (the value field of a `Box`), read
/// out of the raw pointer's snapshot down the `Unique`/`NonNull` chain, and
/// the reverse: the `Unique` snapshot rebuilt around a new pointer. All are
/// functions of the `Unique` field's snapshot: that is where the pointer
/// lives, and (unlike the whole box) it is what the impure side has a
/// snapshot of when the address is needed. Returns the box data and the
/// address (of the value field).
pub(super) fn mk_pure_box_data<'vir>(
    task_key: &TyData<'vir, RustTyDatas>,
    data: &StructData<'vir, RustTyDatas>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<
    (
        TyPureBoxData<'vir>,
        vir::FunctionIdn<'vir, vir::CSnap, vir::Ref>,
    ),
    EncodeFullError<'vir, TyPureEnc>,
> {
    let first = |ty: &RustTyDecomposition<'vir>| {
        ty.ty.expect_structlike().fields[abi::FieldIdx::ZERO.as_usize()]
            .decompose_context(ty.ty.params, ty.args)
    };
    let unique_ty = data.fields[0].ty().decompose(task_key.params);
    let nonnull_ty = first(&unique_ty);
    let raw_ty = first(&nonnull_ty);
    let unique_use = deps.require_dep::<TyUsePureEnc>(unique_ty)?;
    let nonnull_use = deps.require_dep::<TyUsePureEnc>(nonnull_ty)?;
    let raw_use = deps.require_dep::<TyUsePureEnc>(raw_ty)?;

    let unique_decl = builder
        .vcx
        .mk_local_decl("ptr", unique_use.snapshot.downcast_ty::<vir::CSnap>());
    let unique_snap = builder.vcx.mk_local_ex(unique_decl);
    let unique = unique_use.expect_structlike();
    let nonnull = nonnull_use.expect_structlike();
    let raw = raw_use.expect_raw();
    let nonnull_snap = unique[abi::FieldIdx::ZERO].read(unique_snap).downcast_ty();
    let raw_snap = nonnull[abi::FieldIdx::ZERO]
        .read(nonnull_snap)
        .downcast_ty();

    let address_access = builder.function(
        "address",
        unique_decl.ty(),
        vir::TYPE_REF,
        (unique_decl,),
        &[],
        &[],
        Some(raw.address_access(raw_snap)),
    );
    let metadata_access = builder.function(
        "metadata",
        unique_decl.ty(),
        vir::TYPE_PSNAP,
        (unique_decl,),
        &[],
        &[],
        Some(raw.metadata_access(raw_snap).downcast_ty()),
    );

    // The `Unique` with its raw pointer replaced (its other fields kept).
    let address_decl = builder.vcx.mk_local_decl("address", vir::TYPE_REF);
    let metadata_decl = builder.vcx.mk_local_decl("metadata", vir::TYPE_PSNAP);
    let new_raw = raw.prim_to_snap(
        builder.vcx.mk_local_ex(address_decl),
        builder.vcx.mk_local_ex(metadata_decl).upcast_ty(),
    );
    let new_nonnull = nonnull.field_snaps_to_snap(vec![new_raw.upcast_ty()]);
    let mut unique_snaps = vec![new_nonnull.upcast_ty()];
    unique_snaps.extend(unique.fields[1..].iter().map(|f| f.read(unique_snap)));
    let mk_unique = builder.function(
        "mk_unique",
        (unique_decl.ty(), address_decl.ty(), metadata_decl.ty()),
        unique_decl.ty(),
        (unique_decl, address_decl, metadata_decl),
        &[],
        &[],
        Some(unique.field_snaps_to_snap(unique_snaps)),
    );

    Ok((
        TyPureBoxData {
            metadata_access,
            mk_unique,
        },
        address_access,
    ))
}

/// The heap-dependent `address`/`metadata` functions of a `Box`: the pure
/// accessors applied to the `Unique` field's snapshot, read out of its
/// (folded) predicate. Returns the box data and the `address` accessor.
pub(super) fn mk_impure_box_data<'vir>(
    data: &StructData<'vir, (RustTyDatas, PureTyDatas)>,
    fields: &[TyUseImpure<'vir>],
    builder: &mut PredicateBuilder<'vir>,
) -> (
    TyImpureBoxData<'vir>,
    vir::FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::Ref>,
) {
    let ref_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_decl);
    let TyPureFieldRef::Constant(unique_field_ref) = data.fields[0].1.ref_to_field_ref else {
        unreachable!()
    };
    let b_params = &builder.params;
    let unique_ref = unique_field_ref(ref_self, b_params.ty_exprs(), b_params.const_exprs());
    let unique_snap = fields[0].ref_to_snap(unique_ref).downcast_ty();
    let unique_pred = fields[0].ref_to_pred(builder.vcx, unique_ref, None);
    let pure = data.1.box_data.unwrap();
    let TyPureFieldRef::Dynamic(address_access) = data.fields.last().unwrap().1.ref_to_field_ref
    else {
        unreachable!()
    };
    let args = (ref_decl.ty(), b_params.ty_args(), b_params.const_args());
    let params = (ref_decl, b_params.ty_decls(), b_params.const_decls());
    let address = builder.inner.function(
        "address",
        args,
        vir::TYPE_REF,
        params,
        &[unique_pred],
        &[],
        Some(address_access.call()(unique_snap)),
    );
    let metadata = builder.inner.function(
        "metadata",
        args,
        vir::TYPE_PSNAP,
        params,
        &[unique_pred],
        &[],
        Some(pure.metadata_access.call()(unique_snap)),
    );
    (TyImpureBoxData { metadata }, address)
}
