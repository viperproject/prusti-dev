//! Encoding for raw pointer types (`*const T` / `*mut T`).
//!
//! Modelled like a reference (see [`super::immref`]) but conservatively: the
//! snapshot carries the pointer address and the pointer metadata, and the
//! pointee is left opaque (there is no `value_access` into it, and we do not
//! require the pointee type to be encoded. This keeps raw pointers to
//! otherwise-unencodable types, e.g. the panic/formatting machinery, working).

use crate::encoders::{
    TyUseImpureEnc, TyUsePureEnc,
    ty::{
        RustRaw, RustTyDatas,
        data::TyData,
        impure::{PredicateBuilder, TyImpureEnc, TyImpureRaw, TyImpureRawData},
        pure::{AdtBuilder, PureTyDatas, TyPureEnc, TyPureRaw, TyPureRawData},
    },
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::CastType;

pub(crate) fn ty_pure<'vir>(
    task_key: &TyData<'vir, RustTyDatas>,
    data: &RustRaw<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureRaw<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let ty = data.metadata.decompose(task_key.params);
    let metadata = deps.require_ref::<TyUsePureEnc>(ty)?.snapshot.downcast_ty();

    // Unlike a reference, there is no value field for the (opaque) pointee.
    let (field_snaps_to_snap, field_access) =
        builder.constructor("", (vir::TYPE_REF, metadata), None);

    Ok(TyPureRawData {
        prim_to_snap: field_snaps_to_snap,
        address_access: field_access[0].downcast_ty(),
        metadata_access: field_access[1].downcast_ty(),
    })
}

pub(crate) fn ty_impure<'vir>(
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &(&RustRaw<'vir>, &TyPureRaw<'vir>),
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureRaw<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let snap_type = builder.csnap_type();

    let metadata_type = data.0.metadata.decompose(task_key.0.params);
    deps.require_dep::<TyUseImpureEnc>(metadata_type)?;
    // The pointee is opaque; we deliberately do not require its encoding.

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // fields
    let ref_field = builder.field("val", snap_type);

    // main predicate
    builder.mk_predicate("", Some(vir::expr! { acc((ref_self).[ref_field]) }));

    // Ref-to-snap
    builder.mk_snap_function(Some(vir::expr! { [ref_field](ref_self) }));

    Ok(TyImpureRawData {})
}
