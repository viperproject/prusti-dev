use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{AdtDestructorData, CastType, FunctionIdn, HasType, TYPE_PERM};

use crate::encoders::ty::{
    impure::{PredicateBuilder, TyImpureBuiltin, TyImpureEnc},
    pure::{AdtBuilder, TyPureBuiltinData, TyPureEnc},
};

#[derive(Debug, Clone, Copy)]
pub struct TyRealLocal<'vir> {
    pub perm_to_snap: FunctionIdn<'vir, vir::Perm, vir::CSnap>,
    pub snap_to_perm: &'vir AdtDestructorData<'vir, vir::CSnap, vir::Perm>,
}

pub(crate) fn ty_pure<'vir>(
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureBuiltinData<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let (cons, vec) = builder.constructor("", TYPE_PERM, None);
    Ok(TyPureBuiltinData::TyPureBuiltinReal(TyRealLocal {
        perm_to_snap: cons,
        snap_to_perm: vec.first().unwrap().downcast_ty(),
    }))
}

pub(crate) fn ty_impure<'vir>(
    _data: (),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureBuiltin<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let snap_type = builder.csnap_type();

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // fields
    let prim_field = builder.field("val", snap_type);

    // main predicate
    let self_pred = builder.predicate::<vir::Ref>(
        "",
        ref_self_decl.ty(),
        (ref_self_decl,),
        Some(vir::expr! { acc((ref_self).[prim_field]) }),
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
                    unfolding ([self_pred](ref_self)) in ([prim_field](ref_self))
                }),
            )
            .1,
    );

    Ok(())
}
