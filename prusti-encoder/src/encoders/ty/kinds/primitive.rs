use crate::encoders::ty::{
    RustPrimitive,
    impure::{PredicateBuilder, TyImpureEnc, TyImpurePrimitive},
    interpretation::float::ty_pure_float,
    pure::{
        DomainBuilder, TyPureEnc, TyPurePrimData, TyPurePrimDataKind, TyPurePrimDataNative,
        TyPurePrimitive,
    },
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, HasType, VirCtxt};

pub(crate) fn ty_pure<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    data: &RustPrimitive<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<TyPurePrimitive<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let ty = data;
    let ty_kind = ty.kind();

    let prim_type: vir::TypePrim<'vir> = match ty_kind {
        ty::TyKind::Bool => vir::TYPE_BOOL.upcast_ty(),
        ty::TyKind::Char | ty::TyKind::Int(_) | ty::TyKind::Uint(_) => vir::TYPE_INT.upcast_ty(),
        ty::TyKind::Float(_) => vir::TYPE_INT.upcast_ty(),
        _ => unreachable!(),
    };

    let cons_ident = builder.function("cons", prim_type, builder.self_type());

    let kind = match ty_kind {
        ty::TyKind::Float(float) => {
            let data = ty_pure_float(vcx, deps, builder, *float, cons_ident)?;
            TyPurePrimDataKind::Float(vcx.alloc(data))
        }
        _ => {
            let value_ident = builder.function("value", builder.self_type(), prim_type);

            builder.axiom("cons", vir::expr! {
                forall s: [builder.self_type()] :: {[value_ident](s)} ([cons_ident]([value_ident](s))) == (s)
            });

            match ty_kind {
                ty::TyKind::Int(_) | ty::TyKind::Uint(_) => {
                    let min = builder.vcx.get_min_int(ty_kind);
                    let max = builder.vcx.get_max_int(ty_kind);
                    builder.axiom("bounds", vir::expr! {
                        forall s: [builder.self_type()] :: {[value_ident](s)} (([min]) <= (([value_ident](s)) as Int)) && ((([value_ident](s)) as Int) <= ([max]))
                    });
                    builder.axiom(
                        "value",
                        vir::expr! {
                            forall value: [prim_type] :: {[cons_ident](value)}
                                ((([min]) <= ((value) as Int)) && (((value) as Int) <= ([max])))
                                    ==> (([value_ident]([cons_ident](value))) == (value))
                        },
                    );
                }
                _ => {
                    builder.axiom("value", vir::expr! {
                        forall value: [prim_type] :: {[cons_ident](value)} ([value_ident]([cons_ident](value))) == (value)
                    });
                }
            };
            TyPurePrimDataKind::Native(TyPurePrimDataNative {
                snap_to_prim: value_ident,
            })
        }
    };
    Ok(TyPurePrimData {
        prim_type,
        prim_to_snap: cons_ident,
        kind,
    })
}

pub(crate) fn ty_impure<'vir>(
    _data: &(&RustPrimitive<'vir>, &TyPurePrimitive<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpurePrimitive<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    // let ty = data.ty();
    // let ty_kind = ty.kind();

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
