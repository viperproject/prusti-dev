use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::HasType;

use crate::encoders::{
    domain::{DomainBuilder, DomainEnc, DomainEncOutput, DomainEncSpecifics, PureTypeBuilder, PureTypeCommon},
    predicate::{PredicateBuilder, PredicateEnc, PredicateEncData},
};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: PureTypeCommon<'vir>,
) -> Result<(DomainEncSpecifics<'vir>, PureTypeBuilder<'vir>), EncodeFullError<'vir, DomainEnc>> {
    assert_eq!(*task_key.ty().kind(), ty::TyKind::Never);
    Ok((DomainEncSpecifics::Never, Err(DomainBuilder::new(builder))))
}

pub(crate) fn predicate<'vir>(
    _task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: DomainEncOutput<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<PredicateEncData<'vir>, EncodeFullError<'vir, PredicateEnc>> {
    // let ty = task_key.ty();
    // let ty_kind = ty.kind();

    let snap_type = (snap.domain)();

    let ref_self = builder.vcx.mk_local("self", vir::TYPE_REF);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);

    // main predicate
    builder.predicate::<vir::Ref>(
        "",
        ref_self_decl.ty(),
        (ref_self_decl,),
        Some(vir::expr! { false }),
    );

    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function::<vir::Ref, _>(
                "snap",
                ref_self_decl.ty(),
                snap_type,
                (ref_self_decl,),
                &[], // &[vir::expr! { false }],
                &[],
                None,
            )
            .1,
    );

    Ok(PredicateEncData::Never)
}
