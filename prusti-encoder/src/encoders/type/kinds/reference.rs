use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::ToKnownArity;
use crate::encoders::{domain::{DomainBuilder, DomainDataRef, DomainEnc, DomainEncSpecifics}, most_generic_ty::get_vir_base_name_kind};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    assert!(matches!(ty_kind, ty::TyKind::Ref(..)));
    let prim_type = &vir::TypeData::Ref;

    let base_name = get_vir_base_name_kind(&ty_kind, builder.vcx);
    builder.set_name(&base_name);

    let typeof_ident = builder.function("typeof", &[builder.self_type()], builder.type_type());

    deps.emit_output_ref(task_key, builder.output_ref(base_name, typeof_ident.to_known()))?;

    let deref_ident = builder.function("deref", &[builder.self_type()], prim_type);
    let cons_ident = builder.function("cons", &[prim_type], builder.self_type());

    builder.axiom("deref", vir::expr! {
        forall value: [prim_type] :: {[cons_ident](value)} ([deref_ident]([cons_ident](value))) == (value)
    });
    builder.axiom("cons", vir::expr! {
        forall s: [builder.self_type()] :: {[deref_ident](s)} ([cons_ident]([deref_ident](s))) == (s)
    });

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

    Ok(DomainEncSpecifics::Ref(DomainDataRef {
        snap_to_prim: cons_ident.to_known(),
        deref_access: deref_ident.to_known(),
    }))
}
