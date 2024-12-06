use prusti_rustc_interface::middle::ty;

use crate::encoders::domain::{DomainBuilder, DomainEncSpecifics};

pub(crate) fn domain<'vir>(
    ty: ty::Ty<'vir>,
    builder: &mut DomainBuilder<'vir>
) -> DomainEncSpecifics<'vir> {
    let ty_kind = ty.kind();
    assert_eq!(*ty_kind, ty::TyKind::Never);

    builder.set_name("never");
    builder.emit_output_ref();

    let cons_ident = builder.function("cons", &[], builder.self_type());
    builder.function("type", &[builder.self_type()], builder.type_type());

    todo!()
    //DomainEncSpecifics::Primitive(DomainDataPrim {
    //    prim_type,
    //    snap_to_prim: value_ident.to_known(),
    //    prim_to_snap: cons_ident.to_known(),
    //})

    /*

    let prim_type_args = vec![FieldTy {
        ty: prim_type,
        rust_ty_data: None,
    }];
    let data = self.mk_field_functions(&prim_type_args, None, ty.is_integral());
    // TODO: what to do about write?
    let snap_to_prim = data.field_access[0].read;
    let specifics = DomainDataPrim {
        prim_type,
        snap_to_prim,
        prim_to_snap: data.field_snaps_to_snap.to_known(),
    };
    if let Some((lower, upper)) = specifics.bounds(ty) {
        let exp = snap_to_prim.apply(self.vcx, [self.self_ex]);
        let axiom = self.mk_bounds_axiom(self.domain.name_str(), exp, lower, upper);
        self.axioms.push(axiom);
    }
    DomainEncSpecifics::Primitive(specifics)
    */
}
