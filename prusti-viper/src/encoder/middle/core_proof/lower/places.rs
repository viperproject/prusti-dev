use vir_crate::{
    common::identifier::WithIdentifier,
    low as vir_low,
    middle::{self as vir_mid, operations::ty::Typed},
};

fn address_type() -> vir_low::Type {
    vir_low::Type::domain("Address".into())
}

fn place_type() -> vir_low::Type {
    vir_low::Type::domain("Place".into())
}

fn root_address(local: &vir_mid::expression::Local) -> vir_low::Expression {
    let address_variable =
        vir_low::VariableDecl::new(format!("{}$address", local.variable.name), address_type());
    vir_low::Expression::local(address_variable, local.position.into())
}

/// Emits code that lowers `vir_mid` place into a computation of its address.
pub(super) fn compute_stack_place_address(place: &vir_mid::Expression) -> vir_low::Expression {
    assert!(place.is_place());
    match place {
        vir_mid::Expression::Local(local) => root_address(local),
        vir_mid::Expression::Field(field) => {
            let base_type_identifier = field.base.get_type().get_identifier();
            let arg = compute_stack_place_address(&*field.base);
            vir_low::Expression::domain_func_app(
                "Address".into(),
                format!(
                    "field_address$${}$${}",
                    base_type_identifier, field.field.name
                ),
                vec![arg],
                vec![vir_low::VariableDecl::new("_1", address_type())],
                address_type(),
                field.position.into(),
            )
        }
        x => unimplemented!("{}", x),
    }
}

/// Finds the root address of the place.
pub(super) fn extract_root_address(place: &vir_mid::Expression) -> vir_low::Expression {
    assert!(place.is_place());
    match place {
        vir_mid::Expression::Local(local) => root_address(local),
        vir_mid::Expression::Field(field) => extract_root_address(&field.base),
        x => unimplemented!("{}", x),
    }
}

/// Emits code that represents the place.
pub(super) fn encode_expression_as_place(place: &vir_mid::Expression) -> vir_low::Expression {
    assert!(place.is_place());
    match place {
        vir_mid::Expression::Local(local) => vir_low::Expression::domain_func_app(
            "Place".into(),
            format!("{}$place", local.variable.name),
            vec![],
            vec![],
            place_type(),
            local.position.into(),
        ),
        vir_mid::Expression::Field(field) => {
            let base_type_identifier = field.base.get_type().get_identifier();
            let arg = compute_stack_place_address(&*field.base);
            vir_low::Expression::domain_func_app(
                "Place".into(),
                format!(
                    "field_place$${}$${}",
                    base_type_identifier, field.field.name
                ),
                vec![arg],
                vec![vir_low::VariableDecl::new("_1", address_type())],
                address_type(),
                field.position.into(),
            )
        }
        x => unimplemented!("{}", x),
    }
}
