use super::{
    super::utils::place_domain_encoder::PlaceExpressionDomainEncoder, encoder::PlaceEncoder,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::{DomainsLowererInterface, Lowerer},
        type_layouts::TypeLayoutsInterface,
    },
};
use prusti_rustc_interface::data_structures::stable_set::FxHashSet;
use vir_crate::{
    common::{expression::QuantifierHelpers, identifier::WithIdentifier},
    low::{self as vir_low, macros::var_decls},
    middle::{self as vir_mid},
};

#[derive(Default)]
pub(in super::super) struct PlacesState {
    /// For which types array index axioms were generated.
    array_index_axioms: FxHashSet<vir_mid::Type>,
}

pub(in super::super) trait PlacesInterface {
    fn place_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn encode_expression_as_place(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn encode_field_place(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_place: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn encode_enum_variant_place(
        &mut self,
        base_type: &vir_mid::Type,
        variant: &vir_mid::ty::VariantIndex,
        base_place: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn encode_deref_place(
        &mut self,
        base_place: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn encode_index_place(
        &mut self,
        base_type: &vir_mid::Type,
        base_place: vir_low::Expression,
        index: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn encode_place_array_index_axioms(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> PlacesInterface for Lowerer<'p, 'v, 'tcx> {
    fn place_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type("Place")
    }
    /// Emits code that represents the place.
    fn encode_expression_as_place(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut encoder = PlaceEncoder {};
        encoder.encode_expression(place, self)
    }
    fn encode_field_place(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_place: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        self.encode_field_access_function_app("Place", base_place, base_type, field, position)
    }
    fn encode_enum_variant_place(
        &mut self,
        base_type: &vir_mid::Type,
        variant: &vir_mid::ty::VariantIndex,
        base_place: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        self.encode_variant_access_function_app("Place", base_place, base_type, variant, position)
    }
    fn encode_deref_place(
        &mut self,
        base_place: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        let return_type = self.place_type()?;
        self.create_domain_func_app(
            "Place",
            "deref_reference_place",
            vec![base_place],
            return_type,
            position,
        )
    }
    fn encode_index_place(
        &mut self,
        base_type: &vir_mid::Type,
        base_place: vir_low::Expression,
        index: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        self.encode_index_access_function_app("Place", base_place, base_type, index, position)
    }
    fn encode_place_array_index_axioms(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        if !self.places_state.array_index_axioms.contains(ty) {
            self.places_state.array_index_axioms.insert(ty.clone());
            let position = vir_low::Position::default();
            use vir_low::macros::*;
            let place_type = self.place_type()?;
            let size_type = self.size_type()?;
            var_decls! {
                place: Place,
                index: { size_type.clone() }
            };
            let function_app = self.encode_index_access_function_app(
                "Place",
                place.clone().into(),
                ty,
                index.clone().into(),
                position,
            )?;
            let place_inverse = self.create_domain_func_app(
                "Place",
                format!("index_place$${}$$inv_place", ty.get_identifier()),
                vec![function_app.clone()],
                place_type,
                position,
            )?;
            let index_inverse = self.create_domain_func_app(
                "Place",
                format!("index_place$${}$$inv_index", ty.get_identifier()),
                vec![function_app.clone()],
                size_type,
                position,
            )?;
            let body = vir_low::Expression::forall(
                vec![place.clone(), index.clone()],
                vec![vir_low::Trigger::new(vec![function_app])],
                expr! {
                    ([place_inverse] == place) &&
                    ([index_inverse] == index)
                },
            );
            let axiom = vir_low::DomainAxiomDecl {
                name: format!("index_place$${}$$injectivity_axiom", ty.get_identifier()),
                body,
            };
            self.declare_axiom("Place", axiom)?;
        }
        Ok(())
    }
}
