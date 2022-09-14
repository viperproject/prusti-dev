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
use prusti_rustc_interface::data_structures::fx::FxHashSet;
use vir_crate::{
    common::{
        builtin_constants::{PLACE_DOMAIN_NAME, PLACE_OPTION_DOMAIN_NAME},
        expression::QuantifierHelpers,
        identifier::WithIdentifier,
        position::Positioned,
    },
    low::{self as vir_low, macros::var_decls, operations::ty::Typed},
    middle::{self as vir_mid},
};

#[derive(Default)]
pub(in super::super) struct PlacesState {
    /// For which types array index axioms were generated.
    array_index_axioms: FxHashSet<String>,
}

pub(in super::super) trait PlacesInterface {
    fn place_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn place_option_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn place_option_some_constructor(
        &mut self,
        place: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn place_option_none_constructor(
        &mut self,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
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
    fn encode_aliased_place_root(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> PlacesInterface for Lowerer<'p, 'v, 'tcx> {
    fn place_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type(PLACE_DOMAIN_NAME)
    }
    fn place_option_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type(PLACE_OPTION_DOMAIN_NAME)
    }
    fn place_option_some_constructor(
        &mut self,
        place: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        debug_assert_eq!(place.get_type(), &self.place_type()?);
        let place_option_type = self.place_option_type()?;
        let position = place.position();
        self.create_domain_func_app(
            PLACE_OPTION_DOMAIN_NAME,
            "place_option_some",
            vec![place],
            place_option_type,
            position,
        )
    }
    fn place_option_none_constructor(
        &mut self,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let place_option_type = self.place_option_type()?;
        self.create_domain_func_app(
            PLACE_OPTION_DOMAIN_NAME,
            "place_option_none",
            Vec::new(),
            place_option_type,
            position,
        )
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
        debug_assert_eq!(base_place.get_type(), &self.place_option_type()?);
        self.encode_field_access_function_app(
            PLACE_OPTION_DOMAIN_NAME,
            base_place,
            base_type,
            field,
            position,
        )
    }
    fn encode_enum_variant_place(
        &mut self,
        base_type: &vir_mid::Type,
        variant: &vir_mid::ty::VariantIndex,
        base_place: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        self.encode_variant_access_function_app(
            PLACE_OPTION_DOMAIN_NAME,
            base_place,
            base_type,
            variant,
            position,
        )
    }
    fn encode_deref_place(
        &mut self,
        base_place: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        debug_assert_eq!(base_place.get_type(), &self.place_option_type()?);
        let return_type = self.place_option_type()?;
        self.create_domain_func_app(
            PLACE_OPTION_DOMAIN_NAME,
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
        self.encode_index_access_function_app(
            PLACE_OPTION_DOMAIN_NAME,
            base_place,
            base_type,
            index,
            position,
        )
    }
    fn encode_place_array_index_axioms(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let identifier = ty.get_identifier();
        if !self.places_state.array_index_axioms.contains(&identifier) {
            self.places_state.array_index_axioms.insert(identifier);
            let position = vir_low::Position::default();
            use vir_low::macros::*;
            let place_type = self.place_type()?;
            let size_type = self.size_type()?;
            var_decls! {
                place: Place,
                index: { size_type.clone() }
            };
            let function_app = self.encode_index_access_function_app(
                PLACE_DOMAIN_NAME,
                place.clone().into(),
                ty,
                index.clone().into(),
                position,
            )?;
            let place_inverse = self.create_domain_func_app(
                PLACE_DOMAIN_NAME,
                format!("index_place$${}$$inv_place", ty.get_identifier()),
                vec![function_app.clone()],
                place_type,
                position,
            )?;
            let index_inverse = self.create_domain_func_app(
                PLACE_DOMAIN_NAME,
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
                comment: None,
                name: format!("index_place$${}$$injectivity_axiom", ty.get_identifier()),
                body,
            };
            self.declare_axiom(PLACE_DOMAIN_NAME, axiom)?;
        }
        Ok(())
    }
    fn encode_aliased_place_root(
        &mut self,
        _position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        unimplemented!();
        // let return_type = self.place_type()?;
        // let place_root = self.create_domain_func_app(
        //     PLACE_OPTION_DOMAIN_NAME,
        //     "aliased_place_root",
        //     vec![],
        //     return_type,
        //     position,
        // )?;
        // self.encode_compute_address_for_place_root(&place_root)?;
        // Ok(place_root)
    }
}
