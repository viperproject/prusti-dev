use super::{
    super::utils::place_domain_encoder::PlaceExpressionDomainEncoder, encoder::PlaceAddressEncoder,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::{DomainsLowererInterface, Lowerer},
        pointers::PointersInterface,
        snapshots::SnapshotVariablesInterface,
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    common::{
        builtin_constants::ADDRESS_DOMAIN_NAME, expression::QuantifierHelpers, position::Positioned,
    },
    low as vir_low,
    middle::{self as vir_mid},
};

pub(in super::super) trait AddressesInterface {
    fn address_domain(&self) -> &'static str;
    fn address_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn address_null(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn address_offset(
        &mut self,
        size: vir_low::Expression,
        address: vir_low::Expression,
        offset: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    /// Constructs a variable representing the address of the given MIR-level
    /// variable.
    fn root_address(
        &mut self,
        local: &vir_mid::expression::Local,
        old_label: &Option<String>,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    /// Get the variable representing the root address of this place.
    fn extract_root_address(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    /// Emits code that represents the place's address. This method is supposed
    /// to be used in procedures for places whose root addresses are tracked
    /// with SSA variables. For addresses inside predicates, use
    /// `encode_expression_as_place_address_in_predicate`.
    fn encode_expression_as_place_address(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    // fn encode_expression_as_place_address_in_predicate(
    //     &mut self,
    //     place: &vir_mid::Expression,
    //     self_address: vir_low::Expression,
    // ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_field_address(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_address: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn encode_enum_variant_address(
        &mut self,
        base_type: &vir_mid::Type,
        variant: &vir_mid::ty::VariantIndex,
        base_address: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn encode_index_address(
        &mut self,
        base_type: &vir_mid::Type,
        base_address: vir_low::Expression,
        index: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> AddressesInterface for Lowerer<'p, 'v, 'tcx> {
    fn address_domain(&self) -> &'static str {
        ADDRESS_DOMAIN_NAME
    }
    fn address_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type(self.address_domain())
    }
    fn address_null(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let address_type = self.address_type()?;
        self.create_domain_func_app(
            ADDRESS_DOMAIN_NAME,
            "null_address$",
            Vec::new(),
            address_type,
            position,
        )
    }
    fn address_offset(
        &mut self,
        size: vir_low::Expression,
        address: vir_low::Expression,
        offset: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let address_type = self.address_type()?;
        if !self.address_state.is_address_offset_axiom_encoded {
            self.address_state.is_address_offset_axiom_encoded = true;
            use vir_low::macros::*;
            let size_type = self.size_type()?;
            var_decls! {
                address: Address,
                index: Int,
                size: {size_type}
            }
            let call = self.create_domain_func_app(
                ADDRESS_DOMAIN_NAME,
                "offset_address$",
                vec![
                    size.clone().into(),
                    address.clone().into(),
                    index.clone().into(),
                ],
                address_type.clone(),
                position,
            )?;
            let injective_call = self.create_domain_func_app(
                ADDRESS_DOMAIN_NAME,
                "offset_address$inverse",
                vec![address.clone().into(), call.clone()],
                vir_low::Type::Int,
                position,
            )?;
            let forall_body = expr! {
                [injective_call] == index
            };
            let body = vir_low::Expression::forall(
                vec![size, address, index],
                vec![vir_low::Trigger::new(vec![call])],
                forall_body,
            );
            let axiom = vir_low::DomainAxiomDecl::new(None, "offset_address$injective", body);
            self.declare_axiom(ADDRESS_DOMAIN_NAME, axiom)?;
        }
        self.create_domain_func_app(
            ADDRESS_DOMAIN_NAME,
            "offset_address$",
            vec![size, address, offset],
            address_type,
            position,
        )
    }
    fn root_address(
        &mut self,
        local: &vir_mid::expression::Local,
        old_label: &Option<String>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let address_variable =
            self.address_variable_version_at_label(&local.variable.name, old_label)?;
        Ok(vir_low::Expression::local(address_variable, local.position))
    }
    fn extract_root_address(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        unimplemented!("outdated code: {place}");
        // assert!(place.is_place());
        // let result = match place {
        //     vir_mid::Expression::Local(local) => self.root_address(local, &None)?,
        //     vir_mid::Expression::LabelledOld(_) => unimplemented!(),
        //     vir_mid::Expression::Deref(deref) => {
        //         // FIXME: Code duplication with PlaceAddressEncoder
        //         let mut place_encoder =
        //             PlaceToSnapshot::for_address(PredicateKind::Owned);
        //         let base_snapshot =
        //             place_encoder.expression_to_snapshot(self, &deref.base, false)?;
        //         // let base_snapshot = deref.base.to_procedure_snapshot(self)?;
        //         let ty = deref.base.get_type();
        //         if ty.is_reference() {
        //             self.reference_address(ty, base_snapshot, place.position())?
        //         } else {
        //             self.pointer_address(ty, base_snapshot, place.position())?
        //         }
        //     }
        //     _ => self.extract_root_address(place.get_parent_ref().unwrap())?,
        // };
        // Ok(result)
    }
    fn encode_expression_as_place_address(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut encoder = PlaceAddressEncoder::new_in_procedure();
        encoder.encode_expression(place, self)
    }
    // fn encode_expression_as_place_address_in_predicate(
    //     &mut self,
    //     place: &vir_mid::Expression,
    //     self_address: vir_low::Expression,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     let mut encoder = PlaceAddressEncoder::new_in_predicate(self_address);
    //     encoder.encode_expression(place, self)
    // }
    fn encode_field_address(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_address: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        self.encode_field_access_function_app(
            ADDRESS_DOMAIN_NAME,
            base_address,
            base_type,
            field,
            position,
        )
    }
    fn encode_enum_variant_address(
        &mut self,
        base_type: &vir_mid::Type,
        variant: &vir_mid::ty::VariantIndex,
        base_address: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        self.encode_variant_access_function_app(
            ADDRESS_DOMAIN_NAME,
            base_address,
            base_type,
            variant,
            position,
        )
    }
    fn encode_index_address(
        &mut self,
        base_type: &vir_mid::Type,
        base_address: vir_low::Expression,
        index: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        // FIXME: This implementation is most likely wrong. Test it properly.
        let vir_mid::Type::Pointer(pointer_type) = base_type else {
            unreachable!()
        };
        let size = self
            .encode_type_size_expression2(&pointer_type.target_type, &*pointer_type.target_type)?;
        let start_address = self.pointer_address(base_type, base_address, position)?;
        self.address_offset(size, start_address, index, position)
    }
}
