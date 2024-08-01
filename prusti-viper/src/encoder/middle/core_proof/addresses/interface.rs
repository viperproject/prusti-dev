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
        builtin_constants::{ADDRESS_DOMAIN_NAME, ALLOCATION_DOMAIN_NAME},
        expression::{BinaryOperationHelpers, QuantifierHelpers},
        position::Positioned,
    },
    low as vir_low,
    middle::{self as vir_mid},
};

pub(in super::super) trait AddressesInterface {
    fn address_domain(&self) -> &'static str;
    fn allocation_domain(&self) -> &'static str;
    fn address_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn allocation_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
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
    fn offset_from_address(
        &mut self,
        size: vir_low::Expression,
        address: vir_low::Expression,
        from_address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn index_into_allocation(
        &mut self,
        size: vir_low::Expression,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn address_allocation(
        &mut self,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn fresh_allocation(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn address_range_contains(
        &mut self,
        base_address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        element_size: vir_low::Expression,
        checked_address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn pointer_range_contains(
        &mut self,
        base_address: vir_low::Expression,
        element_size: vir_low::Expression,
        range_length: vir_low::Expression,
        checked_address: vir_low::Expression,
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

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
    fn encode_address_axioms(&mut self) -> SpannedEncodingResult<()> {
        if !self.address_state.are_address_axioms_encoded {
            self.address_state.are_address_axioms_encoded = true;
            use vir_low::macros::*;
            let size_type = self.size_type()?;
            let address_type = self.address_type()?;
            let allocation_type = self.allocation_type()?;
            var_decls! {
                allocation: Allocation,
                address: Address,
                index: Int,
                element_size: {size_type}
            }
            let position = vir_low::Position::default();
            {
                // Address constructor is injective with respect to allocation
                // and index. Both inverse functions are total, which is
                // important for the performance.
                {
                    // ```
                    // forall allocation, index, element_size ::
                    //   {address_constructor(allocation, index, element_size)}
                    //   get_allocation(address_constructor(allocation, index, element_size)) == allocation &&
                    //   get_index(address_constructor(allocation, index, element_size), element_size) == index
                    // ```
                    let address_constructor = self.create_domain_func_app(
                        ADDRESS_DOMAIN_NAME,
                        "address_constructor$",
                        vec![
                            allocation.clone().into(),
                            index.clone().into(),
                            element_size.clone().into(),
                        ],
                        address_type.clone(),
                        position,
                    )?;
                    let get_allocation = self.create_domain_func_app(
                        ADDRESS_DOMAIN_NAME,
                        "get_allocation$",
                        vec![address_constructor.clone()],
                        allocation_type.clone(),
                        position,
                    )?;
                    let get_index = self.create_domain_func_app(
                        ADDRESS_DOMAIN_NAME,
                        "get_index$",
                        vec![address_constructor.clone(), element_size.clone().into()],
                        vir_low::Type::Int,
                        position,
                    )?;
                    let body = vir_low::Expression::forall(
                        vec![allocation.clone(), index.clone(), element_size.clone()],
                        vec![vir_low::Trigger::new(vec![address_constructor])],
                        expr! { ([get_allocation] == allocation) && ([get_index] == index) },
                    );
                    let axiom = vir_low::DomainAxiomDecl::new(
                        None,
                        "address_constructor$injectivity1",
                        body,
                    );
                    self.declare_axiom(ADDRESS_DOMAIN_NAME, axiom)?;
                }
                {
                    // ```
                    // forall address, element_size ::
                    //   {address_constructor(get_allocation(address), get_index(address, element_size), element_size)}
                    //   address_constructor(get_allocation(address), get_index(address, element_size), element_size) == address
                    // ```
                    let get_allocation = self.create_domain_func_app(
                        ADDRESS_DOMAIN_NAME,
                        "get_allocation$",
                        vec![address.clone().into()],
                        allocation_type.clone(),
                        position,
                    )?;
                    let get_index = self.create_domain_func_app(
                        ADDRESS_DOMAIN_NAME,
                        "get_index$",
                        vec![address.clone().into(), element_size.clone().into()],
                        vir_low::Type::Int,
                        position,
                    )?;
                    let address_constructor = self.create_domain_func_app(
                        ADDRESS_DOMAIN_NAME,
                        "address_constructor$",
                        vec![
                            get_allocation,
                            index.clone().into(),
                            element_size.clone().into(),
                        ],
                        address_type.clone(),
                        position,
                    )?;
                    let body = vir_low::Expression::forall(
                        vec![address.clone(), index.clone(), element_size.clone()],
                        vec![vir_low::Trigger::new(vec![address_constructor.clone()])],
                        expr! { ([get_index] == index) ==> ([address_constructor] == address) },
                    );
                    let axiom = vir_low::DomainAxiomDecl::new(
                        None,
                        "address_constructor$injectivity2",
                        body,
                    );
                    self.declare_axiom(ADDRESS_DOMAIN_NAME, axiom)?;
                }
            }
            {
                // Define range_contains function, which is used for defining
                // quantified permissions.
                // ```
                // forall base_address, start_index, end_index, element_size, checked_address ::
                // {address_range_contains(base_address, start_index, end_index, element_size, checked_address)}
                //  address_range_contains(base_address, start_index, end_index, element_size, checked_address) ==
                // (get_allocation(base_address) == get_allocation(checked_address) &&
                // get_index(base_address, element_size) + start_index <= get_index(checked_address, element_size)) &&
                // get_index(checked_address, element_size)) < get_index(base_address, element_size) + end_index
                // )
                // ```
                var_decls! {
                    base_address: Address,
                    start_index: Int,
                    end_index: Int,
                    checked_address: Address
                }
                let address_range_contains = self.create_domain_func_app(
                    ADDRESS_DOMAIN_NAME,
                    "address_range_contains$",
                    vec![
                        base_address.clone().into(),
                        start_index.clone().into(),
                        end_index.clone().into(),
                        element_size.clone().into(),
                        checked_address.clone().into(),
                    ],
                    vir_low::Type::Bool,
                    position,
                )?;
                let get_allocation_base_address = self.create_domain_func_app(
                    ADDRESS_DOMAIN_NAME,
                    "get_allocation$",
                    vec![base_address.clone().into()],
                    allocation_type.clone(),
                    position,
                )?;
                let get_allocation_checked_address = self.create_domain_func_app(
                    ADDRESS_DOMAIN_NAME,
                    "get_allocation$",
                    vec![checked_address.clone().into()],
                    allocation_type.clone(),
                    position,
                )?;
                let get_index_base_address = self.create_domain_func_app(
                    ADDRESS_DOMAIN_NAME,
                    "get_index$",
                    vec![base_address.clone().into(), element_size.clone().into()],
                    vir_low::Type::Int,
                    position,
                )?;
                let get_index_checked_address = self.create_domain_func_app(
                    ADDRESS_DOMAIN_NAME,
                    "get_index$",
                    vec![checked_address.clone().into(), element_size.clone().into()],
                    vir_low::Type::Int,
                    position,
                )?;
                let definition = expr! {
                    (([get_allocation_base_address] == [get_allocation_checked_address]) &&
                    (([get_index_base_address.clone()] + start_index) <= [get_index_checked_address.clone()])) &&
                    ([get_index_checked_address] < ([get_index_base_address] + end_index))
                };
                let body = vir_low::Expression::forall(
                    vec![
                        base_address,
                        start_index,
                        end_index,
                        element_size.clone(),
                        checked_address,
                    ],
                    vec![vir_low::Trigger::new(vec![address_range_contains.clone()])],
                    expr! { [address_range_contains] == [definition] },
                );
                let axiom =
                    vir_low::DomainAxiomDecl::new(None, "address_range_contains$definition", body);
                self.declare_axiom(ADDRESS_DOMAIN_NAME, axiom)?;
            }
            {
                // Define `offset_address` function, which is used for computing
                // new addresses by offsetting them.
                // ```
                // forall address, offset, element_size ::
                // {offset_address(address, offset, element_size)}
                // offset_address(address, offset, element_size) ==
                // address_constructor(get_allocation(address), get_index(address, element_size) + offset, element_size)
                // ```
                var_decls! {
                    offset: Int
                }
                let offset_address = self.create_domain_func_app(
                    ADDRESS_DOMAIN_NAME,
                    "offset_address$",
                    vec![
                        address.clone().into(),
                        offset.clone().into(),
                        element_size.clone().into(),
                    ],
                    address_type.clone(),
                    position,
                )?;
                let get_allocation = self.create_domain_func_app(
                    ADDRESS_DOMAIN_NAME,
                    "get_allocation$",
                    vec![address.clone().into()],
                    allocation_type,
                    position,
                )?;
                let get_index = self.create_domain_func_app(
                    ADDRESS_DOMAIN_NAME,
                    "get_index$",
                    vec![address.clone().into(), element_size.clone().into()],
                    vir_low::Type::Int,
                    position,
                )?;
                let definition = self.create_domain_func_app(
                    ADDRESS_DOMAIN_NAME,
                    "address_constructor$",
                    vec![
                        get_allocation,
                        vir_low::Expression::add(get_index, offset.clone().into()),
                        element_size.clone().into(),
                    ],
                    address_type,
                    position,
                )?;
                let body = vir_low::Expression::forall(
                    vec![address, offset, element_size],
                    vec![vir_low::Trigger::new(vec![offset_address.clone()])],
                    expr! { [offset_address] == [definition] },
                );
                let axiom = vir_low::DomainAxiomDecl::new(None, "offset_address$definition", body);
                self.declare_axiom(ADDRESS_DOMAIN_NAME, axiom)?;
            }
        }
        Ok(())
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> AddressesInterface for Lowerer<'p, 'v, 'tcx> {
    fn address_domain(&self) -> &'static str {
        ADDRESS_DOMAIN_NAME
    }
    fn allocation_domain(&self) -> &'static str {
        ALLOCATION_DOMAIN_NAME
    }
    fn address_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type(self.address_domain())
    }
    fn allocation_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type(self.allocation_domain())
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
        self.encode_address_axioms()?;
        self.create_domain_func_app(
            ADDRESS_DOMAIN_NAME,
            "offset_address$",
            vec![address, offset, size],
            address_type,
            position,
        )
    }
    fn offset_from_address(
        &mut self,
        size: vir_low::Expression,
        address: vir_low::Expression,
        from_address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_address_axioms()?;
        let index1 = self.index_into_allocation(size.clone(), address, position)?;
        let index2 = self.index_into_allocation(size, from_address, position)?;
        let offset = vir_low::Expression::subtract(index1, index2);
        Ok(offset)
    }
    fn index_into_allocation(
        &mut self,
        size: vir_low::Expression,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_address_axioms()?;
        self.create_domain_func_app(
            ADDRESS_DOMAIN_NAME,
            "get_index$",
            vec![address, size],
            vir_low::Type::Int,
            position,
        )
    }
    fn address_allocation(
        &mut self,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_address_axioms()?;
        let allocation_type = self.allocation_type()?;
        self.create_domain_func_app(
            ADDRESS_DOMAIN_NAME,
            "get_allocation$",
            vec![address],
            allocation_type,
            position,
        )
    }
    fn fresh_allocation(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_address_axioms()?;
        let allocation_type = self.allocation_type()?;
        self.address_state.fresh_allocation_counter += 1;
        self.create_domain_func_app(
            ADDRESS_DOMAIN_NAME,
            "fresh_allocation$",
            vec![self.address_state.fresh_allocation_counter.into()],
            allocation_type,
            position,
        )
    }
    fn address_range_contains(
        &mut self,
        base_address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        element_size: vir_low::Expression,
        checked_address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_address_axioms()?;
        self.create_domain_func_app(
            ADDRESS_DOMAIN_NAME,
            "address_range_contains$",
            vec![
                base_address,
                start_index,
                end_index,
                element_size,
                checked_address,
            ],
            vir_low::Type::Bool,
            position,
        )
    }
    fn pointer_range_contains(
        &mut self,
        base_address: vir_low::Expression,
        element_size: vir_low::Expression,
        range_length: vir_low::Expression,
        checked_address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // let start_index = self.create_domain_func_app(
        //     ADDRESS_DOMAIN_NAME,
        //     "get_index$",
        //     vec![base_address.clone(), element_size.clone()],
        //     vir_low::Type::Int,
        //     position,
        // )?;
        // let end_index = vir_low::Expression::add(start_index.clone(), range_length);
        let start_index = 0.into();
        let end_index = range_length;
        self.address_range_contains(
            base_address,
            start_index,
            end_index,
            element_size,
            checked_address,
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
