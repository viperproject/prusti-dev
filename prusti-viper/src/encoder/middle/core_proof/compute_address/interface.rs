use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{addresses::AddressesInterface, lowerer::Lowerer},
};
use rustc_hash::FxHashSet;
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle as vir_mid,
};

#[derive(Default)]
pub(in super::super) struct ComputeAddressState {
    pub(super) encoded_types: FxHashSet<String>,
    pub(super) encoded_roots: FxHashSet<vir_low::Expression>,
    pub(super) rewrite_rules: Vec<vir_low::DomainRewriteRuleDecl>,
}

impl ComputeAddressState {
    /// Construct the final domain.
    pub(in super::super) fn destruct(self) -> Option<vir_low::DomainDecl> {
        // None
        if self.encoded_types.is_empty() && self.encoded_roots.is_empty() {
            None
        } else {
            Some(vir_low::DomainDecl {
                name: "ComputeAddress".to_string(),
                functions: vec![
                    // vir_low::DomainFunctionDecl {
                    //     name: "compute_address".to_string(),
                    //     is_unique: false,
                    //     parameters: vir_low::macros::vars! {
                    //         place: PlaceOption,
                    //         address: Address
                    //     },
                    //     return_type: vir_low::macros::ty! { Address },
                    // },
                    vir_low::DomainFunctionDecl {
                        name: "address_is_non_aliased".to_string(),
                        is_unique: false,
                        parameters: vir_low::macros::vars! {
                            address: Address
                        },
                        return_type: vir_low::Type::Bool,
                    },
                ],
                axioms: Vec::new(),
                rewrite_rules: self.rewrite_rules,
            })
        }
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
    //     fn encode_compute_address_axiom_for_field(
    //         &mut self,
    //         ty: &vir_mid::Type,
    //         field: &vir_mid::FieldDecl,
    //     ) -> SpannedEncodingResult<vir_low::DomainRewriteRuleDecl> {
    //         use vir_low::macros::*;
    //         let compute_address = ty!(Address);
    //         var_decls! {
    //             place: Place,
    //             address: Address
    //         };
    //         let place_option = self.place_option_some_constructor(place.clone().into())?;
    //         let field_place =
    //             self.encode_field_place(ty, field, place_option.clone(), Default::default())?;
    //         let field_address = self.encode_field_address(
    //             ty,
    //             field,
    //             expr! { ComputeAddress::compute_address([place_option], address) },
    //             Default::default(),
    //         )?;
    //         let source = expr! { (ComputeAddress::compute_address([field_place], address)) };
    //         Ok(vir_low::DomainRewriteRuleDecl {
    //             comment: None,
    //             name: format!(
    //                 "{}${}$compute_address_axiom",
    //                 ty.get_identifier(),
    //                 field.name
    //             ),
    //             egg_only: false,
    //             variables: vec![place, address],
    //             triggers: None,
    //             source,
    //             target: field_address,
    //         })
    //     }

    fn encode_propagate_address_non_aliased_axiom_for_field(
        &mut self,
        ty: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<vir_low::DomainRewriteRuleDecl> {
        use vir_low::macros::*;
        let address_is_non_aliased = ty!(Bool);
        var_decls! {
            address: Address
        };
        let field_address =
            self.encode_field_address(ty, field, address.clone().into(), Default::default())?;
        let source = expr! { (ComputeAddress::address_is_non_aliased([field_address])) };
        let target = expr! { (ComputeAddress::address_is_non_aliased(address)) };
        Ok(vir_low::DomainRewriteRuleDecl {
            comment: None,
            name: format!(
                "{}${}$address_is_non_aliased_axiom",
                ty.get_identifier(),
                field.name
            ),
            egg_only: true,
            variables: vec![address],
            triggers: None,
            source,
            target,
        })
    }
}

pub(in super::super) trait ComputeAddressInterface {
    fn encode_compute_address(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_compute_address_for_place_root(
        &mut self,
        place_root: &vir_low::Expression,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> ComputeAddressInterface for Lowerer<'p, 'v, 'tcx> {
    fn encode_compute_address(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .compute_address_state
            .encoded_types
            .contains(&ty_identifier)
        {
            self.compute_address_state
                .encoded_types
                .insert(ty_identifier);

            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            match type_decl {
                vir_mid::TypeDecl::Bool
                | vir_mid::TypeDecl::Int(_)
                | vir_mid::TypeDecl::Float(_)
                | vir_mid::TypeDecl::Pointer(_)
                | vir_mid::TypeDecl::Trusted(_)
                | vir_mid::TypeDecl::TypeVar(_)
                | vir_mid::TypeDecl::Sequence(_)
                | vir_mid::TypeDecl::Map(_) => {
                    // Nothing to do.
                }
                vir_mid::TypeDecl::Struct(decl) => {
                    for field in &decl.fields {
                        // let axiom = self.encode_compute_address_axiom_for_field(ty, field)?;
                        // self.compute_address_state.rewrite_rules.push(axiom);
                        let axiom =
                            self.encode_propagate_address_non_aliased_axiom_for_field(ty, field)?;
                        self.compute_address_state.rewrite_rules.push(axiom);
                        self.encode_compute_address(&field.ty)?;
                    }
                }
                vir_mid::TypeDecl::Enum(decl) => {
                    // FIXME: Encode address_is_non_aliased axioms for enum variants.
                    if decl.safety.is_enum() {
                        let discriminant_field = decl.discriminant_field();
                        // let axiom =
                        //     self.encode_compute_address_axiom_for_field(ty, &discriminant_field)?;
                        // self.compute_address_state.rewrite_rules.push(axiom);
                        let axiom = self.encode_propagate_address_non_aliased_axiom_for_field(
                            ty,
                            &discriminant_field,
                        )?;
                        self.compute_address_state.rewrite_rules.push(axiom);
                    }
                    self.encode_compute_address(&decl.discriminant_type)?;
                    for variant in &decl.variants {
                        use vir_low::macros::*;
                        let address_is_non_aliased = ty!(Bool);
                        var_decls! {
                            address: Address
                        }
                        let variant_index = variant.name.clone().into();
                        let variant_address = self.encode_enum_variant_address(
                            ty,
                            &variant_index,
                            address.clone().into(),
                            Default::default(),
                        )?;
                        let source = expr! {
                            (ComputeAddress::address_is_non_aliased([variant_address]))
                        };
                        let target = expr! {
                            (ComputeAddress::address_is_non_aliased(address))
                        };
                        let axiom = vir_low::DomainRewriteRuleDecl {
                            comment: None,
                            name: format!(
                                "{}${}$compute_address_axiom",
                                ty.get_identifier(),
                                variant.name
                            ),
                            egg_only: true,
                            variables: vec![address],
                            triggers: None,
                            source,
                            target,
                        };
                        self.compute_address_state.rewrite_rules.push(axiom);
                        let variant_ty = ty.clone().variant(variant.name.clone().into());
                        self.encode_compute_address(&variant_ty)?;
                        // self.encode_compute_address(&decl.discriminant_type)?;
                        // for variant in &decl.variants {
                        //     use vir_low::macros::*;
                        //     let compute_address = ty!(Address);
                        //     var_decls! {
                        //         place: Place,
                        //         address: Address
                        //     }
                        //     let variant_index = variant.name.clone().into();
                        //     let variant_place = self.encode_enum_variant_place(
                        //         ty,
                        //         &variant_index,
                        //         place.clone().into(),
                        //         Default::default(),
                        //     )?;
                        //     let variant_address = self.encode_enum_variant_address(
                        //         ty,
                        //         &variant_index,
                        //         expr! { ComputeAddress::compute_address(place, address) },
                        //         Default::default(),
                        //     )?;
                        //     let source = expr! {
                        //         (ComputeAddress::compute_address([variant_place], address))
                        //     };
                        //     let axiom = vir_low::DomainRewriteRuleDecl {
                        //         comment: None,
                        //         name: format!(
                        //             "{}${}$compute_address_axiom",
                        //             ty.get_identifier(),
                        //             variant.name
                        //         ),
                        //         egg_only: false,
                        //         variables: vec![place, address],
                        //         triggers: None,
                        //         source,
                        //         target: variant_address,
                        //     };
                        //     self.compute_address_state.rewrite_rules.push(axiom);
                        //     let variant_ty = ty.clone().variant(variant.name.clone().into());
                        //     self.encode_compute_address(&variant_ty)?;
                    }
                }
                vir_mid::TypeDecl::Array(_decl) => {
                    // FIXME: Doing nothing is probably wrong.
                }
                vir_mid::TypeDecl::Reference(_reference) => {
                    // use vir_low::macros::*;
                    // let compute_address = ty!(Address);
                    // let _body = expr! {
                    //     forall(
                    //         place: Place, snapshot: {ty.to_snapshot(self)?} ::
                    //         raw_code {
                    //             let position = vir_low::Position::default();
                    //             let deref_place = self.reference_deref_place(
                    //                 place.clone().into(), position)?;
                    //             let address = self.reference_address(
                    //                 ty,
                    //                 snapshot.clone().into(),
                    //                 position,
                    //             )?;
                    //         }
                    //         [ { (ComputeAddress::compute_address(
                    //             [deref_place.clone()], [address.clone()])) } ]
                    //         (ComputeAddress::compute_address(
                    //             [deref_place], [address.clone()])) == [address]
                    //     )
                    // };
                    // var_decls! {
                    //     place: Place,
                    //     snapshot: {ty.to_snapshot(self)?}
                    // }
                    // let position = vir_low::Position::default();
                    // let deref_place = self.reference_deref_place(place.clone().into(), position)?;
                    // let address = self.reference_address(ty, snapshot.clone().into(), position)?;
                    // let source = expr! {
                    //     (ComputeAddress::compute_address(
                    //         [deref_place], [address.clone()]))
                    // };
                    // let axiom = vir_low::DomainRewriteRuleDecl {
                    //     comment: None,
                    //     name: format!("{}$compute_address_axiom", ty.get_identifier(),),
                    //     egg_only: false,
                    //     variables: vec![place, snapshot],
                    //     triggers: None,
                    //     source,
                    //     target: address,
                    // };
                    // self.compute_address_state.rewrite_rules.push(axiom);
                }
                // vir_mid::TypeDecl::Closure(Closure) => {},
                // vir_mid::TypeDecl::Unsupported(Unsupported) => {},
                x => unimplemented!("{:?}", x),
            }
        }
        Ok(())
    }
    fn encode_compute_address_for_place_root(
        &mut self,
        _place_root: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        // debug_assert_eq!(place_root.get_type(), &self.place_type()?);
        // if self
        //     .compute_address_state
        //     .encoded_roots
        //     .contains(place_root)
        // {
        //     return Ok(());
        // }
        // self.compute_address_state
        //     .encoded_roots
        //     .insert(place_root.clone());
        // use vir_low::macros::*;
        // let compute_address = ty! { Address };
        // var_decls! {
        //     address: Address
        // }
        // let place_option_root = self.place_option_some_constructor(place_root.clone())?;
        // let source = expr! { (ComputeAddress::compute_address([place_option_root], address)) };
        // let axiom = vir_low::DomainRewriteRuleDecl {
        //     comment: None,
        //     name: format!(
        //         "root${}$compute_address_axiom",
        //         self.compute_address_state.encoded_roots.len()
        //     ),
        //     egg_only: false,
        //     variables: vec![address.clone()],
        //     triggers: None,
        //     source,
        //     target: address.into(),
        // };
        // self.compute_address_state.rewrite_rules.push(axiom);
        Ok(())
    }
}
