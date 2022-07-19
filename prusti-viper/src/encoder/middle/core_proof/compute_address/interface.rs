use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface, lowerer::Lowerer, places::PlacesInterface,
    },
};
use rustc_hash::FxHashSet;
use vir_crate::{common::identifier::WithIdentifier, low as vir_low, middle as vir_mid};

#[derive(Default)]
pub(in super::super) struct ComputeAddressState {
    pub(super) encoded_types: FxHashSet<vir_mid::Type>,
    pub(super) encoded_roots: FxHashSet<vir_low::Expression>,
    pub(super) axioms: Vec<vir_low::DomainAxiomDecl>,
}

impl ComputeAddressState {
    /// Construct the final domain.
    pub(in super::super) fn destruct(self) -> Option<vir_low::DomainDecl> {
        if self.encoded_types.is_empty() && self.encoded_roots.is_empty() {
            None
        } else {
            Some(vir_low::DomainDecl {
                name: "ComputeAddress".to_string(),
                functions: vec![vir_low::DomainFunctionDecl {
                    name: "compute_address".to_string(),
                    is_unique: false,
                    parameters: vir_low::macros::vars! {
                        place: Place,
                        address: Address
                    },
                    return_type: vir_low::macros::ty! { Address },
                }],
                axioms: self.axioms,
            })
        }
    }
}

trait Private {
    fn encode_compute_address_axiom_for_field(
        &mut self,
        ty: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<vir_low::DomainAxiomDecl>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn encode_compute_address_axiom_for_field(
        &mut self,
        ty: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<vir_low::DomainAxiomDecl> {
        use vir_low::macros::*;
        let compute_address = ty!(Address);
        let body = expr! {
            forall(
                place: Place, address: Address ::
                raw_code {
                    let field_place = self.encode_field_place(
                        ty,
                        field,
                        place.clone().into(),
                        Default::default()
                    )?;
                    let field_address = self.encode_field_address(
                        ty,
                        field,
                        expr! { ComputeAddress::compute_address(place, address) },
                        Default::default(),
                    )?;
                }
                [ { (ComputeAddress::compute_address([field_place.clone()], address)) } ]
                (ComputeAddress::compute_address([field_place], address)) == [field_address]
            )
        };
        Ok(vir_low::DomainAxiomDecl {
            name: format!(
                "{}${}$compute_address_axiom",
                ty.get_identifier(),
                field.name
            ),
            body,
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
        let ty_without_lifetime = ty.clone().erase_lifetimes();
        if !self
            .compute_address_state
            .encoded_types
            .contains(&ty_without_lifetime)
        {
            self.compute_address_state
                .encoded_types
                .insert(ty_without_lifetime);

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
                vir_mid::TypeDecl::Tuple(decl) => {
                    for field in decl.iter_fields() {
                        let axiom = self.encode_compute_address_axiom_for_field(ty, &field)?;
                        self.compute_address_state.axioms.push(axiom);
                        self.encode_compute_address(&field.ty)?;
                    }
                }
                vir_mid::TypeDecl::Struct(decl) => {
                    for field in &decl.fields {
                        let axiom = self.encode_compute_address_axiom_for_field(ty, field)?;
                        self.compute_address_state.axioms.push(axiom);
                        self.encode_compute_address(&field.ty)?;
                    }
                }
                vir_mid::TypeDecl::Enum(decl) => {
                    let discriminant_field = decl.discriminant_field();
                    let axiom =
                        self.encode_compute_address_axiom_for_field(ty, &discriminant_field)?;
                    self.compute_address_state.axioms.push(axiom);
                    self.encode_compute_address(&decl.discriminant_type)?;
                    for variant in &decl.variants {
                        use vir_low::macros::*;
                        let compute_address = ty!(Address);
                        let body = expr! {
                            forall(
                                place: Place, address: Address ::
                                raw_code {
                                    let variant_index = variant.name.clone().into();
                                    let variant_place = self.encode_enum_variant_place(
                                        ty,
                                        &variant_index,
                                        place.clone().into(),
                                        Default::default()
                                    )?;
                                    let variant_address = self.encode_enum_variant_address(
                                        ty,
                                        &variant_index,
                                        expr! { ComputeAddress::compute_address(place, address) },
                                        Default::default(),
                                    )?;
                                }
                                [ { (ComputeAddress::compute_address([variant_place.clone()], address)) } ]
                                (ComputeAddress::compute_address([variant_place], address)) == [variant_address]
                            )
                        };
                        let axiom = vir_low::DomainAxiomDecl {
                            name: format!(
                                "{}${}$compute_address_axiom",
                                ty.get_identifier(),
                                variant.name
                            ),
                            body,
                        };
                        self.compute_address_state.axioms.push(axiom);
                        let variant_ty = ty.clone().variant(variant.name.clone().into());
                        self.encode_compute_address(&variant_ty)?;
                    }
                }
                vir_mid::TypeDecl::Union(decl) => {
                    self.encode_compute_address(&decl.discriminant_type)?;
                    for variant in &decl.variants {
                        use vir_low::macros::*;
                        let compute_address = ty!(Address);
                        let body = expr! {
                            forall(
                                place: Place, address: Address ::
                                raw_code {
                                    let variant_index = variant.name.clone().into();
                                    let variant_place = self.encode_enum_variant_place(
                                        ty,
                                        &variant_index,
                                        place.clone().into(),
                                        Default::default()
                                    )?;
                                    let variant_address = self.encode_enum_variant_address(
                                        ty,
                                        &variant_index,
                                        expr! { ComputeAddress::compute_address(place, address) },
                                        Default::default(),
                                    )?;
                                }
                                [ { (ComputeAddress::compute_address([variant_place.clone()], address)) } ]
                                (ComputeAddress::compute_address([variant_place], address)) == [variant_address]
                            )
                        };
                        let axiom = vir_low::DomainAxiomDecl {
                            name: format!(
                                "{}${}$compute_address_axiom",
                                ty.get_identifier(),
                                variant.name
                            ),
                            body,
                        };
                        self.compute_address_state.axioms.push(axiom);
                        let variant_ty = ty.clone().variant(variant.name.clone().into());
                        self.encode_compute_address(&variant_ty)?;
                    }
                }
                vir_mid::TypeDecl::Array(_decl) => {
                    // FIXME: Doing nothing is probably wrong.
                }
                vir_mid::TypeDecl::Reference(_reference) => {
                    // Do nothing
                }
                // vir_mid::TypeDecl::Never => {},
                // vir_mid::TypeDecl::Closure(Closure) => {},
                // vir_mid::TypeDecl::Unsupported(Unsupported) => {},
                x => unimplemented!("{:?}", x),
            }
        }
        Ok(())
    }
    fn encode_compute_address_for_place_root(
        &mut self,
        place_root: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        if self
            .compute_address_state
            .encoded_roots
            .contains(place_root)
        {
            return Ok(());
        }
        self.compute_address_state
            .encoded_roots
            .insert(place_root.clone());
        use vir_low::macros::*;
        let compute_address = ty! { Address };
        let body = expr! {
            forall(
                address: Address ::
                [ { (ComputeAddress::compute_address([place_root.clone()], address)) } ]
                (ComputeAddress::compute_address([place_root.clone()], address)) == address
            )
        };
        let axiom = vir_low::DomainAxiomDecl {
            name: format!(
                "root${}$compute_address_axiom",
                self.compute_address_state.encoded_roots.len()
            ),
            body,
        };
        self.compute_address_state.axioms.push(axiom);
        Ok(())
    }
}
