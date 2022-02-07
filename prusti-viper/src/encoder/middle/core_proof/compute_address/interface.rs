use super::encoder::ComputeAddressEncoder;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{lowerer::Lowerer, utils::type_decl_encoder::TypeDeclWalker},
};
use rustc_hash::FxHashSet;

use vir_crate::{low as vir_low, middle as vir_mid};

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

pub(in super::super) trait ComputeAddressInterface {
    fn encode_compute_address(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_compute_address_for_place_root(
        &mut self,
        place_root: &vir_low::Expression,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> ComputeAddressInterface for Lowerer<'p, 'v, 'tcx> {
    fn encode_compute_address(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let mut encoder = ComputeAddressEncoder;
        encoder.walk_type(ty, (), self)
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
                "compute_address_axiom${}",
                self.compute_address_state.encoded_roots.len()
            ),
            body,
        };
        self.compute_address_state.axioms.push(axiom);
        Ok(())
    }
}
