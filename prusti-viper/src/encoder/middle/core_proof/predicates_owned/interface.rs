use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        compute_address::ComputeAddressInterface,
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates_memory_block::PredicatesMemoryBlockInterface,
        snapshots::{IntoSnapshot, SnapshotsInterface},
        type_layouts::TypeLayoutsInterface,
    },
};
use rustc_hash::FxHashSet;
use std::borrow::Cow;
use vir_crate::{common::expression::ExpressionIterator, low as vir_low, middle as vir_mid};

#[derive(Default)]
pub(in super::super) struct PredicatesOwnedState {
    unfolded_owned_non_aliased_predicates: FxHashSet<vir_mid::Type>,
}

pub(in super::super) trait Private {
    fn encode_owned_non_aliased(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::PredicateDecl>;
    fn encode_owned_non_aliased_with_fields<'a>(
        &mut self,
        ty: &vir_mid::Type,
        snapshot: vir_low::VariableDecl,
        snapshot_type: vir_low::Type,
        validity: vir_low::Expression,
        fields: impl Iterator<Item = Cow<'a, vir_mid::FieldDecl>>,
    ) -> SpannedEncodingResult<vir_low::PredicateDecl>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn encode_owned_non_aliased(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::PredicateDecl> {
        self.encode_compute_address(ty)?;
        use vir_low::macros::*;
        let type_decl = self.encoder.get_type_decl_mid(ty)?;
        self.encode_snapshot_to_bytes_function(ty)?;
        let snapshot_type = ty.create_snapshot(self)?;
        var_decls! {
            place: Place,
            root_address: Address,
            snapshot: {snapshot_type.clone()}
        }
        let compute_address = ty!(Address);
        let to_bytes = ty! { Bytes };
        let validity = self.encode_snapshot_validity_expression(snapshot.clone().into(), ty)?;
        let size_of = self.encode_type_size_expression(ty)?;
        let compute_address = expr! { ComputeAddress::compute_address(place, root_address) };
        let bytes =
            self.encode_memory_block_bytes_expression(compute_address.clone(), size_of.clone())?;
        let predicate = match &type_decl {
            vir_mid::TypeDecl::Bool | vir_mid::TypeDecl::Int(_) | vir_mid::TypeDecl::Float(_) => {
                predicate! {
                    OwnedNonAliased<ty>(place: Place, root_address: Address, snapshot: {snapshot_type})
                    {(
                        ([validity]) &&
                        (acc(MemoryBlock([compute_address], [size_of]))) &&
                        (([bytes]) == (Snap<ty>::to_bytes(snapshot)))
                    )}
                }
            }
            // vir_mid::TypeDecl::TypeVar(TypeVar) => {},
            vir_mid::TypeDecl::Tuple(tuple_decl) => self.encode_owned_non_aliased_with_fields(
                ty,
                snapshot,
                snapshot_type,
                validity,
                tuple_decl.iter_fields(),
            )?,
            vir_mid::TypeDecl::Struct(struct_decl) => self.encode_owned_non_aliased_with_fields(
                ty,
                snapshot,
                snapshot_type,
                validity,
                struct_decl.iter_fields(),
            )?,
            // vir_mid::TypeDecl::Enum(Enum) => {},
            // vir_mid::TypeDecl::Array(Array) => {},
            // vir_mid::TypeDecl::Reference(Reference) => {},
            // vir_mid::TypeDecl::Never => {},
            // vir_mid::TypeDecl::Closure(Closure) => {},
            // vir_mid::TypeDecl::Unsupported(Unsupported) => {},
            x => unimplemented!("{}", x),
        };
        Ok(predicate)
    }
    #[allow(unused_parens)] // Our macros require to put parenthesis around, but currently there is no way of putting this inside the macro.
    fn encode_owned_non_aliased_with_fields<'a>(
        &mut self,
        ty: &vir_mid::Type,
        snapshot: vir_low::VariableDecl,
        snapshot_type: vir_low::Type,
        validity: vir_low::Expression,
        fields: impl Iterator<Item = Cow<'a, vir_mid::FieldDecl>>,
    ) -> SpannedEncodingResult<vir_low::PredicateDecl> {
        use vir_low::macros::*;
        var_decls! {
            place: Place,
            root_address: Address
        }
        let mut field_predicates = Vec::new();
        for field in fields {
            let field_place =
                self.encode_field_place(ty, &field, place.clone().into(), Default::default())?;
            let field_value = self.encode_field_snapshot(
                ty,
                &field,
                snapshot.clone().into(),
                Default::default(),
            )?;
            let acc = expr! {
                acc(OwnedNonAliased<(&field.ty)>(
                    [field_place], root_address, [field_value]
                ))
            };
            field_predicates.push(acc);
        }
        let predicate_decl = predicate! {
            OwnedNonAliased<ty>(place: Place, root_address: Address, snapshot: {snapshot_type})
            {(
                ([validity]) && ([field_predicates.into_iter().conjoin()])
            )}
        };
        Ok(predicate_decl)
    }
}

pub(in super::super) trait PredicatesOwnedInterface {
    /// Marks that `OwnedNonAliased<ty>` was unfolded in the program and we need
    /// to provide its body.
    fn mark_owned_non_aliased_as_unfolded(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    fn collect_owned_predicate_decls(
        &mut self,
    ) -> SpannedEncodingResult<Vec<vir_low::PredicateDecl>>;
}

impl<'p, 'v: 'p, 'tcx: 'v> PredicatesOwnedInterface for Lowerer<'p, 'v, 'tcx> {
    fn mark_owned_non_aliased_as_unfolded(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        if !self
            .predicates_owned_state
            .unfolded_owned_non_aliased_predicates
            .contains(ty)
        {
            self.encode_validity_axioms(ty)?;
            self.predicates_owned_state
                .unfolded_owned_non_aliased_predicates
                .insert(ty.clone());
        }
        Ok(())
    }
    fn collect_owned_predicate_decls(
        &mut self,
    ) -> SpannedEncodingResult<Vec<vir_low::PredicateDecl>> {
        let mut predicates = Vec::new();
        for ty in std::mem::take(
            &mut self
                .predicates_owned_state
                .unfolded_owned_non_aliased_predicates,
        ) {
            predicates.push(self.encode_owned_non_aliased(&ty)?);
        }
        Ok(predicates)
    }
}
