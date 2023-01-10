use std::collections::BTreeMap;

use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        compute_address::ComputeAddressInterface,
        lowerer::{FunctionsLowererInterface, Lowerer},
        places::PlacesInterface,
        predicates::{
            owned::builders::{
                FracRefBuilder, OwnedNonAliasedBuilder, PredicateDeclBuilderMethods,
                UniqueRefBuilder,
            },
            PredicatesMemoryBlockInterface,
        },
        snapshots::SnapshotBytesInterface,
        types::TypesInterface,
    },
};
use prusti_common::config;
use rustc_hash::FxHashSet;
use vir_crate::{
    common::{
        expression::{ExpressionIterator, GuardedExpressionIterator},
        identifier::WithIdentifier,
    },
    low::{self as vir_low},
    middle as vir_mid,
};

use super::builders::{
    FracRefSnapFunctionBuilder, OwnedAliasedBuilder, OwnedAliasedSnapFunctionBuilder,
    OwnedNonAliasedSnapFunctionBuilder, UniqueRefSnapFunctionBuilder,
};

pub(super) struct PredicateEncoder<'l, 'p, 'v, 'tcx> {
    lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
    encoded_owned_non_aliased_predicates: FxHashSet<String>,
    encoded_owned_aliased_predicates: FxHashSet<String>,
    encoded_mut_borrow_predicates: FxHashSet<String>,
    encoded_frac_borrow_predicates: FxHashSet<String>,
    predicates: Vec<vir_low::PredicateDecl>,
    /// A map from predicate names to snapshot function names and snapshot types.
    predicate_info: BTreeMap<String, (String, vir_low::Type)>,
}

impl<'l, 'p, 'v, 'tcx> PredicateEncoder<'l, 'p, 'v, 'tcx> {
    pub(super) fn new(lowerer: &'l mut Lowerer<'p, 'v, 'tcx>) -> Self {
        Self {
            lowerer,
            encoded_owned_non_aliased_predicates: Default::default(),
            encoded_owned_aliased_predicates: Default::default(),
            encoded_mut_borrow_predicates: Default::default(),
            encoded_frac_borrow_predicates: Default::default(),
            predicates: Default::default(),
            predicate_info: Default::default(),
        }
    }

    pub(super) fn into_predicates(self) -> Vec<vir_low::PredicateDecl> {
        self.predicates
    }

    pub(super) fn take_predicate_info(&mut self) -> BTreeMap<String, (String, vir_low::Type)> {
        std::mem::take(&mut self.predicate_info)
    }

    pub(super) fn encode_owned_non_aliased_snapshot(
        &mut self,
        normalized_type: &vir_mid::Type,
        type_decl: &vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<(String, vir_low::Type)> {
        let mut builder =
            OwnedNonAliasedSnapFunctionBuilder::new(self.lowerer, normalized_type, type_decl)?;
        builder.create_parameters()?;
        builder.add_owned_precondition()?;
        builder.add_validity_postcondition()?;
        match type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Map(_) => {
                builder.add_bytes_snapshot_equality()?;
            }
            vir_mid::TypeDecl::Trusted(_) | vir_mid::TypeDecl::TypeVar(_) => {}
            vir_mid::TypeDecl::Struct(decl) => {
                let mut equalities = Vec::new();
                for field in &decl.fields {
                    equalities.push(builder.create_field_snapshot_equality(field)?);
                }
                builder.add_unfolding_postcondition(equalities.into_iter().conjoin())?;
                builder.add_structural_invariant(decl)?;
            }
            vir_mid::TypeDecl::Enum(decl) => {
                let mut equalities = Vec::new();
                if decl.safety.is_enum() {
                    let discriminant_equality =
                        builder.create_discriminant_snapshot_equality(decl)?;
                    builder.add_unfolding_postcondition(discriminant_equality)?;
                }
                for (discriminant, variant) in decl.iter_discriminant_variants() {
                    equalities
                        .push(builder.create_variant_snapshot_equality(discriminant, variant)?);
                }
                builder.add_unfolding_postcondition(equalities.into_iter().create_match())?;
            }
            vir_mid::TypeDecl::Reference(decl) => {
                builder.add_bytes_address_snapshot_equality()?;
                // FIXME: Have a getter for the first lifetime.
                let lifetime = &decl.lifetimes[0];
                builder.add_reference_snapshot_equalities(decl, lifetime)?;
            }
            vir_mid::TypeDecl::Array(decl) => {
                let length = if normalized_type.is_slice() {
                    builder.get_slice_len()?
                } else {
                    decl.const_parameters[0].clone()
                };
                builder.add_snapshot_len_equal_to_postcondition(&length)?;
                builder.add_quantifiers(&length, &decl.element_type)?;
            }
            _ => {
                unimplemented!("{}", type_decl);
            }
        }
        let function = builder.build()?;
        let function_name = function.name.clone();
        let snapshot_type = function.return_type.clone();
        self.lowerer.declare_function(function)?;
        Ok((function_name, snapshot_type))
    }

    pub(super) fn encode_owned_aliased_snapshot(
        &mut self,
        normalized_type: &vir_mid::Type,
        type_decl: &vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<()> {
        let mut builder =
            OwnedAliasedSnapFunctionBuilder::new(self.lowerer, normalized_type, type_decl)?;
        builder.create_parameters()?;
        builder.add_owned_precondition()?;
        builder.add_validity_postcondition()?;
        match type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Map(_) => {
                builder.add_bytes_snapshot_equality()?;
            }
            vir_mid::TypeDecl::Trusted(_) | vir_mid::TypeDecl::TypeVar(_) => {}
            vir_mid::TypeDecl::Struct(decl) => {
                let mut equalities = Vec::new();
                for field in &decl.fields {
                    equalities.push(builder.create_field_snapshot_equality(field)?);
                }
                builder.add_unfolding_postcondition(equalities.into_iter().conjoin())?;
                builder.add_structural_invariant(decl)?;
            }
            vir_mid::TypeDecl::Enum(decl) => {
                let mut equalities = Vec::new();
                if decl.safety.is_enum() {
                    let discriminant_equality =
                        builder.create_discriminant_snapshot_equality(decl)?;
                    builder.add_unfolding_postcondition(discriminant_equality)?;
                }
                for (discriminant, variant) in decl.iter_discriminant_variants() {
                    equalities
                        .push(builder.create_variant_snapshot_equality(discriminant, variant)?);
                }
                builder.add_unfolding_postcondition(equalities.into_iter().create_match())?;
            }
            vir_mid::TypeDecl::Reference(decl) => {
                builder.add_bytes_address_snapshot_equality()?;
                // FIXME: Have a getter for the first lifetime.
                let lifetime = &decl.lifetimes[0];
                builder.add_reference_snapshot_equalities(decl, lifetime)?;
            }
            vir_mid::TypeDecl::Array(decl) => {
                let length = if normalized_type.is_slice() {
                    builder.get_slice_len()?
                } else {
                    decl.const_parameters[0].clone()
                };
                builder.add_snapshot_len_equal_to_postcondition(&length)?;
                builder.add_quantifiers(&length, &decl.element_type)?;
            }
            _ => {
                unimplemented!("{}", type_decl);
            }
        }
        let function = builder.build()?;
        self.lowerer.declare_function(function)?;
        Ok(())
    }

    pub(super) fn encode_unique_ref_current_snapshot(
        &mut self,
        normalized_type: &vir_mid::Type,
        type_decl: &vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<()> {
        let mut builder =
            UniqueRefSnapFunctionBuilder::new(self.lowerer, normalized_type, type_decl, false)?;
        builder.create_parameters()?;
        builder.add_unique_ref_precondition()?;
        match &type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Map(_) => {
                // For these types the unique ref predicate is abstract.
            }
            vir_mid::TypeDecl::Trusted(_) | vir_mid::TypeDecl::TypeVar(_) => {}
            vir_mid::TypeDecl::Struct(decl) => {
                let mut equalities = Vec::new();
                for field in &decl.fields {
                    equalities.push(builder.create_field_snapshot_equality(field)?);
                }
                builder.add_unfolding_postcondition(equalities.into_iter().conjoin())?;
                builder.add_structural_invariant(decl)?;
            }
            vir_mid::TypeDecl::Enum(_decl) => {}
            vir_mid::TypeDecl::Reference(_decl) => {}
            vir_mid::TypeDecl::Array(_decl) => {}
            _ => {
                unimplemented!("{}", type_decl);
            }
        }
        let function = builder.build()?;
        self.lowerer.declare_function(function)?;
        Ok(())
    }

    pub(super) fn encode_unique_ref_final_snapshot(
        &mut self,
        normalized_type: &vir_mid::Type,
        type_decl: &vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<()> {
        let mut builder =
            UniqueRefSnapFunctionBuilder::new(self.lowerer, normalized_type, type_decl, true)?;
        builder.create_parameters()?;
        match &type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Map(_) => {
                // For these types the unique ref predicate is abstract.
            }
            vir_mid::TypeDecl::Trusted(_) | vir_mid::TypeDecl::TypeVar(_) => {}
            vir_mid::TypeDecl::Struct(decl) => {
                let mut equalities = Vec::new();
                for field in &decl.fields {
                    equalities.push(builder.create_field_snapshot_equality(field)?);
                }
                builder.add_postcondition(equalities.into_iter().conjoin())?;
                builder.add_structural_invariant(decl)?;
            }
            vir_mid::TypeDecl::Enum(_decl) => {}
            vir_mid::TypeDecl::Reference(_decl) => {
                // For references, the final snapshot is abstract.
            }
            vir_mid::TypeDecl::Array(_decl) => {}
            _ => {
                unimplemented!("{}", type_decl);
            }
        }
        let function = builder.build()?;
        self.lowerer.declare_function(function)?;
        Ok(())
    }

    pub(super) fn encode_frac_ref_snapshot(
        &mut self,
        normalized_type: &vir_mid::Type,
        type_decl: &vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<()> {
        let mut builder =
            FracRefSnapFunctionBuilder::new(self.lowerer, normalized_type, type_decl)?;
        builder.create_parameters()?;
        builder.add_frac_ref_precondition()?;
        match &type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Map(_) => {
                // For these types the unique ref predicate is abstract.
            }
            vir_mid::TypeDecl::Trusted(_) | vir_mid::TypeDecl::TypeVar(_) => {}
            vir_mid::TypeDecl::Struct(decl) => {
                let mut equalities = Vec::new();
                for field in &decl.fields {
                    equalities.push(builder.create_field_snapshot_equality(field)?);
                }
                builder.add_unfolding_postcondition(equalities.into_iter().conjoin())?;
                builder.add_structural_invariant(decl)?;
            }
            vir_mid::TypeDecl::Enum(_decl) => {}
            vir_mid::TypeDecl::Reference(_decl) => {}
            vir_mid::TypeDecl::Array(_decl) => {}
            _ => {
                unimplemented!("{}", type_decl);
            }
        }
        let function = builder.build()?;
        self.lowerer.declare_function(function)?;
        Ok(())
    }

    pub(super) fn encode_owned_non_aliased(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if self
            .encoded_owned_non_aliased_predicates
            .contains(&ty_identifier)
        {
            return Ok(());
        }

        self.encoded_owned_non_aliased_predicates
            .insert(ty_identifier);
        self.lowerer.encode_compute_address(ty)?;
        let type_decl = self.lowerer.encoder.get_type_decl_mid(ty)?;

        let normalized_type = ty.normalize_type();
        self.lowerer
            .encode_snapshot_to_bytes_function(&normalized_type)?;
        // if !config::use_snapshot_parameters_in_predicates() {
        let (snap_function_name, snap_type) =
            self.encode_owned_non_aliased_snapshot(&normalized_type, &type_decl)?;
        // }
        let mut owned_predicates_to_encode = Vec::new();
        let mut unique_ref_predicates_to_encode = Vec::new();
        let mut frac_ref_predicates_to_encode = Vec::new();
        self.lowerer.encode_memory_block_predicate()?;
        let mut builder = OwnedNonAliasedBuilder::new(self.lowerer, &normalized_type, &type_decl)?;
        builder.create_parameters()?;
        if !(type_decl.is_type_var() || type_decl.is_trusted()) {
            builder.create_body();
            if config::use_snapshot_parameters_in_predicates() {
                builder.add_validity()?;
            }
        }
        // Build the body.
        match &type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Map(_) => {
                builder.add_base_memory_block()?;
                // if config::use_snapshot_parameters_in_predicates() {
                //     builder.add_bytes_snapshot_equality()?;
                // }
                if let vir_mid::TypeDecl::Pointer(decl) = &type_decl {
                    owned_predicates_to_encode.push(decl.target_type.clone());
                }
            }
            vir_mid::TypeDecl::Trusted(_) | vir_mid::TypeDecl::TypeVar(_) => {}
            vir_mid::TypeDecl::Struct(decl) => {
                builder.add_padding_memory_block()?;
                for field in &decl.fields {
                    builder.add_field_predicate(field)?;
                    // if !self
                    //     .unfolded_owned_non_aliased_predicates
                    //     .contains(&field.ty)
                    // {
                    owned_predicates_to_encode.push(field.ty.clone());
                    // }
                }
                owned_predicates_to_encode.extend(builder.add_structural_invariant(decl)?);
            }
            vir_mid::TypeDecl::Enum(decl) => {
                builder.add_padding_memory_block()?;
                let mut variant_predicates = Vec::new();
                for (discriminant, variant) in decl.iter_discriminant_variants() {
                    let variant_index: vir_mid::ty::VariantIndex = variant.name.clone().into();
                    let variant_type = vir_mid::Type::enum_(
                        decl.name.clone(),
                        decl.safety,
                        decl.arguments.clone(),
                        Some(variant_index.clone()),
                        decl.lifetimes.clone(),
                    );
                    variant_predicates.push(builder.create_variant_predicate(
                        decl,
                        discriminant,
                        variant,
                        &variant_type,
                    )?);
                    let variant_type = ty.clone().variant(variant_index);
                    // if !self
                    //     .unfolded_owned_non_aliased_predicates
                    //     .contains(&variant_type)
                    // {
                    owned_predicates_to_encode.push(variant_type);
                    // }
                }
                // if !self
                //     .unfolded_owned_non_aliased_predicates
                //     .contains(&decl.discriminant_type)
                // {
                owned_predicates_to_encode.push(decl.discriminant_type.clone());
                // }
                if decl.safety.is_enum() {
                    builder.add_discriminant_predicate(decl)?;
                }
                builder.add_variant_predicates(variant_predicates)?;
            }
            vir_mid::TypeDecl::Reference(decl) => {
                builder.add_base_memory_block()?;
                if config::use_snapshot_parameters_in_predicates() {
                    builder.add_bytes_address_snapshot_equality()?;
                }
                // FIXME: Have a getter for the first lifetime.
                let lifetime = &decl.lifetimes[0];
                if decl.uniqueness.is_unique() {
                    builder.add_unique_ref_target_predicate(&decl.target_type, lifetime)?;
                    unique_ref_predicates_to_encode.push(decl.target_type.clone());
                } else {
                    builder.add_frac_ref_target_predicate(&decl.target_type, lifetime)?;
                    frac_ref_predicates_to_encode.push(decl.target_type.clone());
                }
            }
            vir_mid::TypeDecl::Array(decl) => {
                builder.lowerer().encode_place_array_index_axioms(ty)?;
                builder
                    .lowerer()
                    .ensure_type_definition(&decl.element_type)?;
                owned_predicates_to_encode.push(decl.element_type.clone());
                builder.add_const_parameters_validity()?;
                // FIXME: Have a getter for the first const parameter.
                let length = if normalized_type.is_slice() {
                    builder.get_slice_len()?
                } else {
                    decl.const_parameters[0].clone()
                };
                if config::use_snapshot_parameters_in_predicates() {
                    builder.add_snapshot_len_equal_to(&length)?;
                }
                builder.add_quantified_permission(&length, &decl.element_type)?;
            }
            _ => {
                builder.add_base_memory_block()?;
                builder.add_bytes_snapshot_equality()?;
                unimplemented!("{}", type_decl);
            }
        }
        let predicate = builder.build();
        self.predicate_info
            .insert(predicate.name.clone(), (snap_function_name, snap_type));
        self.predicates.push(predicate);
        for ty in owned_predicates_to_encode {
            // TODO: Optimization: This variant is never unfolded,
            // encode it as abstract predicate.
            self.encode_owned_non_aliased(&ty)?;
        }
        for ty in unique_ref_predicates_to_encode {
            // TODO: Optimization: This variant is never unfolded,
            // encode it as abstract predicate.
            self.encode_unique_ref(&ty)?;
        }
        for ty in frac_ref_predicates_to_encode {
            // TODO: Optimization: This variant is never unfolded,
            // encode it as abstract predicate.
            self.encode_frac_ref(&ty)?;
        }
        Ok(())
    }

    pub(super) fn encode_owned_aliased(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if self
            .encoded_owned_aliased_predicates
            .contains(&ty_identifier)
        {
            return Ok(());
        }

        self.encoded_owned_aliased_predicates.insert(ty_identifier);
        self.lowerer.encode_compute_address(ty)?;
        let type_decl = self.lowerer.encoder.get_type_decl_mid(ty)?;

        let normalized_type = ty.normalize_type();
        self.lowerer
            .encode_snapshot_to_bytes_function(&normalized_type)?;
        self.encode_owned_aliased_snapshot(&normalized_type, &type_decl)?;
        let mut owned_predicates_to_encode = Vec::new();
        let mut unique_ref_predicates_to_encode = Vec::new();
        let mut frac_ref_predicates_to_encode = Vec::new();
        self.lowerer.encode_memory_block_predicate()?;
        let mut builder = OwnedAliasedBuilder::new(self.lowerer, &normalized_type, &type_decl)?;
        builder.create_parameters()?;
        if !(type_decl.is_type_var() || type_decl.is_trusted()) {
            builder.create_body();
        }
        // Build the body.
        match &type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Map(_) => {
                builder.add_base_memory_block()?;
                if let vir_mid::TypeDecl::Pointer(decl) = &type_decl {
                    owned_predicates_to_encode.push(decl.target_type.clone());
                }
            }
            vir_mid::TypeDecl::Trusted(_) | vir_mid::TypeDecl::TypeVar(_) => {}
            vir_mid::TypeDecl::Struct(decl) => {
                builder.add_padding_memory_block()?;
                for field in &decl.fields {
                    builder.add_field_predicate(field)?;
                    owned_predicates_to_encode.push(field.ty.clone());
                }
                owned_predicates_to_encode.extend(builder.add_structural_invariant(decl)?);
            }
            vir_mid::TypeDecl::Enum(decl) => {
                builder.add_padding_memory_block()?;
                let mut variant_predicates = Vec::new();
                for (discriminant, variant) in decl.iter_discriminant_variants() {
                    let variant_index: vir_mid::ty::VariantIndex = variant.name.clone().into();
                    let variant_type = vir_mid::Type::enum_(
                        decl.name.clone(),
                        decl.safety,
                        decl.arguments.clone(),
                        Some(variant_index.clone()),
                        decl.lifetimes.clone(),
                    );
                    variant_predicates.push(builder.create_variant_predicate(
                        decl,
                        discriminant,
                        variant,
                        &variant_type,
                    )?);
                    let variant_type = ty.clone().variant(variant_index);
                    owned_predicates_to_encode.push(variant_type);
                }
                owned_predicates_to_encode.push(decl.discriminant_type.clone());
                if decl.safety.is_enum() {
                    builder.add_discriminant_predicate(decl)?;
                }
                builder.add_variant_predicates(variant_predicates)?;
            }
            vir_mid::TypeDecl::Reference(decl) => {
                builder.add_base_memory_block()?;
                // FIXME: Have a getter for the first lifetime.
                let lifetime = &decl.lifetimes[0];
                if decl.uniqueness.is_unique() {
                    builder.add_unique_ref_target_predicate(&decl.target_type, lifetime)?;
                    unique_ref_predicates_to_encode.push(decl.target_type.clone());
                } else {
                    builder.add_frac_ref_target_predicate(&decl.target_type, lifetime)?;
                    frac_ref_predicates_to_encode.push(decl.target_type.clone());
                }
            }
            vir_mid::TypeDecl::Array(decl) => {
                builder.lowerer().encode_place_array_index_axioms(ty)?;
                builder
                    .lowerer()
                    .ensure_type_definition(&decl.element_type)?;
                owned_predicates_to_encode.push(decl.element_type.clone());
                builder.add_const_parameters_validity()?;
                // FIXME: Have a getter for the first const parameter.
                let length = if normalized_type.is_slice() {
                    builder.get_slice_len()?
                } else {
                    decl.const_parameters[0].clone()
                };
                unimplemented!();
                // builder.add_quantified_permission(&length, &decl.element_type)?;
            }
            _ => {
                builder.add_base_memory_block()?;
                unimplemented!("{}", type_decl);
            }
        }
        self.predicates.push(builder.build());
        for ty in owned_predicates_to_encode {
            // TODO: Optimization: This variant is never unfolded,
            // encode it as abstract predicate.
            self.encode_owned_aliased(&ty)?;
        }
        for ty in unique_ref_predicates_to_encode {
            // TODO: Optimization: This variant is never unfolded,
            // encode it as abstract predicate.
            self.encode_unique_ref(&ty)?;
        }
        for ty in frac_ref_predicates_to_encode {
            // TODO: Optimization: This variant is never unfolded,
            // encode it as abstract predicate.
            self.encode_frac_ref(&ty)?;
        }
        Ok(())
    }

    fn encode_frac_ref(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if self.encoded_frac_borrow_predicates.contains(&ty_identifier) {
            return Ok(());
        }
        self.encoded_frac_borrow_predicates.insert(ty_identifier);
        self.lowerer.encode_compute_address(ty)?;
        let type_decl = self.lowerer.encoder.get_type_decl_mid(ty)?;

        let normalized_type = ty.normalize_type();
        if !config::use_snapshot_parameters_in_predicates() {
            self.encode_frac_ref_snapshot(&normalized_type, &type_decl)?;
        }
        let mut predicates_to_encode = Vec::new();
        let mut builder = FracRefBuilder::new(self.lowerer, &normalized_type, &type_decl)?;
        builder.create_parameters()?;
        if !matches!(
            type_decl,
            vir_mid::TypeDecl::Bool
                | vir_mid::TypeDecl::Int(_)
                | vir_mid::TypeDecl::Float(_)
                | vir_mid::TypeDecl::Pointer(_)
                | vir_mid::TypeDecl::Sequence(_)
                | vir_mid::TypeDecl::Trusted(_)
                | vir_mid::TypeDecl::Map(_)
                | vir_mid::TypeDecl::TypeVar(_)
        ) {
            builder.create_body();
            // builder.add_validity()?;
        }
        // Build the body.
        match &type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Trusted(_)
            | vir_mid::TypeDecl::Map(_)
            | vir_mid::TypeDecl::TypeVar(_) => {}
            vir_mid::TypeDecl::Struct(decl) => {
                for field in &decl.fields {
                    builder.add_field_predicate(field)?;
                    predicates_to_encode.push(field.ty.clone());
                }
                predicates_to_encode.extend(builder.add_structural_invariant(decl)?);
            }
            vir_mid::TypeDecl::Enum(decl) => {
                let mut variant_predicates = Vec::new();
                for (discriminant, variant) in decl.iter_discriminant_variants() {
                    let variant_index = variant.name.clone().into();
                    let variant_type = ty.clone().variant(variant_index);
                    variant_predicates.push(builder.create_variant_predicate(
                        discriminant,
                        variant,
                        &variant_type,
                    )?);
                    predicates_to_encode.push(variant_type);
                }
                predicates_to_encode.push(decl.discriminant_type.clone());
                if decl.safety.is_enum() {
                    builder.add_discriminant_predicate(decl)?;
                }
                builder.add_variant_predicates(variant_predicates)?;
            }
            vir_mid::TypeDecl::Reference(decl) => {
                // FIXME: Have a getter for the first lifetime.
                let lifetime = &decl.lifetimes[0];
                builder.add_frac_ref_target_predicate(&decl.target_type, lifetime)?;
                predicates_to_encode.push(decl.target_type.clone());
            }
            vir_mid::TypeDecl::Array(decl) => {
                builder.lowerer().encode_place_array_index_axioms(ty)?;
                builder
                    .lowerer()
                    .ensure_type_definition(&decl.element_type)?;
                predicates_to_encode.push(decl.element_type.clone());
                builder.add_const_parameters_validity()?;
                // FIXME: Have a getter for the first const parameter.
                let length = if normalized_type.is_slice() {
                    builder.get_slice_len()?
                } else {
                    decl.const_parameters[0].clone()
                };
                builder.add_snapshot_len_equal_to(&length)?;
                builder.add_quantified_permission(&length, &decl.element_type)?;
            }
            _ => {
                unimplemented!("{:?}", type_decl);
            }
        }
        self.predicates.push(builder.build());
        for ty in predicates_to_encode {
            // TODO: Optimization: This variant is never unfolded,
            // encode it as abstract predicate.
            self.encode_frac_ref(&ty)?;
        }
        Ok(())
    }

    pub(super) fn encode_unique_ref(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if self.encoded_mut_borrow_predicates.contains(&ty_identifier) {
            return Ok(());
        }
        self.encoded_mut_borrow_predicates.insert(ty_identifier);
        self.lowerer.encode_compute_address(ty)?;
        let type_decl = self.lowerer.encoder.get_type_decl_mid(ty)?;

        // FIXME: Make get_type_decl_mid to return the erased ty for which it
        // returned type_decl.
        let normalized_type = ty.normalize_type();
        // if !config::use_snapshot_parameters_in_predicates() {
        self.encode_unique_ref_current_snapshot(&normalized_type, &type_decl)?;
        self.encode_unique_ref_final_snapshot(&normalized_type, &type_decl)?;
        // }
        let mut unique_ref_predicates_to_encode = Vec::new();
        let mut frac_ref_predicates_to_encode = Vec::new();
        let mut builder = UniqueRefBuilder::new(self.lowerer, &normalized_type, &type_decl)?;
        builder.create_parameters()?;
        if !matches!(
            type_decl,
            vir_mid::TypeDecl::Bool
                | vir_mid::TypeDecl::Int(_)
                | vir_mid::TypeDecl::Float(_)
                | vir_mid::TypeDecl::Pointer(_)
                | vir_mid::TypeDecl::Sequence(_)
                | vir_mid::TypeDecl::Trusted(_)
                | vir_mid::TypeDecl::Map(_)
                | vir_mid::TypeDecl::TypeVar(_)
        ) {
            builder.create_body();
            // if config::use_snapshot_parameters_in_predicates() {
            //     builder.add_validity()?;
            // }
        }
        // Build the body.
        match &type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Trusted(_)
            | vir_mid::TypeDecl::Map(_)
            | vir_mid::TypeDecl::TypeVar(_) => {}
            vir_mid::TypeDecl::Struct(decl) => {
                for field in &decl.fields {
                    builder.add_field_predicate(field)?;
                    unique_ref_predicates_to_encode.push(field.ty.clone());
                }
                unique_ref_predicates_to_encode.extend(builder.add_structural_invariant(decl)?);
            }
            vir_mid::TypeDecl::Enum(decl) => {
                let mut variant_predicates = Vec::new();
                for (discriminant, variant) in decl.iter_discriminant_variants() {
                    let variant_index = variant.name.clone().into();
                    let variant_type = ty.clone().variant(variant_index);
                    variant_predicates.push(builder.create_variant_predicate(
                        discriminant,
                        variant,
                        &variant_type,
                    )?);
                    unique_ref_predicates_to_encode.push(variant_type);
                }
                unique_ref_predicates_to_encode.push(decl.discriminant_type.clone());
                if decl.safety.is_enum() {
                    builder.add_discriminant_predicate(decl)?;
                }
                builder.add_variant_predicates(variant_predicates)?;
            }
            vir_mid::TypeDecl::Reference(decl) => {
                // FIXME: Have a getter for the first lifetime.
                let lifetime = &decl.lifetimes[0];
                let pointer_type = builder.add_unique_ref_pointer_predicate(lifetime)?;
                if decl.uniqueness.is_unique() {
                    builder.add_unique_ref_target_predicate(&decl.target_type, lifetime)?;
                    unique_ref_predicates_to_encode.push(decl.target_type.clone());
                    unique_ref_predicates_to_encode.push(pointer_type);
                } else {
                    builder.add_frac_ref_target_predicate(&decl.target_type, lifetime)?;
                    frac_ref_predicates_to_encode.push(decl.target_type.clone());
                    frac_ref_predicates_to_encode.push(pointer_type);
                }
            }
            vir_mid::TypeDecl::Array(decl) => {
                builder.lowerer().encode_place_array_index_axioms(ty)?;
                builder
                    .lowerer()
                    .ensure_type_definition(&decl.element_type)?;
                unique_ref_predicates_to_encode.push(decl.element_type.clone());
                builder.add_const_parameters_validity()?;
                // FIXME: Have a getter for the first const parameter.
                let length = if normalized_type.is_slice() {
                    builder.get_slice_len()?
                } else {
                    decl.const_parameters[0].clone()
                };
                if config::use_snapshot_parameters_in_predicates() {
                    builder.add_snapshot_len_equal_to(&length)?;
                }
                builder.add_quantified_permission(&length, &decl.element_type)?;
            }
            _ => {
                unimplemented!("{:?}", type_decl);
            }
        }
        self.predicates.push(builder.build());
        for ty in unique_ref_predicates_to_encode {
            // TODO: Optimization: This variant is never unfolded,
            // encode it as abstract predicate.
            self.encode_unique_ref(&ty)?;
        }
        for ty in frac_ref_predicates_to_encode {
            self.encode_frac_ref(&ty)?;
        }
        Ok(())
    }
}
