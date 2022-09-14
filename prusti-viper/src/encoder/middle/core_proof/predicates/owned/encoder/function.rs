use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::{FunctionsLowererInterface, Lowerer},
        predicates::{
            owned::builders::{
                FracRefSnapFunctionBuilder, OwnedNonAliasedSnapFunctionBuilder,
                UniqueRefCurrentSnapFunctionBuilder, UniqueRefFinalSnapFunctionBuilder,
            },
            OwnedPredicateInfo, SnapshotFunctionInfo,
        },
    },
};

use vir_crate::{
    common::expression::{ExpressionIterator, GuardedExpressionIterator},
    middle::{self as vir_mid},
};

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
    pub(super) fn encode_owned_predicate_snapshot(
        &mut self,
        normalized_type: &vir_mid::Type,
        type_decl: &vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<OwnedPredicateInfo> {
        super::guard!(assert self, encoded_owned_predicate_snapshot_functions, normalized_type);

        let mut builder =
            OwnedNonAliasedSnapFunctionBuilder::new(self, normalized_type, type_decl)?;
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
                builder.add_snapshot_body_postcondition(equalities.into_iter().conjoin())?;
                builder.add_structural_invariant(decl)?;
            }
            vir_mid::TypeDecl::Enum(decl) => {
                let mut equalities = Vec::new();
                if decl.safety.is_enum() {
                    let discriminant_equality =
                        builder.create_discriminant_snapshot_equality(decl)?;
                    builder.add_snapshot_body_postcondition(discriminant_equality)?;
                }
                for (discriminant, variant) in decl.iter_discriminant_variants() {
                    equalities
                        .push(builder.create_variant_snapshot_equality(discriminant, variant)?);
                }
                builder.add_snapshot_body_postcondition(equalities.into_iter().create_match())?;
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
        let owned_snapshots_to_encode = builder.take_owned_snapshot_functions_to_encode();
        let owned_range_snapshots_to_encode =
            builder.take_owned_range_snapshot_functions_to_encode();
        let snapshot_postconditions = builder.get_snapshot_postconditions()?;
        let snapshot_body = builder.get_snapshot_body()?;
        let function = builder.build()?;
        let function_name = function.name.clone();
        let snapshot_type = function.return_type.clone();
        self.declare_function(function)?;
        for ty in owned_snapshots_to_encode {
            self.encode_owned_predicate(&ty)?;
        }
        for ty in owned_range_snapshots_to_encode {
            self.encode_owned_predicate_range_snapshot(&ty)?;
        }
        Ok(OwnedPredicateInfo {
            current_snapshot_function: SnapshotFunctionInfo {
                function_name,
                postconditions: snapshot_postconditions,
                body: snapshot_body,
            },
            final_snapshot_function: None,
            snapshot_type,
        })
    }

    pub(super) fn encode_unique_ref_predicate_current_snapshot(
        &mut self,
        normalized_type: &vir_mid::Type,
        type_decl: &vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<OwnedPredicateInfo> {
        super::guard!(assert self, encoded_unique_ref_predicate_current_snapshot_functions, normalized_type);

        let mut builder =
            UniqueRefCurrentSnapFunctionBuilder::new(self, normalized_type, type_decl)?;
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
                builder.add_snapshot_body_postcondition(equalities.into_iter().conjoin())?;
                builder.add_structural_invariant(decl)?;
            }
            vir_mid::TypeDecl::Enum(decl) => {
                let mut equalities = Vec::new();
                if decl.safety.is_enum() {
                    let discriminant_equality =
                        builder.create_discriminant_snapshot_equality(decl)?;
                    builder.add_snapshot_body_postcondition(discriminant_equality)?;
                }
                for (discriminant, variant) in decl.iter_discriminant_variants() {
                    equalities
                        .push(builder.create_variant_snapshot_equality(discriminant, variant)?);
                }
                builder.add_snapshot_body_postcondition(equalities.into_iter().create_match())?;
            }
            vir_mid::TypeDecl::Reference(_decl) => {
                // FIXME: Implement.
            }
            vir_mid::TypeDecl::Array(_decl) => {
                unimplemented!();
            }
            _ => {
                unimplemented!("{}", type_decl);
            }
        }
        let snapshot_postconditions = builder.get_snapshot_postconditions()?;
        let snapshot_body = builder.get_snapshot_body()?;
        let function = builder.build()?;
        let function_name = function.name.clone();
        let snapshot_type = function.return_type.clone();
        self.declare_function(function)?;
        Ok(OwnedPredicateInfo {
            current_snapshot_function: SnapshotFunctionInfo {
                function_name,
                postconditions: snapshot_postconditions,
                body: snapshot_body,
            },
            final_snapshot_function: None,
            snapshot_type,
        })
    }

    pub(super) fn encode_unique_ref_predicate_final_snapshot(
        &mut self,
        normalized_type: &vir_mid::Type,
        type_decl: &vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<OwnedPredicateInfo> {
        super::guard!(assert self, encoded_unique_ref_predicate_final_snapshot_functions, normalized_type);

        let mut builder = UniqueRefFinalSnapFunctionBuilder::new(self, normalized_type, type_decl)?;
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
                builder.add_snapshot_postcondition(equalities.into_iter().conjoin())?;
                builder.add_structural_invariant(decl)?;
            }
            vir_mid::TypeDecl::Enum(decl) => {
                let mut equalities = Vec::new();
                if decl.safety.is_enum() {
                    let discriminant_equality =
                        builder.create_discriminant_snapshot_equality(decl)?;
                    builder.add_snapshot_postcondition(discriminant_equality)?;
                }
                for (discriminant, variant) in decl.iter_discriminant_variants() {
                    equalities
                        .push(builder.create_variant_snapshot_equality(discriminant, variant)?);
                }
                builder.add_snapshot_postcondition(equalities.into_iter().create_match())?;
            }
            vir_mid::TypeDecl::Reference(_decl) => {
                // For references, the final snapshot is abstract.
            }
            vir_mid::TypeDecl::Array(_decl) => {
                unimplemented!();
            }
            _ => {
                unimplemented!("{}", type_decl);
            }
        }
        let snapshot_postconditions = builder.get_snapshot_postconditions()?;
        let snapshot_body = builder.get_snapshot_body()?;
        let (function_name, snapshot_type) = builder.build()?;
        Ok(OwnedPredicateInfo {
            current_snapshot_function: SnapshotFunctionInfo {
                function_name,
                postconditions: snapshot_postconditions,
                body: snapshot_body,
            },
            final_snapshot_function: None,
            snapshot_type,
        })
    }

    pub(super) fn encode_frac_ref_predicate_snapshot(
        &mut self,
        normalized_type: &vir_mid::Type,
        type_decl: &vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<OwnedPredicateInfo> {
        super::guard!(assert self, encoded_frac_ref_predicate_snapshot_functions, normalized_type);

        let mut builder = FracRefSnapFunctionBuilder::new(self, normalized_type, type_decl)?;
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
                builder.add_snapshot_body_postcondition(equalities.into_iter().conjoin())?;
                builder.add_structural_invariant(decl)?;
            }
            vir_mid::TypeDecl::Enum(decl) => {
                let mut equalities = Vec::new();
                if decl.safety.is_enum() {
                    let discriminant_equality =
                        builder.create_discriminant_snapshot_equality(decl)?;
                    builder.add_snapshot_body_postcondition(discriminant_equality)?;
                }
                for (discriminant, variant) in decl.iter_discriminant_variants() {
                    equalities
                        .push(builder.create_variant_snapshot_equality(discriminant, variant)?);
                }
                builder.add_snapshot_body_postcondition(equalities.into_iter().create_match())?;
            }
            vir_mid::TypeDecl::Reference(_decl) => {
                // FIXME: Implement.
            }
            vir_mid::TypeDecl::Array(_decl) => {
                unimplemented!();
            }
            _ => {
                unimplemented!("{}", type_decl);
            }
        }
        let snapshot_postconditions = builder.get_snapshot_postconditions()?;
        let snapshot_body = builder.get_snapshot_body()?;
        let function = builder.build()?;
        let function_name = function.name.clone();
        let snapshot_type = function.return_type.clone();
        self.declare_function(function)?;
        Ok(OwnedPredicateInfo {
            current_snapshot_function: SnapshotFunctionInfo {
                function_name,
                postconditions: snapshot_postconditions,
                body: snapshot_body,
            },
            final_snapshot_function: None,
            snapshot_type,
        })
    }
}
