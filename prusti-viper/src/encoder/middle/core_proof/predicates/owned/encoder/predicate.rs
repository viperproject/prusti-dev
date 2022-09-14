use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        compute_address::ComputeAddressInterface,
        lowerer::Lowerer,
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

use vir_crate::middle::{self as vir_mid};

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
    pub(in super::super) fn encode_owned_predicate(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        super::guard!(self, encoded_owned_predicates, ty);
        // let ty_identifier = ty.get_identifier();
        // if self
        //     .state()
        //     .encoded_owned_non_aliased_predicates
        //     .contains(&ty_identifier)
        // {
        //     return Ok(());
        // }

        // self.state()
        //     .encoded_owned_non_aliased_predicates
        //     .insert(ty_identifier);
        self.encode_compute_address(ty)?;
        let type_decl = self.encoder.get_type_decl_mid(ty)?;

        let normalized_type = ty.normalize_type();
        self.encode_snapshot_to_bytes_function(&normalized_type)?;
        let predicate_info = self.encode_owned_predicate_snapshot(&normalized_type, &type_decl)?;
        let mut owned_predicates_to_encode = Vec::new();
        let mut unique_ref_predicates_to_encode = Vec::new();
        let mut frac_ref_predicates_to_encode = Vec::new();
        self.encode_memory_block_predicate()?;
        let mut builder = OwnedNonAliasedBuilder::new(self, &normalized_type, &type_decl)?;
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
                builder.add_quantified_permission(&length, &decl.element_type)?;
            }
            _ => {
                builder.add_base_memory_block()?;
                builder.add_bytes_snapshot_equality()?;
                unimplemented!("{}", type_decl);
            }
        }
        let predicate = builder.build();
        self.state()
            .predicate_info
            .insert(predicate.name.clone(), predicate_info);
        self.state().predicates.push(predicate);
        for ty in owned_predicates_to_encode {
            // TODO: Optimization: This variant is never unfolded,
            // encode it as abstract predicate.
            self.encode_owned_predicate(&ty)?;
        }
        for ty in unique_ref_predicates_to_encode {
            // TODO: Optimization: This variant is never unfolded,
            // encode it as abstract predicate.
            self.encode_unique_ref_predicate(&ty)?;
        }
        for ty in frac_ref_predicates_to_encode {
            // TODO: Optimization: This variant is never unfolded,
            // encode it as abstract predicate.
            self.encode_frac_ref_predicate(&ty)?;
        }
        Ok(())
    }

    pub(in super::super) fn encode_unique_ref_predicate(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        super::guard!(self, encoded_unique_ref_predicates, ty);
        // let ty_identifier = ty.get_identifier();
        // if self
        //     .state()
        //     .encoded_mut_borrow_predicates
        //     .contains(&ty_identifier)
        // {
        //     return Ok(());
        // }
        // self.state()
        //     .encoded_mut_borrow_predicates
        //     .insert(ty_identifier);
        self.encode_compute_address(ty)?;
        let type_decl = self.encoder.get_type_decl_mid(ty)?;

        // FIXME: Make get_type_decl_mid to return the erased ty for which it
        // returned type_decl.
        let normalized_type = ty.normalize_type();
        // if !config::use_snapshot_parameters_in_predicates() {
        let current_predicate_info =
            self.encode_unique_ref_predicate_current_snapshot(&normalized_type, &type_decl)?;
        let final_predicate_info =
            self.encode_unique_ref_predicate_final_snapshot(&normalized_type, &type_decl)?;
        // }
        let mut unique_ref_predicates_to_encode = Vec::new();
        let mut frac_ref_predicates_to_encode = Vec::new();
        let mut builder = UniqueRefBuilder::new(self, &normalized_type, &type_decl)?;
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
                        decl,
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
                builder.add_quantified_permission(&length, &decl.element_type)?;
            }
            _ => {
                unimplemented!("{:?}", type_decl);
            }
        }
        let predicate = builder.build();
        assert_eq!(
            current_predicate_info.snapshot_type,
            final_predicate_info.snapshot_type
        );
        let mut predicate_info = current_predicate_info;
        predicate_info.final_snapshot_function =
            Some(final_predicate_info.current_snapshot_function);
        self.state()
            .predicate_info
            .insert(predicate.name.clone(), predicate_info);
        self.state().predicates.push(predicate);
        for ty in unique_ref_predicates_to_encode {
            // TODO: Optimization: This variant is never unfolded,
            // encode it as abstract predicate.
            self.encode_unique_ref_predicate(&ty)?;
        }
        for ty in frac_ref_predicates_to_encode {
            self.encode_frac_ref_predicate(&ty)?;
        }
        Ok(())
    }

    pub(in super::super) fn encode_frac_ref_predicate(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        super::guard!(self, encoded_frac_ref_predicates, ty);
        // let ty_identifier = ty.get_identifier();
        // if self
        //     .state()
        //     .encoded_frac_borrow_predicates
        //     .contains(&ty_identifier)
        // {
        //     return Ok(());
        // }
        // self.state()
        //     .encoded_frac_borrow_predicates
        //     .insert(ty_identifier);
        self.encode_compute_address(ty)?;
        let type_decl = self.encoder.get_type_decl_mid(ty)?;

        let normalized_type = ty.normalize_type();
        let predicate_info =
            self.encode_frac_ref_predicate_snapshot(&normalized_type, &type_decl)?;
        let mut predicates_to_encode = Vec::new();
        let mut builder = FracRefBuilder::new(self, &normalized_type, &type_decl)?;
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
                        decl,
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
                let pointer_type = builder.add_frac_ref_pointer_predicate(lifetime)?;
                builder.add_frac_ref_target_predicate(&decl.target_type, lifetime)?;
                predicates_to_encode.push(decl.target_type.clone());
                predicates_to_encode.push(pointer_type);
            }
            vir_mid::TypeDecl::Array(decl) => {
                builder.lowerer().encode_place_array_index_axioms(ty)?;
                builder
                    .lowerer()
                    .ensure_type_definition(&decl.element_type)?;
                predicates_to_encode.push(decl.element_type.clone());
                builder.add_const_parameters_validity()?;
                // FIXME: Have a getter for the first const parameter.
                let _length = if normalized_type.is_slice() {
                    builder.get_slice_len()?
                } else {
                    decl.const_parameters[0].clone()
                };
                unimplemented!();
                // builder.add_snapshot_len_equal_to(&length)?;
                // builder.add_quantified_permission(&length, &decl.element_type)?;
            }
            _ => {
                unimplemented!("{:?}", type_decl);
            }
        }
        let predicate = builder.build();
        self.state()
            .predicate_info
            .insert(predicate.name.clone(), predicate_info);
        self.state().predicates.push(predicate);
        for ty in predicates_to_encode {
            // TODO: Optimization: This variant is never unfolded,
            // encode it as abstract predicate.
            self.encode_frac_ref_predicate(&ty)?;
        }
        Ok(())
    }
}
