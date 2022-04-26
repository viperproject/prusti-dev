use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        lowerer::{DomainsLowererInterface, Lowerer},
        snapshots::{
            IntoPureSnapshot, IntoSnapshot, SnapshotAdtsInterface, SnapshotDomainsInterface,
            SnapshotValidityInterface,
        },
    },
};
use rustc_hash::FxHashSet;
use std::collections::BTreeSet;
use vir_crate::{
    common::{
        expression::{ExpressionIterator, QuantifierHelpers},
        identifier::WithIdentifier,
    },
    low::{self as vir_low},
    middle as vir_mid,
};

#[derive(Default)]
pub(in super::super) struct TypesState {
    /// The types for which the definitions were ensured.
    ensured_definitions: BTreeSet<vir_mid::Type>,
    encoded_binary_operations: FxHashSet<String>,
    encoded_unary_operations: FxHashSet<String>,
}

trait Private {
    fn ensure_type_definition_for_decl(
        &mut self,
        ty: &vir_mid::Type,
        type_decl: &vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<()>;
    fn declare_simplification_axiom(
        &mut self,
        ty: &vir_mid::Type,
        variant: &str,
        parameters: Vec<vir_low::VariableDecl>,
        parameter_type: &vir_mid::Type,
        simplification_result: vir_low::Expression,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn ensure_type_definition_for_decl(
        &mut self,
        ty: &vir_mid::Type,
        type_decl: &vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        match type_decl {
            vir_mid::TypeDecl::Bool => {
                self.register_constant_constructor(&domain_name, vir_low::Type::Bool)?;
                self.encode_validity_axioms_primitive(
                    &domain_name,
                    vir_low::Type::Bool,
                    true.into(),
                )?;
            }
            vir_mid::TypeDecl::Int(decl) => {
                self.ensure_type_definition(&vir_mid::Type::Bool)?;
                self.register_constant_constructor(&domain_name, vir_low::Type::Int)?;
                var_decls! { value: Int };
                let mut conjuncts = Vec::new();
                if let Some(lower_bound) = &decl.lower_bound {
                    conjuncts
                        .push(expr! { [lower_bound.clone().to_pure_snapshot(self)? ] <= value });
                }
                if let Some(upper_bound) = &decl.upper_bound {
                    conjuncts
                        .push(expr! { value <= [upper_bound.clone().to_pure_snapshot(self)? ] });
                }
                let validity = conjuncts.into_iter().conjoin();
                self.encode_validity_axioms_primitive(&domain_name, vir_low::Type::Int, validity)?;
            }
            vir_mid::TypeDecl::Tuple(decl) => {
                let mut parameters = Vec::new();
                for field in decl.iter_fields() {
                    parameters.push(vir_low::VariableDecl::new(
                        field.name.clone(),
                        field.ty.to_snapshot(self)?,
                    ));
                }
                self.register_struct_constructor(&domain_name, parameters.clone())?;
                self.encode_validity_axioms_struct(&domain_name, parameters, true.into())?;
            }
            vir_mid::TypeDecl::Struct(decl) => {
                let mut parameters = Vec::new();
                for field in decl.iter_fields() {
                    parameters.push(vir_low::VariableDecl::new(
                        field.name.clone(),
                        field.ty.to_snapshot(self)?,
                    ));
                }
                self.register_struct_constructor(&domain_name, parameters.clone())?;
                self.encode_validity_axioms_struct(&domain_name, parameters, true.into())?;
            }
            vir_mid::TypeDecl::Enum(decl) => {
                let mut variants = Vec::new();
                for (variant, &discriminant) in decl.variants.iter().zip(&decl.discriminant_values)
                {
                    let variant_type = ty.clone().variant(variant.name.clone().into());
                    let variant_domain = self.encode_snapshot_domain_name(&variant_type)?;
                    let discriminant: vir_low::Expression = discriminant.into();
                    self.register_enum_variant_constructor(
                        &domain_name,
                        &variant.name,
                        &variant_domain,
                        discriminant.clone(),
                    )?;
                    self.ensure_type_definition(&variant_type)?;
                    variants.push((variant.name.clone(), variant_domain, discriminant));
                }
                self.encode_validity_axioms_enum(
                    ty,
                    &domain_name,
                    variants.clone(),
                    true.into(),
                    &decl.discriminant_bounds,
                )?;
            }
            vir_mid::TypeDecl::Union(decl) => {
                let mut variants = Vec::new();
                for (variant, &discriminant) in decl.variants.iter().zip(&decl.discriminant_values)
                {
                    let variant_type = ty.clone().variant(variant.name.clone().into());
                    let variant_domain = self.encode_snapshot_domain_name(&variant_type)?;
                    let discriminant: vir_low::Expression = discriminant.into();
                    self.register_enum_variant_constructor(
                        &domain_name,
                        &variant.name,
                        &variant_domain,
                        discriminant.clone(),
                    )?;
                    self.ensure_type_definition(&variant_type)?;
                    variants.push((variant.name.clone(), variant_domain, discriminant));
                }
                self.encode_validity_axioms_enum(
                    ty,
                    &domain_name,
                    variants.clone(),
                    true.into(),
                    &decl.discriminant_bounds,
                )?;
            }
            vir_mid::TypeDecl::Pointer(decl) => {
                self.ensure_type_definition(&decl.target_type)?;
                let address_type = self.address_type()?;
                self.register_constant_constructor(&domain_name, address_type.clone())?;
                self.encode_validity_axioms_primitive(&domain_name, address_type, true.into())?;
            }
            vir_mid::TypeDecl::Reference(reference) if reference.uniqueness.is_unique() => {
                self.ensure_type_definition(&reference.target_type)?;
                let target_type = reference.target_type.to_snapshot(self)?;
                let parameters = vars! {
                    address: Address,
                    target_current: {target_type.clone()},
                    target_final: {target_type}
                };
                self.register_struct_constructor(&domain_name, parameters.clone())?;
                self.encode_validity_axioms_struct(&domain_name, parameters, true.into())?;
            }
            _ => unimplemented!("type: {:?}", type_decl),
        };
        Ok(())
    }
    fn declare_simplification_axiom(
        &mut self,
        ty: &vir_mid::Type,
        variant: &str,
        parameters: Vec<vir_low::VariableDecl>,
        parameter_type: &vir_mid::Type,
        simplification_result: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let parameter_domain_name = self.encode_snapshot_domain_name(parameter_type)?;
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let snapshot_type = ty.to_snapshot(self)?;
        let mut constructor_calls = Vec::new();
        for parameter in parameters.iter() {
            constructor_calls.push(self.snapshot_constructor_constant_call(
                &parameter_domain_name,
                vec![parameter.clone().into()],
            )?);
        }
        let constructor_call_op =
            self.snapshot_constructor_constant_call(&domain_name, vec![simplification_result])?;
        let op_constructor_call = vir_low::Expression::domain_function_call(
            &domain_name,
            self.snapshot_constructor_struct_alternative_name(&domain_name, variant)?,
            constructor_calls,
            snapshot_type,
        );
        let body = vir_low::Expression::forall(
            parameters,
            vec![vir_low::Trigger::new(vec![op_constructor_call.clone()])],
            expr! { [op_constructor_call] == [constructor_call_op] },
        );
        let axiom = vir_low::DomainAxiomDecl {
            name: format!("{}$simplification_axiom", variant),
            body,
        };
        self.declare_axiom(&domain_name, axiom)?;
        Ok(())
    }
}

pub(in super::super) trait TypesInterface {
    /// Ensure that all encoders know the necessary information to encode the
    /// uses of this type that require its definition.
    fn ensure_type_definition(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_unary_op_variant(
        &mut self,
        op: vir_mid::UnaryOpKind,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<String>;
    fn encode_binary_op_variant(
        &mut self,
        op: vir_mid::BinaryOpKind,
        argument_type: &vir_mid::Type,
    ) -> SpannedEncodingResult<String>;
    fn decode_type_low_into_mid(&self, ty: &vir_low::Type) -> SpannedEncodingResult<vir_mid::Type>;
}

impl<'p, 'v: 'p, 'tcx: 'v> TypesInterface for Lowerer<'p, 'v, 'tcx> {
    fn ensure_type_definition(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        if matches!(ty, vir_mid::Type::MBool | vir_mid::Type::MInt) {
            // Natively supported types, nothing to do.
            return Ok(());
        }
        if !self.types_state.ensured_definitions.contains(ty) {
            // We insert before doing the actual work to break infinite
            // recursion.
            self.types_state.ensured_definitions.insert(ty.clone());

            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            self.ensure_type_definition_for_decl(ty, &type_decl)?;
        }
        Ok(())
    }
    fn encode_unary_op_variant(
        &mut self,
        op: vir_mid::UnaryOpKind,
        argument_type: &vir_mid::Type,
    ) -> SpannedEncodingResult<String> {
        let variant_name = format!("{}_{}", op, argument_type.get_identifier());
        if !self
            .types_state
            .encoded_unary_operations
            .contains(&variant_name)
        {
            self.types_state
                .encoded_unary_operations
                .insert(variant_name.clone());
            use vir_low::macros::*;
            let snapshot_type = argument_type.to_snapshot(self)?;
            let result_type = argument_type;
            let result_domain = self.encode_snapshot_domain_name(result_type)?;
            self.register_alternative_constructor(
                &result_domain,
                &variant_name,
                vars! { argument: {snapshot_type} },
            )?;
            // Simplification axioms.
            let op = op.to_snapshot(self)?;
            let simplification = match argument_type {
                vir_mid::Type::Bool => {
                    assert_eq!(op, vir_low::UnaryOpKind::Not);
                    var_decls! { constant: Bool };
                    Some((expr! { !constant }, constant))
                }
                vir_mid::Type::Int(_) => {
                    assert_eq!(op, vir_low::UnaryOpKind::Minus);
                    var_decls! { constant: Int };
                    Some((expr! { -constant }, constant))
                }
                _ => None,
            };
            if let Some((simplification_result, parameter)) = simplification {
                self.declare_simplification_axiom(
                    result_type,
                    &variant_name,
                    vec![parameter],
                    argument_type,
                    simplification_result,
                )?;
            }
        }
        Ok(variant_name)
    }
    fn encode_binary_op_variant(
        &mut self,
        op: vir_mid::BinaryOpKind,
        argument_type: &vir_mid::Type,
    ) -> SpannedEncodingResult<String> {
        let variant_name = format!("{}_{}", op, argument_type.get_identifier());
        if !self
            .types_state
            .encoded_binary_operations
            .contains(&variant_name)
        {
            self.types_state
                .encoded_binary_operations
                .insert(variant_name.clone());
            use vir_low::macros::*;
            let snapshot_type = argument_type.to_snapshot(self)?;
            let result_type = op.get_result_type(argument_type);
            let result_domain = self.encode_snapshot_domain_name(result_type)?;
            self.register_alternative_constructor(
                &result_domain,
                &variant_name,
                vars! { left: {snapshot_type.clone()}, right: {snapshot_type} },
            )?;
            // Simplification axioms.
            let op = op.to_snapshot(self)?;
            let constant_type = match argument_type {
                vir_mid::Type::Bool => Some(ty! { Bool }),
                vir_mid::Type::Int(_) => Some(ty! {Int}),
                vir_mid::Type::Pointer(_) => Some(ty!(Address)),
                _ => None,
            };
            if let Some(constant_type) = constant_type {
                var_decls! { left: {constant_type.clone()}, right: {constant_type} };
                let result = vir_low::Expression::binary_op_no_pos(op, expr! {left}, expr! {right});
                self.declare_simplification_axiom(
                    result_type,
                    &variant_name,
                    vec![left, right],
                    argument_type,
                    result,
                )?;
            }
        }
        Ok(variant_name)
    }
    fn decode_type_low_into_mid(&self, ty: &vir_low::Type) -> SpannedEncodingResult<vir_mid::Type> {
        let decoded_type = match ty {
            vir_low::Type::Domain(domain) => {
                if let Some(decoded_type) = self.try_decoding_snapshot_type(&domain.name)? {
                    decoded_type
                } else {
                    unreachable!("Failed to decode the snapshot type: {}", ty);
                }
            }
            _ => unreachable!("Trying to decode unsupported type: {}", ty),
        };
        Ok(decoded_type)
    }
}
