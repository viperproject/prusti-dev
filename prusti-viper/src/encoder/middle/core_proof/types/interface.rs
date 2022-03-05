use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        lowerer::{DomainsLowererInterface, Lowerer},
        snapshots::{
            IntoSnapshot, SnapshotAdtsInterface, SnapshotDomainsInterface,
            SnapshotValidityInterface,
        },
    },
};
use std::collections::BTreeSet;
use vir_crate::{
    common::{
        expression::{ExpressionIterator, QuantifierHelpers},
        identifier::WithIdentifier,
    },
    low::{self as vir_low, operations::ToLow},
    middle as vir_mid,
};

#[derive(Default)]
pub(in super::super) struct TypesState {
    /// The types for which the definitions were ensured.
    ensured_definitions: BTreeSet<vir_mid::Type>,
}

const BOOLEAN_OPERATORS: &[vir_low::BinaryOpKind] = &[
    vir_low::BinaryOpKind::EqCmp,
    vir_low::BinaryOpKind::And,
    vir_low::BinaryOpKind::Or,
    vir_low::BinaryOpKind::Implies,
];

const COMPARISON_OPERATORS: &[vir_low::BinaryOpKind] = &[
    vir_low::BinaryOpKind::EqCmp,
    vir_low::BinaryOpKind::NeCmp,
    vir_low::BinaryOpKind::GtCmp,
    vir_low::BinaryOpKind::GeCmp,
    vir_low::BinaryOpKind::LtCmp,
    vir_low::BinaryOpKind::LeCmp,
];
const ARITHMETIC_OPERATORS: &[vir_low::BinaryOpKind] = &[
    vir_low::BinaryOpKind::Add,
    vir_low::BinaryOpKind::Sub,
    vir_low::BinaryOpKind::Mul,
    vir_low::BinaryOpKind::Div,
    vir_low::BinaryOpKind::Mod,
];

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
    fn declare_simplification_axioms(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
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
                let snapshot_type = ty.create_snapshot(self)?;
                let variant_name =
                    self.encode_unary_op_variant(vir_low::UnaryOpKind::Not, &vir_mid::Type::Bool)?;
                self.register_alternative_constructor(
                    &domain_name,
                    &variant_name,
                    vars! { argument: {snapshot_type.clone()} },
                )?;
                var_decls! { constant: Bool };
                self.declare_simplification_axiom(
                    ty,
                    &variant_name,
                    vec![constant.clone()],
                    ty,
                    expr! { !constant },
                )?;
                for op in BOOLEAN_OPERATORS {
                    // FIXME: Make these on demand.
                    let variant_name = self.encode_binary_op_variant(*op, &vir_mid::Type::Bool)?;
                    self.register_alternative_constructor(
                        &domain_name,
                        &variant_name,
                        vars! { left: {snapshot_type.clone()}, right: {snapshot_type.clone()} },
                    )?;
                    var_decls! { left: Bool, right: Bool };
                    let result =
                        vir_low::Expression::binary_op_no_pos(*op, expr! {left}, expr! {right});
                    self.declare_simplification_axiom(
                        ty,
                        &variant_name,
                        vec![left, right],
                        ty,
                        result,
                    )?;
                }

                self.encode_validity_axioms_primitive(
                    &domain_name,
                    vir_low::Type::Bool,
                    true.into(),
                )?;
            }
            vir_mid::TypeDecl::Int(decl) => {
                self.ensure_type_definition(&vir_mid::Type::Bool)?;
                self.register_constant_constructor(&domain_name, vir_low::Type::Int)?;
                let snapshot_type = ty.create_snapshot(self)?;
                let variant_name = self.encode_unary_op_variant(vir_low::UnaryOpKind::Minus, ty)?;
                self.register_alternative_constructor(
                    &domain_name,
                    &variant_name,
                    vars! { argument: {snapshot_type.clone()} },
                )?;
                var_decls! { constant: Int };
                self.declare_simplification_axiom(
                    ty,
                    &variant_name,
                    vec![constant.clone()],
                    ty,
                    expr! { -constant },
                )?;
                for op in ARITHMETIC_OPERATORS {
                    // FIXME: Make these on demand.
                    let variant_name = self.encode_binary_op_variant(*op, ty)?;
                    self.register_alternative_constructor(
                        &domain_name,
                        &variant_name,
                        vars! { left: {snapshot_type.clone()}, right: {snapshot_type.clone()} },
                    )?;
                    var_decls! { left: Int, right: Int };
                    let result =
                        vir_low::Expression::binary_op_no_pos(*op, expr! {left}, expr! {right});
                    self.declare_simplification_axiom(
                        ty,
                        &variant_name,
                        vec![left, right],
                        ty,
                        result,
                    )?;
                }
                let bool_domain_name = self.encode_snapshot_domain_name(&vir_mid::Type::Bool)?;
                for op in COMPARISON_OPERATORS {
                    // FIXME: Make these on demand.
                    let variant_name = self.encode_binary_op_variant(*op, ty)?;
                    self.register_alternative_constructor(
                        &bool_domain_name,
                        &variant_name,
                        vars! { left: {snapshot_type.clone()}, right: {snapshot_type.clone()} },
                    )?;
                    var_decls! { left: Int, right: Int };
                    let result =
                        vir_low::Expression::binary_op_no_pos(*op, expr! {left}, expr! {right});
                    self.declare_simplification_axiom(
                        &vir_mid::Type::Bool,
                        &variant_name,
                        vec![left, right],
                        ty,
                        result,
                    )?;
                }
                var_decls! { value: Int };
                let mut conjuncts = Vec::new();
                if let Some(lower_bound) = &decl.lower_bound {
                    conjuncts.push(expr! { [lower_bound.clone().to_low(self)? ] <= value });
                }
                if let Some(upper_bound) = &decl.upper_bound {
                    conjuncts.push(expr! { value <= [upper_bound.clone().to_low(self)? ] });
                }
                let validity = conjuncts.into_iter().conjoin();
                self.encode_validity_axioms_primitive(&domain_name, vir_low::Type::Int, validity)?;
            }
            vir_mid::TypeDecl::Tuple(decl) => {
                let mut parameters = Vec::new();
                for field in decl.iter_fields() {
                    parameters.push(vir_low::VariableDecl::new(
                        field.name.clone(),
                        field.ty.create_snapshot(self)?,
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
                        field.ty.create_snapshot(self)?,
                    ));
                }
                self.register_struct_constructor(&domain_name, parameters.clone())?;
                self.encode_validity_axioms_struct(&domain_name, parameters, true.into())?;
            }
            vir_mid::TypeDecl::Enum(decl) => {
                let mut variants = Vec::new();
                for (variant, discriminant) in decl.variants.iter().zip(&decl.discriminant_values) {
                    let variant_type = ty.clone().variant(variant.name.clone().into());
                    let variant_domain = self.encode_snapshot_domain_name(&variant_type)?;
                    let discriminant = discriminant.clone().to_low(self)?;
                    self.register_enum_variant_constructor(
                        &domain_name,
                        &variant.name,
                        &variant_domain,
                        discriminant.clone(),
                    )?;
                    self.ensure_type_definition(&variant_type)?;
                    variants.push((variant.name.clone(), variant_domain, discriminant));
                }
                let discriminant_bounds = decl.discriminant_bounds.clone().to_low(self)?;
                self.encode_validity_axioms_enum(
                    ty,
                    &domain_name,
                    variants.clone(),
                    true.into(),
                    discriminant_bounds,
                )?;
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
        let snapshot_type = ty.create_snapshot(self)?;
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
    fn declare_simplification_axioms(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        match ty {
            vir_mid::Type::Bool => {
                let variant = self.encode_unary_op_variant(vir_low::UnaryOpKind::Not, ty)?;
                var_decls! { constant: Bool };
                let result = expr! { !constant };
                self.declare_simplification_axiom(ty, &variant, vec![constant], ty, result)?;
                for op in BOOLEAN_OPERATORS {
                    let variant = self.encode_binary_op_variant(*op, ty)?;
                    var_decls! { left: Bool, right: Bool };
                    let result =
                        vir_low::Expression::binary_op_no_pos(*op, expr! {left}, expr! {right});
                    self.declare_simplification_axiom(ty, &variant, vec![left, right], ty, result)?;
                }
            }
            vir_mid::Type::Int(_) => {
                let variant = self.encode_unary_op_variant(vir_low::UnaryOpKind::Minus, ty)?;
                var_decls! { constant: Int };
                let result = expr! { -constant };
                self.declare_simplification_axiom(ty, &variant, vec![constant], ty, result)?;
                for op in ARITHMETIC_OPERATORS {
                    let variant = self.encode_binary_op_variant(*op, ty)?;
                    var_decls! { left: Int, right: Int };
                    let result =
                        vir_low::Expression::binary_op_no_pos(*op, expr! {left}, expr! {right});
                    self.declare_simplification_axiom(ty, &variant, vec![left, right], ty, result)?;
                }
                // FIXME: This should be more fine grained instead of including all Bool axioms.
                self.ensure_type_definition(&vir_mid::Type::Bool)?;
                for op in COMPARISON_OPERATORS {
                    let variant = self.encode_binary_op_variant(*op, ty)?;
                    var_decls! { left: Int, right: Int };
                    let result =
                        vir_low::Expression::binary_op_no_pos(*op, expr! {left}, expr! {right});
                    self.declare_simplification_axiom(
                        &vir_mid::Type::Bool,
                        &variant,
                        vec![left, right],
                        ty,
                        result,
                    )?;
                }
            }
            _ => {
                // Other types do not need simplification axioms.
            }
        }
        Ok(())
    }
}

pub(in super::super) trait TypesInterface {
    /// Ensure that all encoders know the necessary information to encode the
    /// uses of this type that require its definition.
    fn ensure_type_definition(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_unary_op_variant(
        &mut self,
        op: vir_low::UnaryOpKind,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<String>;
    fn encode_binary_op_variant(
        &mut self,
        op: vir_low::BinaryOpKind,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<String>;
    fn decode_type_low_into_mid(&self, ty: &vir_low::Type) -> SpannedEncodingResult<vir_mid::Type>;
}

impl<'p, 'v: 'p, 'tcx: 'v> TypesInterface for Lowerer<'p, 'v, 'tcx> {
    fn ensure_type_definition(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
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
        op: vir_low::UnaryOpKind,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("{}_{}", op, ty.get_identifier()))
    }
    fn encode_binary_op_variant(
        &mut self,
        op: vir_low::BinaryOpKind,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("{}_{}", op, ty.get_identifier()))
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
