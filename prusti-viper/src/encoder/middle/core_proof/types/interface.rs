//! A module that defines axioms for a specific type.
//!
//! ## Simplification and evaluation axioms
//!
//! ``simplification_axiom`` and ``eval_axiom`` should always terminate because:
//!
//! 1. They triggers require a term that contains the alternaive constructor.
//! 2. The term used in the trigger is equated to a strictly simpler term.
//! 3. The terms that are produced by applying the quantifier are only
//!    constructors of constants, which can trigger only validity and
//!    injectivity axioms.

use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        footprint::{DerefOwned, DerefOwnedRange, FootprintInterface},
        lowerer::{DomainsLowererInterface, Lowerer},
        snapshots::{
            IntoPureSnapshot, IntoSnapshot, IntoSnapshotLowerer, SnapshotAdtsInterface,
            SnapshotDomainsInterface, SnapshotValidityInterface, SnapshotValuesInterface,
            ValidityAssertionToSnapshot,
        },
        type_layouts::TypeLayoutsInterface,
    },
};
use prusti_common::config;
use rustc_hash::FxHashSet;
use std::collections::BTreeSet;
use vir_crate::{
    common::{
        expression::{ExpressionIterator, QuantifierHelpers},
        identifier::WithIdentifier,
    },
    low::{self as vir_low},
    middle::{self as vir_mid},
};

#[derive(Default)]
pub(in super::super) struct TypesState {
    /// The types for which the definitions were ensured.
    ensured_definitions: BTreeSet<String>,
    encoded_binary_operations: FxHashSet<String>,
    encoded_unary_operations: FxHashSet<String>,
}

// trait Private {
//     fn ensure_type_definition_for_decl(
//         &mut self,
//         ty: &vir_mid::Type,
//         type_decl: &vir_mid::TypeDecl,
//     ) -> SpannedEncodingResult<()>;
//     fn declare_simplification_axiom(
//         &mut self,
//         ty: &vir_mid::Type,
//         variant: &str,
//         parameters: Vec<vir_low::VariableDecl>,
//         parameter_type: &vir_mid::Type,
//         simplification_result: vir_low::Expression,
//     ) -> SpannedEncodingResult<()>;
//     fn declare_evaluation_axiom(
//         &mut self,
//         ty: &vir_mid::Type,
//         variant: &str,
//         parameters: Vec<vir_low::VariableDecl>,
//         evaluation_result: vir_low::Expression,
//     ) -> SpannedEncodingResult<()>;
//     // fn purify_structural_invariant(
//     //     &mut self,
//     //     structural_invariant: Vec<vir_mid::Expression>,
//     //     field_count: usize,
//     // ) -> SpannedEncodingResult<Vec<vir_mid::Expression>>;
// }

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
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
            vir_mid::TypeDecl::Trusted(_) => {
                // FIXME: ensure type definition for trusted
            }
            vir_mid::TypeDecl::TypeVar(_decl) => {
                // FIXME: we should make sure that the snapshot and validity
                // function is generated, but nothing else.
            }
            vir_mid::TypeDecl::Map(_) => {
                // FIXME: we should generate validity and to_bytes functions.
                // The ghost containers should be valid iff the values they
                // contain are valid.
            }
            vir_mid::TypeDecl::Sequence(vir_mid::type_decl::Sequence { element_type, .. })
            | vir_mid::TypeDecl::Array(vir_mid::type_decl::Array { element_type, .. }) => {
                self.ensure_type_definition(element_type)?;
                let element_domain_name = &self.encode_snapshot_domain_name(element_type)?;
                let element_type_snapshot = element_type.to_snapshot(self)?;
                self.encode_validity_axioms_sequence(
                    ty,
                    &domain_name,
                    element_domain_name,
                    element_type_snapshot,
                )?;
            }
            vir_mid::TypeDecl::Struct(decl) => {
                let mut parameters = Vec::new();
                for field in decl.fields.iter() {
                    parameters.push(vir_low::VariableDecl::new(
                        field.name.clone(),
                        field.ty.to_snapshot(self)?,
                    ));
                }
                let parameters_with_validity = decl.fields.len();
                let invariant = if let Some(invariant) = &decl.structural_invariant {
                    let (deref_fields, deref_range_fields) =
                        self.structural_invariant_to_deref_fields(invariant)?;
                    for DerefOwned {
                        field_name,
                        field_type,
                        ..
                    } in &deref_fields
                    {
                        parameters.push(vir_low::VariableDecl::new(field_name, field_type.clone()));
                    }
                    for DerefOwnedRange {
                        field_name,
                        field_type,
                        ..
                    } in &deref_range_fields
                    {
                        parameters.push(vir_low::VariableDecl::new(field_name, field_type.clone()));
                    }
                    let mut validity_assertion_encoder =
                        ValidityAssertionToSnapshot::new((deref_fields, deref_range_fields));
                    // let invariant = self.structural_invariant_to_pure_expression(
                    //     invariant.clone(),
                    //     ty,
                    //     decl,
                    //     &mut parameters,
                    // )?;
                    let mut conjuncts = Vec::new();
                    for expression in invariant {
                        conjuncts.push(
                            validity_assertion_encoder
                                .expression_to_snapshot(self, expression, true)?,
                        );
                        // conjuncts.push(expression.to_pure_bool_expression(self)?);
                    }
                    conjuncts.into_iter().conjoin() //.remove_acc_predicates()
                } else {
                    true.into()
                };
                self.register_struct_constructor(&domain_name, parameters.clone())?;
                self.encode_validity_axioms_struct_with_invariant(
                    &domain_name,
                    parameters,
                    parameters_with_validity,
                    invariant,
                )?;
            }
            vir_mid::TypeDecl::Enum(decl) => {
                let mut variants = Vec::new();
                for (discriminant, variant) in decl.iter_discriminant_variants() {
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
                let position = vir_low::Position::default();
                self.ensure_type_definition(&decl.target_type)?;
                let address_type = self.address_type()?;
                let address = vir_low::VariableDecl::new("address", address_type);
                let mut parameters = vec![address.clone()];
                if decl.target_type.is_slice() {
                    let len_type = self.size_type()?;
                    parameters.push(vir_low::VariableDecl::new("len", len_type));
                }
                self.register_struct_constructor(&domain_name, parameters.clone())?;
                // self.register_constant_constructor(&domain_name, address_type.clone())?;
                let vir_mid::Type::Pointer(pointer_type) = ty else {
                    unreachable!()
                };
                // let size = self.encode_type_size_expression2(&pointer_type.target_type, type_decl)?;
                // let size_type_mid = self.size_type_mid()?;
                // let size_int =
                //     self.obtain_constant_value(&size_type_mid, size.clone(), position)?;
                // let is_address_zst = self.address_is_zst(address.clone().into(), position)?;
                // let invariant = expr! { [is_address_zst] == ([size_int] == [0.into()]) };
                let invariant = self.address_value_is_valid(address.clone().into(), &pointer_type.target_type, position)?;
                // self.encode_validity_axioms_primitive(&domain_name, address_type, invariant)?;
                let parameters_with_validity = parameters.len();
                // TODO: Add an uninterepreted function to mark the unknown part.
                self.encode_validity_axioms_struct_with_invariant(
                    &domain_name,
                    parameters,
                    parameters_with_validity,
                    invariant,
                )?;
            }
            vir_mid::TypeDecl::Reference(decl) => {
                self.ensure_type_definition(&decl.target_type)?;
                let target_type = decl.target_type.to_snapshot(self)?;
                if decl.uniqueness.is_unique() {
                    let mut parameters = vars! {
                        address: Address,
                        target_current: {target_type.clone()},
                        target_final: {target_type}
                    };
                    if decl.target_type.is_slice() {
                        let len_type = self.size_type()?;
                        parameters.push(vir_low::VariableDecl::new("len", len_type));
                    }
                    self.register_struct_constructor(&domain_name, parameters.clone())?;
                    self.encode_validity_axioms_struct(&domain_name, parameters)?;
                } else {
                    let mut parameters = vars! {
                        address: Address,
                        target_current: {target_type.clone()}
                    };
                    if decl.target_type.is_slice() {
                        let len_type = self.size_type()?;
                        parameters.push(vir_low::VariableDecl::new("len", len_type));
                    }
                    self.register_struct_constructor(&domain_name, parameters.clone())?;
                    self.encode_validity_axioms_struct(&domain_name, parameters)?;
                    let no_alloc_parameters = vars! { target_current: {target_type} };
                    self.register_alternative_constructor_with_injectivity_axioms(
                        &domain_name,
                        "no_alloc",
                        true,
                        no_alloc_parameters.clone(),
                    )?;
                    let parameters_with_validity = no_alloc_parameters.len();
                    self.encode_validity_axioms_struct_alternative_constructor(
                        &domain_name,
                        "no_alloc",
                        no_alloc_parameters,
                        parameters_with_validity,
                        true.into(),
                    )?;
                }
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
        let mut parameters_validity = Vec::new();
        for parameter in parameters.iter() {
            let constructor_call = self.snapshot_constructor_constant_call(
                &parameter_domain_name,
                vec![parameter.clone().into()],
            )?;
            constructor_calls.push(constructor_call.clone());
            parameters_validity
                .push(self.encode_snapshot_valid_call_for_type(constructor_call, parameter_type)?);
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
            expr! { [parameters_validity.into_iter().conjoin()] ==> ([op_constructor_call] == [constructor_call_op]) },
        );
        let axiom = vir_low::DomainAxiomDecl {
            comment: None,
            name: format!("{variant}$simplification_axiom"),
            body,
        };
        self.declare_axiom(&domain_name, axiom)?;
        Ok(())
    }

    fn declare_evaluation_axiom(
        &mut self,
        ty: &vir_mid::Type,
        variant: &str,
        parameters: Vec<vir_low::VariableDecl>,
        evaluation_result: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let op_constructor = vir_low::Expression::domain_function_call(
            &domain_name,
            self.snapshot_constructor_struct_alternative_name(&domain_name, variant)?,
            parameters
                .iter()
                .map(|parameter| parameter.clone().into())
                .collect(),
            ty.to_snapshot(self)?,
        );
        let destructor = self.obtain_constant_value(ty, op_constructor, Default::default())?;
        let body = vir_low::Expression::forall(
            parameters,
            vec![vir_low::Trigger::new(vec![destructor.clone()])],
            expr! { [destructor] == [evaluation_result] },
        );
        let axiom = vir_low::DomainAxiomDecl {
            comment: None,
            name: format!("{variant}$eval_axiom"),
            body,
        };
        if config::use_eval_axioms() {
            self.declare_axiom(&domain_name, axiom)?;
        }
        Ok(())
    }

    /// Encodes the following axiom:
    ///
    /// $$$
    /// (first * mul >= second * mul) == (first >= second)
    /// $$$
    ///
    /// This holds because we are dealing with unsigned integers.
    fn declare_usize_mul_simplification_axiom(
        &mut self,
        ty: &vir_mid::Type,
        variant: &str,
        first: vir_low::VariableDecl,
        second: vir_low::VariableDecl,
        mul: vir_low::VariableDecl,
        parameter_type: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let bool_domain_name = self.encode_snapshot_domain_name(&vir_mid::Type::Bool)?;
        let bool_type = vir_mid::Type::Bool.to_snapshot(self)?;
        let snapshot_type = ty.to_snapshot(self)?;
        let first_mul = vir_low::Expression::domain_function_call(
            &domain_name,
            self.snapshot_constructor_struct_alternative_name(&domain_name, variant)?,
            vec![first.clone().into(), mul.clone().into()],
            snapshot_type.clone(),
        );
        let second_mul = vir_low::Expression::domain_function_call(
            &domain_name,
            self.snapshot_constructor_struct_alternative_name(&domain_name, variant)?,
            vec![second.clone().into(), mul.clone().into()],
            snapshot_type,
        );
        // let body = vir_low::Expression::forall(
        //     vec![first, second, mul],
        //     vec![vir_low::Trigger::new(vec![source.clone()])],
        //     expr! { ([source] == [target]) },
        // );
        let ge_cmp_name =
            self.encode_binary_op_variant(vir_mid::BinaryOpKind::GeCmp, parameter_type)?;
        let le_cmp_name =
            self.encode_binary_op_variant(vir_mid::BinaryOpKind::LeCmp, parameter_type)?;
        {
            let source = vir_low::Expression::domain_function_call(
                &bool_domain_name,
                self.snapshot_constructor_struct_alternative_name(&bool_domain_name, &ge_cmp_name)?,
                vec![first_mul.clone(), second_mul.clone()],
                bool_type.clone(),
            );
            let target = vir_low::Expression::domain_function_call(
                &bool_domain_name,
                self.snapshot_constructor_struct_alternative_name(&bool_domain_name, &ge_cmp_name)?,
                vec![first.clone().into(), second.clone().into()],
                bool_type.clone(),
            );
            let axiom = vir_low::DomainRewriteRuleDecl {
                comment: None,
                name: format!("{variant}$simplification_axiom_ge_cmp"),
                variables: vec![first.clone(), second.clone(), mul.clone()],
                egg_only: true,
                triggers: None,
                source,
                target,
            };
            // self.declare_axiom(&domain_name, axiom)?;
            self.declare_rewrite_rule(&domain_name, axiom)?;
        }
        {
            let source = vir_low::Expression::domain_function_call(
                &bool_domain_name,
                self.snapshot_constructor_struct_alternative_name(&bool_domain_name, &le_cmp_name)?,
                vec![first_mul, second_mul],
                bool_type.clone(),
            );
            let target = vir_low::Expression::domain_function_call(
                &bool_domain_name,
                self.snapshot_constructor_struct_alternative_name(&bool_domain_name, &le_cmp_name)?,
                vec![first.clone().into(), second.clone().into()],
                bool_type.clone(),
            );
            let axiom = vir_low::DomainRewriteRuleDecl {
                comment: None,
                name: format!("{variant}$simplification_axiom_le_cmp"),
                variables: vec![first.clone(), second.clone(), mul],
                egg_only: true,
                triggers: None,
                source,
                target,
            };
            // self.declare_axiom(&domain_name, axiom)?;
            self.declare_rewrite_rule(&domain_name, axiom)?;
        }
        {
            let source = vir_low::Expression::domain_function_call(
                &bool_domain_name,
                self.snapshot_constructor_struct_alternative_name(&bool_domain_name, &le_cmp_name)?,
                vec![first.clone().into(), second.clone().into()],
                bool_type.clone(),
            );
            let target = vir_low::Expression::domain_function_call(
                &bool_domain_name,
                self.snapshot_constructor_struct_alternative_name(&bool_domain_name, &ge_cmp_name)?,
                vec![second.clone().into(), first.clone().into()],
                bool_type.clone(),
            );
            let axiom = vir_low::DomainRewriteRuleDecl {
                comment: None,
                name: format!("{variant}$simplification_axiom_le_ge_commute"),
                variables: vec![first.clone(), second.clone()],
                egg_only: true,
                triggers: None,
                source,
                target,
            };
            // self.declare_axiom(&domain_name, axiom)?;
            self.declare_rewrite_rule(&domain_name, axiom)?;
        }
        {
            let source = vir_low::Expression::domain_function_call(
                &bool_domain_name,
                self.snapshot_constructor_struct_alternative_name(&bool_domain_name, &ge_cmp_name)?,
                vec![first.clone().into(), second.clone().into()],
                bool_type.clone(),
            );
            let target = vir_low::Expression::domain_function_call(
                &bool_domain_name,
                self.snapshot_constructor_struct_alternative_name(&bool_domain_name, &le_cmp_name)?,
                vec![second.clone().into(), first.clone().into()],
                bool_type,
            );
            let axiom = vir_low::DomainRewriteRuleDecl {
                comment: None,
                name: format!("{variant}$simplification_axiom_ge_le_commute"),
                variables: vec![first, second],
                egg_only: true,
                triggers: None,
                source,
                target,
            };
            // self.declare_axiom(&domain_name, axiom)?;
            self.declare_rewrite_rule(&domain_name, axiom)?;
        }
        Ok(())
    }

    fn declare_commutativity_axiom(
        &mut self,
        ty: &vir_mid::Type,
        variant: &str,
        left: vir_low::VariableDecl,
        right: vir_low::VariableDecl,
    ) -> SpannedEncodingResult<()> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let op_constructor_1 = vir_low::Expression::domain_function_call(
            &domain_name,
            self.snapshot_constructor_struct_alternative_name(&domain_name, variant)?,
            vec![left.clone().into(), right.clone().into()],
            ty.to_snapshot(self)?,
        );
        let op_constructor_2 = vir_low::Expression::domain_function_call(
            &domain_name,
            self.snapshot_constructor_struct_alternative_name(&domain_name, variant)?,
            vec![right.clone().into(), left.clone().into()],
            ty.to_snapshot(self)?,
        );
        let axiom = vir_low::DomainRewriteRuleDecl {
            comment: None,
            name: format!("{variant}$commutativity_axiom"),
            egg_only: true,
            variables: vec![left, right],
            triggers: None,
            source: op_constructor_1,
            target: op_constructor_2,
        };
        self.declare_rewrite_rule(&domain_name, axiom)?;
        Ok(())
    }

    fn declare_zero_axioms(
        &mut self,
        op: vir_low::BinaryOpKind,
        ty: &vir_mid::Type,
        variant: &str,
        variable: vir_low::VariableDecl,
    ) -> SpannedEncodingResult<()> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let zero = self.construct_constant_snapshot(ty, 0.into(), Default::default())?;
        let (source, target) = match op {
            vir_low::BinaryOpKind::Add | vir_low::BinaryOpKind::Sub => {
                let source = vir_low::Expression::domain_function_call(
                    &domain_name,
                    self.snapshot_constructor_struct_alternative_name(&domain_name, variant)?,
                    vec![variable.clone().into(), zero],
                    ty.to_snapshot(self)?,
                );
                let target = variable.clone().into();
                (source, target)
            }
            vir_low::BinaryOpKind::Mul
            | vir_low::BinaryOpKind::Div
            | vir_low::BinaryOpKind::Mod => {
                let source = vir_low::Expression::domain_function_call(
                    &domain_name,
                    self.snapshot_constructor_struct_alternative_name(&domain_name, variant)?,
                    vec![zero.clone(), variable.clone().into()],
                    ty.to_snapshot(self)?,
                );
                let target = zero;
                (source, target)
            }
            _ => {
                return Ok(()); // No zero axiom for non-numeric operators.
            }
        };
        let axiom = vir_low::DomainRewriteRuleDecl {
            comment: None,
            name: format!("{variant}$zero_axiom"),
            egg_only: true,
            variables: vec![variable],
            triggers: None,
            source,
            target,
        };
        self.declare_rewrite_rule(&domain_name, axiom)?;
        Ok(())
    }

    // fn purify_structural_invariant(
    //     &mut self,
    //     structural_invariant: Vec<vir_mid::Expression>,
    //     field_count: usize,
    // ) -> SpannedEncodingResult<Vec<vir_mid::Expression>> {

    //     // TODO: Create deref fields in vir_high together with a required
    //     // structural invariant that links their values? Probably does not work
    //     // because I need different treatment in predicate and snapshot
    //     // encoders.

    //     // TODO: Maybe a better idea would be to have code that computes a
    //     // footprint of an expression? Then I could also use it for pure
    //     // functions.

    //     struct Purifier<'l, 'p, 'v, 'tcx> {
    //         lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
    //         field_count: usize,
    //     }
    //     impl<'l, 'p, 'v, 'tcx> vir_mid::visitors::ExpressionFolder for Purifier<'l, 'p, 'v, 'tcx> {
    //         fn fold_acc_predicate_enum(
    //             &mut self,
    //             acc_predicate: vir_mid::AccPredicate,
    //         ) -> vir_mid::Expression {
    //             match *acc_predicate.predicate {
    //                 vir_mid::Predicate::LifetimeToken(_) => {
    //                     unimplemented!()
    //                 }
    //                 vir_mid::Predicate::MemoryBlockStack(_)
    //                 | vir_mid::Predicate::MemoryBlockStackDrop(_)
    //                 | vir_mid::Predicate::MemoryBlockHeap(_)
    //                 | vir_mid::Predicate::MemoryBlockHeapDrop(_) => true.into(),
    //                 vir_mid::Predicate::OwnedNonAliased(predicate) => {
    //                     match predicate.place {
    //                         vir_mid::Expression::Deref(vir_mid::Deref {
    //                             base:
    //                                 box vir_mid::Expression::Field(vir_mid::Field {
    //                                     box base,
    //                                     field,
    //                                     ..
    //                                 }),
    //                             ty,
    //                             position,
    //                         }) => {
    //                             // let parameter = vir_mid::VariableDecl::new(
    //                             //     format!("{}$deref", field.name),
    //                             //     ty,
    //                             // );
    //                             let app = vir_mid::Expression::builtin_func_app(
    //                                 vir_mid::BuiltinFunc::IsValid,
    //                                 Vec::new(),
    //                                 vec![
    //                                     vir_mid::Expression::field(
    //                                         base,
    //                                         vir_mid::FieldDecl {
    //                                             name: format!("{}$deref", field.name),
    //                                             index: self.field_count,
    //                                             ty,
    //                                         },
    //                                         position,
    //                                     )],
    //                                 vir_mid::Type::Bool,
    //                                 position,
    //                             );
    //                             self.field_count += 1;
    //                             app
    //                             // self.lowerer.encode_snapshot_valid_call_for_type(parameter.into(), ty)?
    //                         }
    //                         _ => unimplemented!(),
    //                     }
    //                 }
    //             }
    //         }
    //     }
    //     let mut purifier = Purifier { lowerer: self, field_count };
    //     Ok(structural_invariant
    //         .into_iter()
    //         .map(|expression| purifier.fold_expression(expression))
    //         .collect())
    // }
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
        if matches!(
            ty,
            vir_mid::Type::MBool
                | vir_mid::Type::MInt
                | vir_mid::Type::MPerm
                | vir_mid::Type::Lifetime
                | vir_mid::Type::MByte
                | vir_mid::Type::MBytes
        ) {
            // Natively supported types, nothing to do.
            return Ok(());
        }
        // FIXME: We should avoid these copies in some smarter way.
        let ty_identifier = ty.get_identifier();
        if !self
            .types_state
            .ensured_definitions
            .contains(&ty_identifier)
        {
            // We insert before doing the actual work to break infinite
            // recursion.
            self.types_state.ensured_definitions.insert(ty_identifier);

            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            self.ensure_type_definition_for_decl(ty, &type_decl)?;
        }
        Ok(())
    }
    fn encode_unary_op_variant(
        &mut self,
        op_mid: vir_mid::UnaryOpKind,
        argument_type: &vir_mid::Type,
    ) -> SpannedEncodingResult<String> {
        let variant_name = format!("{}_{}", op_mid, argument_type.get_identifier());
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
            let op = op_mid.to_snapshot(self)?;
            self.register_alternative_constructor(
                &result_domain,
                &variant_name,
                Some(op),
                None,
                false,
                vars! { argument: {snapshot_type.clone()} },
            )?;
            // Simplification axioms.
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
                var_decls! { value: {snapshot_type}};
                let destructor_value = self.obtain_constant_value(
                    argument_type,
                    value.clone().into(),
                    Default::default(),
                )?;
                self.declare_evaluation_axiom(
                    result_type,
                    &variant_name,
                    vec![value],
                    vir_low::Expression::unary_op_no_pos(op, destructor_value),
                )?;
            }
        }
        Ok(variant_name)
    }
    fn encode_binary_op_variant(
        &mut self,
        op_mid: vir_mid::BinaryOpKind,
        argument_type: &vir_mid::Type,
    ) -> SpannedEncodingResult<String> {
        let variant_name = format!("{}_{}", op_mid, argument_type.get_identifier());
        // format!("{}_{}", op, argument_type.get_identifier());
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
            let result_type = op_mid.get_result_type(argument_type);
            let result_domain = self.encode_snapshot_domain_name(result_type)?;
            let op = op_mid.to_snapshot(self)?;
            self.register_alternative_constructor(
                &result_domain,
                &variant_name,
                None,
                Some(op),
                false,
                vars! { left: {snapshot_type.clone()}, right: {snapshot_type.clone()} },
            )?;
            // Simplification axioms.
            let constant_type = match argument_type {
                vir_mid::Type::Bool => Some(ty! { Bool }),
                vir_mid::Type::Int(_) => Some(ty! {Int}),
                vir_mid::Type::Pointer(_) => Some(ty!(Address)),
                _ => None,
            };
            if let Some(constant_type) = constant_type {
                var_decls! { left_const: {constant_type.clone()}, right_const: {constant_type} };
                let result = vir_low::Expression::binary_op_no_pos(
                    op,
                    expr! {left_const},
                    expr! {right_const},
                );
                var_decls! {left_snap: {snapshot_type.clone()}, right_snap: {snapshot_type.clone()}};
                let destructor_left = self.obtain_constant_value(
                    argument_type,
                    left_snap.clone().into(),
                    Default::default(),
                )?;
                let destructor_right = self.obtain_constant_value(
                    argument_type,
                    right_snap.clone().into(),
                    Default::default(),
                )?;
                self.declare_simplification_axiom(
                    result_type,
                    &variant_name,
                    vec![left_const, right_const],
                    argument_type,
                    result,
                )?;
                self.declare_evaluation_axiom(
                    result_type,
                    &variant_name,
                    vec![left_snap.clone(), right_snap.clone()],
                    vir_low::Expression::binary_op_no_pos(op, destructor_left, destructor_right),
                )?;
                if argument_type == &vir_mid::Type::Int(vir_mid::ty::Int::Usize)
                    && op == vir_low::BinaryOpKind::Mul
                {
                    var_decls! { mul_snap: {snapshot_type} };
                    self.declare_usize_mul_simplification_axiom(
                        result_type,
                        &variant_name,
                        left_snap.clone(),
                        right_snap.clone(),
                        mul_snap,
                        argument_type,
                    )?;
                }
                if matches!(op, vir_low::BinaryOpKind::Add | vir_low::BinaryOpKind::Mul) {
                    self.declare_commutativity_axiom(
                        result_type,
                        &variant_name,
                        left_snap.clone(),
                        right_snap,
                    )?;
                }
                self.declare_zero_axioms(op, result_type, &variant_name, left_snap)?;
            } else if op == vir_low::BinaryOpKind::EqCmp {
                // FIXME: For now, we treat Rust's == as bit equality.
                var_decls! { left: {snapshot_type.clone()}, right: {snapshot_type} };
                let domain_name = self.encode_snapshot_domain_name(&vir_mid::Type::Bool)?;
                let op_constructor_call = vir_low::Expression::domain_function_call(
                    &domain_name,
                    self.snapshot_constructor_struct_alternative_name(&domain_name, &variant_name)?,
                    vec![left.clone().into(), right.clone().into()],
                    result_type.to_snapshot(self)?,
                );
                let constructor_call_op = self.snapshot_constructor_constant_call(
                    &domain_name,
                    vec![expr! { left == right }],
                )?;
                let body = vir_low::Expression::forall(
                    vec![left, right],
                    vec![vir_low::Trigger::new(vec![op_constructor_call.clone()])],
                    expr! { [op_constructor_call] == [constructor_call_op] },
                );
                let axiom = vir_low::DomainAxiomDecl {
                    comment: None,
                    name: format!("{variant_name}$simplification_axiom"),
                    body,
                };
                self.declare_axiom(&domain_name, axiom)?;
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
