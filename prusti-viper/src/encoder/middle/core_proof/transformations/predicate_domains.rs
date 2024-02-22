use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    common::{
        expression::{
            BinaryOperationHelpers, ExpressionIterator, QuantifierHelpers, UnaryOperationHelpers,
        },
        graphviz::ToGraphviz,
    },
    low::{
        self as vir_low,
        ast::statement::visitors::StatementFolder,
        expression::visitors::{default_fold_container_op, ExpressionFolder},
        operations::ty::Typed,
        ty::visitors::TypeFolder,
    },
};

use crate::encoder::middle::core_proof::predicates::OwnedPredicateInfo;

pub(crate) type PredicateDomainsInfo = FxHashMap<String, PredicateDomainInfo>;

pub(crate) struct PredicateDomainInfo {
    pub(crate) permission_domain_name: String,
    pub(crate) permission_amount_type: vir_low::Type,
    pub(crate) permission_lookup_function_name: String,
    pub(crate) permission_set_full_function_name: String,
    pub(crate) permission_set_none_function_name: String,
    pub(crate) heap_domain_name: String,
    pub(crate) heap_snapshot_type: vir_low::Type,
    pub(crate) heap_lookup_function_name: String,
}

impl PredicateDomainInfo {
    pub(crate) fn permission_mask_type(&self) -> vir_low::Type {
        vir_low::Type::domain(self.permission_domain_name.clone())
    }

    pub(crate) fn create_permission_mask_variable(&self, name: String) -> vir_low::VariableDecl {
        vir_low::VariableDecl::new(name, self.permission_mask_type())
    }

    fn set_permissions(
        &self,
        setter: &str,
        old_permission_mask: &vir_low::VariableDecl,
        new_permission_mask: &vir_low::VariableDecl,
        predicate_arguments: &[vir_low::Expression],
    ) -> vir_low::Expression {
        let mut arguments = Vec::with_capacity(2 + predicate_arguments.len());
        arguments.push(old_permission_mask.clone().into());
        arguments.push(new_permission_mask.clone().into());
        arguments.extend(predicate_arguments.iter().cloned());
        vir_low::Expression::domain_function_call(
            self.permission_domain_name.clone(),
            setter.to_string(),
            arguments,
            vir_low::Type::Bool,
        )
    }

    pub(crate) fn set_permissions_to_full(
        &self,
        old_permission_mask: &vir_low::VariableDecl,
        new_permission_mask: &vir_low::VariableDecl,
        predicate_arguments: &[vir_low::Expression],
    ) -> vir_low::Expression {
        self.set_permissions(
            &self.permission_set_full_function_name,
            old_permission_mask,
            new_permission_mask,
            predicate_arguments,
        )
    }

    pub(crate) fn set_permissions_to_none(
        &self,
        old_permission_mask: &vir_low::VariableDecl,
        new_permission_mask: &vir_low::VariableDecl,
        predicate_arguments: &[vir_low::Expression],
    ) -> vir_low::Expression {
        self.set_permissions(
            &self.permission_set_none_function_name,
            old_permission_mask,
            new_permission_mask,
            predicate_arguments,
        )
    }

    fn lookup_permission(
        &self,
        permission_mask: &vir_low::VariableDecl,
        predicate_arguments: &[vir_low::VariableDecl],
    ) -> vir_low::Expression {
        let mut arguments = Vec::with_capacity(1 + predicate_arguments.len());
        arguments.push(permission_mask.clone().into());
        arguments.extend(
            predicate_arguments
                .iter()
                .cloned()
                .map(|parameter| parameter.into()),
        );
        vir_low::Expression::domain_function_call(
            self.permission_domain_name.clone(),
            self.permission_lookup_function_name.clone(),
            arguments,
            self.permission_amount_type.clone(),
        )
    }

    pub(crate) fn check_permissions_full(
        &self,
        permission_mask: &vir_low::VariableDecl,
        predicate_arguments: &[vir_low::Expression],
    ) -> vir_low::Expression {
        let mut arguments = Vec::with_capacity(1 + predicate_arguments.len());
        arguments.push(permission_mask.clone().into());
        arguments.extend(predicate_arguments.iter().cloned());
        let lookup_permission = vir_low::Expression::domain_function_call(
            self.permission_domain_name.clone(),
            self.permission_lookup_function_name.clone(),
            arguments,
            self.permission_amount_type.clone(),
        );
        lookup_permission
    }

    pub(crate) fn heap_type(&self) -> vir_low::Type {
        vir_low::Type::domain(self.heap_domain_name.clone())
    }

    pub(crate) fn create_heap_variable(&self, name: String) -> vir_low::VariableDecl {
        vir_low::VariableDecl::new(name, self.heap_type())
    }

    pub(crate) fn lookup_snapshot(
        &self,
        heap: &vir_low::VariableDecl,
        predicate_arguments: &[vir_low::Expression],
    ) -> vir_low::Expression {
        let mut arguments = Vec::with_capacity(1 + predicate_arguments.len());
        arguments.push(heap.clone().into());
        arguments.extend(predicate_arguments.iter().cloned());
        vir_low::Expression::domain_function_call(
            self.heap_domain_name.clone(),
            self.heap_lookup_function_name.clone(),
            arguments,
            self.heap_snapshot_type.clone(),
        )
    }
}

pub(in super::super) fn define_predicate_domains(
    source_filename: &str,
    mut program: vir_low::Program,
    owned_predicate_info: &BTreeMap<String, OwnedPredicateInfo>,
) -> (vir_low::Program, PredicateDomainsInfo) {
    let mut domains_info = FxHashMap::default();
    for predicate in &program.predicates {
        match predicate.kind {
            vir_low::PredicateKind::MemoryBlock => {
                define_predicate_domain_for_boolean_mask(
                    &mut program.domains,
                    &mut domains_info,
                    predicate,
                    vir_low::macros::ty!(Bytes),
                );
            }
            vir_low::PredicateKind::Owned => {
                define_predicate_domain_for_boolean_mask(
                    &mut program.domains,
                    &mut domains_info,
                    predicate,
                    owned_predicate_info
                        .get(&predicate.name)
                        .unwrap()
                        .snapshot_type
                        .clone(),
                );
            }
            vir_low::PredicateKind::LifetimeToken => {
                // Lifetime tokens require no additional axioms.
            }
            vir_low::PredicateKind::CloseFracRef => todo!(),
            vir_low::PredicateKind::WithoutSnapshotWhole => todo!(),
            vir_low::PredicateKind::WithoutSnapshotWholeNonAliased => todo!(),
            vir_low::PredicateKind::DeadLifetimeToken => {
                // Dead lifetime tokens require no additional axioms.
            }
            vir_low::PredicateKind::EndBorrowViewShift => todo!(),
        }
    }
    (program, domains_info)
}

fn define_predicate_domain_for_boolean_mask(
    domains: &mut Vec<vir_low::DomainDecl>,
    domains_info: &mut PredicateDomainsInfo,
    predicate: &vir_low::PredicateDecl,
    snapshot_type: vir_low::Type,
) {
    let predicate_info = PredicateDomainInfo {
        permission_domain_name: format!("{}$Perm", predicate.name),
        permission_amount_type: vir_low::Type::Bool,
        permission_lookup_function_name: format!("{}$perm", predicate.name),
        permission_set_full_function_name: format!("{}$set_write", predicate.name),
        permission_set_none_function_name: format!("{}$set_none", predicate.name),
        heap_domain_name: format!("{}$Heap", predicate.name),
        heap_snapshot_type: snapshot_type,
        heap_lookup_function_name: format!("{}$lookup", predicate.name),
    };

    let permission_domain = create_permission_domain_for_boolean_mask(predicate, &predicate_info);
    let heap_domain = create_heap_domain_for_boolean_mask(predicate, &predicate_info);

    domains.push(permission_domain);
    domains.push(heap_domain);
    assert!(domains_info
        .insert(predicate.name.clone(), predicate_info)
        .is_none());
}

fn create_permission_domain_for_boolean_mask(
    predicate: &vir_low::PredicateDecl,
    predicate_info: &PredicateDomainInfo,
) -> vir_low::DomainDecl {
    use vir_low::macros::*;

    let mask = predicate_info.create_permission_mask_variable("mask".to_string());
    let mut lookup_parameters = Vec::with_capacity(1 + predicate.parameters.len());
    lookup_parameters.push(mask.clone());
    lookup_parameters.extend(predicate.parameters.iter().cloned());
    let lookup = vir_low::DomainFunctionDecl::new(
        predicate_info.permission_lookup_function_name.clone(),
        false,
        lookup_parameters,
        predicate_info.permission_amount_type.clone(),
    );

    let old_mask = predicate_info.create_permission_mask_variable("old_mask".to_string());
    let new_mask = predicate_info.create_permission_mask_variable("new_mask".to_string());
    let mut set_full_parameters = Vec::with_capacity(2 + predicate.parameters.len());
    set_full_parameters.push(old_mask.clone());
    set_full_parameters.push(new_mask.clone());
    set_full_parameters.extend(predicate.parameters.iter().cloned());
    let set_full = vir_low::DomainFunctionDecl::new(
        predicate_info.permission_set_full_function_name.clone(),
        false,
        set_full_parameters.clone(),
        vir_low::Type::Bool,
    );

    let set_full_axiom = {
        let old_lookup = predicate_info.lookup_permission(&old_mask, &predicate.parameters);
        let new_lookup = predicate_info.lookup_permission(&new_mask, &predicate.parameters);

        let set_full_arguments = set_full_parameters
            .iter()
            .map(|parameter| parameter.clone().into())
            .collect();
        let set_full_call = vir_low::Expression::domain_function_call(
            predicate_info.permission_domain_name.clone(),
            predicate_info.permission_set_full_function_name.clone(),
            set_full_arguments,
            vir_low::Type::Bool,
        );

        let other_preserved = {
            let parameters_nested: Vec<_> = predicate
                .parameters
                .iter()
                .map(|parameter| {
                    vir_low::VariableDecl::new(
                        format!("{}$nested", parameter.name),
                        parameter.ty.clone(),
                    )
                })
                .collect();
            let old_lookup_nested = predicate_info.lookup_permission(&old_mask, &parameters_nested);
            let new_lookup_nested = predicate_info.lookup_permission(&new_mask, &parameters_nested);

            vir_low::Expression::forall(
                parameters_nested,
                vec![vir_low::Trigger::new(vec![new_lookup_nested.clone()])],
                expr! { [old_lookup_nested] ==> [new_lookup_nested] },
            )
        };

        let set_full_definition = expr! {
            (![old_lookup]) &&
            [new_lookup] &&
            [other_preserved]
        };

        let axiom_body = vir_low::Expression::forall(
            set_full_parameters,
            vec![vir_low::Trigger::new(vec![set_full_call.clone()])],
            expr! { [set_full_call] == [set_full_definition]},
        );

        vir_low::DomainAxiomDecl::new(
            None,
            format!("{}$definitional_axiom", lookup.name),
            axiom_body,
        )
    };

    let mut set_none_parameters = Vec::with_capacity(2 + predicate.parameters.len());
    set_none_parameters.push(old_mask.clone());
    set_none_parameters.push(new_mask.clone());
    set_none_parameters.extend(predicate.parameters.iter().cloned());
    let set_none = vir_low::DomainFunctionDecl::new(
        predicate_info.permission_set_none_function_name.clone(),
        false,
        set_none_parameters.clone(),
        vir_low::Type::Bool,
    );

    let set_none_axiom = {
        let set_none_arguments = set_none_parameters
            .iter()
            .map(|parameter| parameter.clone().into())
            .collect();
        let set_none_call = vir_low::Expression::domain_function_call(
            predicate_info.permission_domain_name.clone(),
            predicate_info.permission_set_none_function_name.clone(),
            set_none_arguments,
            vir_low::Type::Bool,
        );

        let set_none_definition = {
            let parameters_nested: Vec<_> = predicate
                .parameters
                .iter()
                .map(|parameter| {
                    vir_low::VariableDecl::new(
                        format!("{}$nested", parameter.name),
                        parameter.ty.clone(),
                    )
                })
                .collect();
            let old_lookup_nested = predicate_info.lookup_permission(&old_mask, &parameters_nested);
            let new_lookup_nested = predicate_info.lookup_permission(&new_mask, &parameters_nested);
            let arguments_equal = predicate
                .parameters
                .iter()
                .zip(parameters_nested.iter())
                .map(|(parameter, parameter_nested)| {
                    expr! { parameter == parameter_nested }
                })
                .conjoin();

            vir_low::Expression::forall(
                parameters_nested,
                vec![vir_low::Trigger::new(vec![new_lookup_nested.clone()])],
                vir_low::Expression::conditional_no_pos(
                    arguments_equal,
                    expr! { ![new_lookup_nested.clone()] },
                    expr! { [old_lookup_nested] == [new_lookup_nested] },
                ),
            )
        };

        let axiom_body = vir_low::Expression::forall(
            set_none_parameters,
            vec![vir_low::Trigger::new(vec![set_none_call.clone()])],
            expr! { [set_none_call] == [set_none_definition]},
        );

        vir_low::DomainAxiomDecl::new(
            None,
            format!("{}$definitional_axiom", lookup.name),
            axiom_body,
        )
    };

    let functions = vec![lookup, set_full, set_none];
    let axioms = vec![set_full_axiom, set_none_axiom];
    vir_low::DomainDecl::new(
        predicate_info.permission_domain_name.clone(),
        functions,
        axioms,
        Vec::new(),
    )
}

fn create_heap_domain_for_boolean_mask(
    predicate: &vir_low::PredicateDecl,
    predicate_info: &PredicateDomainInfo,
) -> vir_low::DomainDecl {
    let heap = predicate_info.create_heap_variable("heap".to_string());
    let mut lookup_parameters = Vec::with_capacity(1 + predicate.parameters.len());
    lookup_parameters.push(heap.clone());
    lookup_parameters.extend(predicate.parameters.iter().cloned());
    let lookup = vir_low::DomainFunctionDecl::new(
        predicate_info.heap_lookup_function_name.clone(),
        false,
        lookup_parameters,
        predicate_info.heap_snapshot_type.clone(),
    );

    let functions = vec![lookup];
    vir_low::DomainDecl::new(
        predicate_info.heap_domain_name.clone(),
        functions,
        Vec::new(),
        Vec::new(),
    )
}
