use crate::encoder::middle::core_proof::{
    predicates::{OwnedPredicateInfo, SnapshotFunctionInfo},
    snapshots::{SnapshotDomainInfo, SnapshotDomainsInfo},
    transformations::encoder_context::EncoderContext,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::BTreeMap;
use vir_crate::{
    common::builtin_constants::MEMORY_BLOCK_PREDICATE_NAME,
    low::{self as vir_low, operations::ty::Typed},
};

pub(super) struct ProgramContext<'a, EC: EncoderContext> {
    domains: &'a [vir_low::DomainDecl],
    domain_functions: FxHashMap<String, &'a vir_low::DomainFunctionDecl>,
    functions: FxHashMap<String, &'a vir_low::FunctionDecl>,
    predicate_decls: FxHashMap<String, &'a vir_low::PredicateDecl>,
    snapshot_functions_to_predicates: BTreeMap<String, String>,
    predicates_to_snapshot_functions: BTreeMap<String, String>,
    predicates_to_snapshot_types: BTreeMap<String, vir_low::Type>,
    non_aliased_memory_block_addresses: &'a FxHashSet<vir_low::Expression>,
    snapshot_domains_info: &'a SnapshotDomainsInfo,
    constant_constructor_names: FxHashSet<String>,
    extensionality_gas_constant: &'a vir_low::Expression,
    encoder: &'a mut EC,
}

impl<'a, EC: EncoderContext> ProgramContext<'a, EC> {
    pub(super) fn new(
        domains: &'a [vir_low::DomainDecl],
        functions: &'a [vir_low::FunctionDecl],
        predicate_decls: &'a [vir_low::PredicateDecl],
        snapshot_domains_info: &'a SnapshotDomainsInfo,
        predicate_info: BTreeMap<String, OwnedPredicateInfo>,
        non_aliased_memory_block_addresses: &'a FxHashSet<vir_low::Expression>,
        extensionality_gas_constant: &'a vir_low::Expression,
        encoder: &'a mut EC,
    ) -> Self {
        let mut snapshot_functions_to_predicates = BTreeMap::new();
        let mut predicates_to_snapshot_functions = BTreeMap::new();
        let mut predicates_to_snapshot_types = BTreeMap::new();
        for (
            predicate_name,
            OwnedPredicateInfo {
                current_snapshot_function: SnapshotFunctionInfo { function_name, .. },
                // We are not purifying the final snapshot function because it
                // is already pure.
                final_snapshot_function: _,
                snapshot_type,
            },
        ) in predicate_info
        {
            snapshot_functions_to_predicates.insert(function_name.clone(), predicate_name.clone());
            predicates_to_snapshot_functions.insert(predicate_name.clone(), function_name);
            predicates_to_snapshot_types.insert(predicate_name, snapshot_type);
        }
        for function in functions {
            if function.kind == vir_low::FunctionKind::MemoryBlockBytes {
                let predicate_name = MEMORY_BLOCK_PREDICATE_NAME;
                assert!(predicates_to_snapshot_functions
                    .insert(predicate_name.to_string(), function.name.clone())
                    .is_none());
            }
        }
        Self {
            constant_constructor_names: snapshot_domains_info
                .snapshot_domains
                .values()
                .flat_map(|domain| domain.constant_constructor_name.clone())
                .collect(),
            domain_functions: domains
                .iter()
                .flat_map(|domain| {
                    domain
                        .functions
                        .iter()
                        .map(move |function| (function.name.clone(), function))
                })
                .collect(),
            domains,
            snapshot_functions_to_predicates,
            predicates_to_snapshot_functions,
            predicates_to_snapshot_types,
            functions: functions
                .iter()
                .map(|function| (function.name.clone(), function))
                .collect(),
            predicate_decls: predicate_decls
                .iter()
                .map(|predicate| (predicate.name.clone(), predicate))
                .collect(),
            non_aliased_memory_block_addresses,
            snapshot_domains_info,
            extensionality_gas_constant,
            encoder,
        }
    }

    pub(super) fn get_domains(&self) -> &'a [vir_low::DomainDecl] {
        self.domains
    }

    pub(super) fn get_function(&self, name: &str) -> &'a vir_low::FunctionDecl {
        self.functions
            .get(name)
            .unwrap_or_else(|| panic!("Function not found: {}", name,))
    }

    pub(super) fn get_snapshot_type(&self, predicate_name: &str) -> Option<vir_low::Type> {
        // FIXME: Code duplication with
        // prusti-viper/src/encoder/middle/core_proof/transformations/custom_heap_encoding/heap_encoder/predicates.rs
        let predicate = self.predicate_decls[predicate_name];
        match predicate.kind {
            vir_low::PredicateKind::MemoryBlock => {
                use vir_low::macros::*;
                Some(ty!(Bytes))
            }
            vir_low::PredicateKind::Owned => Some(
                self.predicates_to_snapshot_types
                    .get(predicate_name)
                    .unwrap_or_else(|| unreachable!("predicate not found: {}", predicate_name))
                    .clone(),
            ),
            vir_low::PredicateKind::CloseFracRef
            | vir_low::PredicateKind::LifetimeToken
            | vir_low::PredicateKind::WithoutSnapshotWhole
            | vir_low::PredicateKind::WithoutSnapshotWholeNonAliased
            // | vir_low::PredicateKind::WithoutSnapshotFrac
            | vir_low::PredicateKind::DeadLifetimeToken
            | vir_low::PredicateKind::EndBorrowViewShift => None,
        }
    }

    pub(super) fn get_snapshot_predicate(&self, function_name: &str) -> Option<&str> {
        let function = self.get_function(function_name);
        match function.kind {
            vir_low::FunctionKind::MemoryBlockBytes => Some(MEMORY_BLOCK_PREDICATE_NAME),
            vir_low::FunctionKind::CallerFor => todo!(),
            vir_low::FunctionKind::SnapRange => todo!(),
            vir_low::FunctionKind::Snap => self
                .snapshot_functions_to_predicates
                .get(function_name)
                .map(|s| s.as_str()),
        }
    }

    pub(super) fn get_predicate_snapshot_function(&self, predicate_name: &str) -> &str {
        &self
            .predicates_to_snapshot_functions
            .get(predicate_name)
            .unwrap_or_else(|| panic!("Predicate snapshot function not found: {}", predicate_name))
    }

    pub(super) fn get_non_aliased_memory_block_addresses(
        &self,
    ) -> &'a FxHashSet<vir_low::Expression> {
        self.non_aliased_memory_block_addresses
    }

    pub(super) fn get_predicate_kind(&self, predicate_name: &str) -> vir_low::PredicateKind {
        self.predicate_decls[predicate_name].kind
    }

    pub(super) fn is_predicate_kind_non_aliased(&self, predicate_name: &str) -> bool {
        self.predicate_decls
            .get(predicate_name)
            .unwrap_or_else(|| panic!("{predicate_name}"))
            .kind
            .is_non_aliased()
    }

    pub(super) fn get_binary_operator(
        &self,
        snapshot_domain_name: &str,
        function_name: &str,
    ) -> Option<vir_low::BinaryOpKind> {
        self.snapshot_domains_info
            .snapshot_domains
            .get(snapshot_domain_name)
            .and_then(|snapshot_domain| {
                snapshot_domain.binary_operators.get(function_name).cloned()
            })
    }

    pub(super) fn get_constant_constructor(
        &self,
        snapshot_domain_name: &str,
    ) -> &'a vir_low::DomainFunctionDecl {
        let constructor_name = self
            .snapshot_domains_info
            .snapshot_domains
            .get(snapshot_domain_name)
            .unwrap()
            .constant_constructor_name
            .as_ref()
            .unwrap_or_else(|| panic!("not found: {snapshot_domain_name}"));
        self.domain_functions[constructor_name]
    }

    pub(super) fn get_constant_destructor(
        &self,
        snapshot_domain_name: &str,
    ) -> &vir_low::DomainFunctionDecl {
        let destructor_name = self
            .snapshot_domains_info
            .snapshot_domains
            .get(snapshot_domain_name)
            .unwrap()
            .constant_destructor_name
            .as_ref()
            .unwrap_or_else(|| panic!("not found: {snapshot_domain_name}"));
        self.domain_functions[destructor_name]
    }

    pub(super) fn get_constant_constructor_names(&self) -> &FxHashSet<String> {
        &self.constant_constructor_names
    }

    pub(super) fn predicate_snapshots_extensionality_call(
        &self,
        left: vir_low::Expression,
        right: vir_low::Expression,
        position: vir_low::Position,
    ) -> vir_low::Expression {
        let domain_name = self
            .snapshot_domains_info
            .type_domains
            .get(left.get_type())
            .unwrap_or_else(|| panic!("not found: {}", left.get_type()));
        let function_name = self
            .snapshot_domains_info
            .snapshot_domains
            .get(domain_name)
            .unwrap_or_else(|| panic!("not found: {}", domain_name))
            .snapshot_equality
            .as_ref()
            .unwrap_or_else(|| panic!("not found: {}", domain_name));
        vir_low::Expression::domain_function_call(
            domain_name,
            function_name,
            vec![left, right, self.extensionality_gas_constant.clone()],
            vir_low::Type::Bool,
        )
        .set_default_position(position)
    }

    pub(super) fn get_bool_domain_info(&self) -> (vir_low::Type, SnapshotDomainInfo) {
        let bool_type = self
            .snapshot_domains_info
            .bool_type
            .as_ref()
            .unwrap()
            .clone();
        let bool_domain = &self.snapshot_domains_info.type_domains[&bool_type];
        let domain_info = self.snapshot_domains_info.snapshot_domains[bool_domain].clone();
        (bool_type, domain_info)
    }

    pub(super) fn env(&mut self) -> &mut impl EncoderContext {
        self.encoder
    }

    pub(super) fn is_place_option_type(&self, ty: &vir_low::Type) -> bool {
        match ty {
            vir_low::Type::Domain(vir_low::ty::Domain { name })
                if name == vir_crate::common::builtin_constants::PLACE_OPTION_DOMAIN_NAME =>
            {
                true
            }
            _ => false,
        }
    }

    pub(super) fn is_address_type(&self, ty: &vir_low::Type) -> bool {
        match ty {
            vir_low::Type::Domain(vir_low::ty::Domain { name })
                if name == vir_crate::common::builtin_constants::ADDRESS_DOMAIN_NAME =>
            {
                true
            }
            _ => false,
        }
    }

    pub(super) fn is_lifetime_type(&self, ty: &vir_low::Type) -> bool {
        match ty {
            vir_low::Type::Domain(vir_low::ty::Domain { name })
                if name == vir_crate::common::builtin_constants::LIFETIME_DOMAIN_NAME =>
            {
                true
            }
            _ => false,
        }
    }

    pub(super) fn is_bytes_type(&self, ty: &vir_low::Type) -> bool {
        match ty {
            vir_low::Type::Domain(vir_low::ty::Domain { name })
                if name == vir_crate::common::builtin_constants::BYTES_DOMAIN_NAME =>
            {
                true
            }
            _ => false,
        }
    }

    // pub(super) fn get_bytes_base<'e>(&self, expression: &'e vir_low::Expression) -> Option<&'e vir_low::VariableDecl> {
    //     match expression {
    //         vir_low::Expression::Local(expression) if self.is_bytes_type(&expression.variable.ty)=> {
    //             Some(&expression.variable)
    //         }
    //         vir_low::Expression::DomainFuncApp(expression) if expression.arguments.len() == 1 => {
    //             // FIXME: Properly check that I am using only destructors and constructors.
    //             self.get_bytes_base(&expression.arguments[0])
    //         },
    //         _ => None,
    //     }
    // }

    pub(super) fn is_place_non_aliased(&self, place: &vir_low::Expression) -> bool {
        assert_eq!(place.get_type(), &vir_low::macros::ty!(PlaceOption));
        match place {
            vir_low::Expression::DomainFuncApp(domain_func_app)
                if domain_func_app.arguments.len() == 1 =>
            {
                let argument = &domain_func_app.arguments[0];
                if domain_func_app.function_name == "place_option_some" {
                    true
                } else {
                    self.is_place_non_aliased(argument)
                }
            }
            vir_low::Expression::DomainFuncApp(domain_func_app) => {
                assert_eq!(domain_func_app.function_name, "place_option_none");
                false
            }
            // vir_low::Expression::LabelledOld(labelled_old) => self.is_place_non_aliased(&labelled_old.base),
            _ => unreachable!("place: {place}"),
        }
    }

    pub(super) fn is_address_non_aliased(&self, address: &vir_low::Expression) -> bool {
        assert_eq!(address.get_type(), &vir_low::macros::ty!(Address));
        if self.non_aliased_memory_block_addresses.contains(address) {
            true
        } else {
            match address {
                vir_low::Expression::DomainFuncApp(domain_func_app)
                    if domain_func_app.arguments.len() == 1 =>
                {
                    if domain_func_app.function_name.starts_with("field_address$") {
                        // FIXME: Instead of using a string match, lookup in the
                        // context.
                        self.is_address_non_aliased(&domain_func_app.arguments[0])
                    } else if domain_func_app
                        .function_name
                        .starts_with("variant_address$")
                    {
                        // FIXME: Instead of using a string match, lookup in the
                        // context.
                        self.is_address_non_aliased(&domain_func_app.arguments[0])
                    } else if domain_func_app
                        .function_name
                        .starts_with("destructor$Snap$ref$Unique$")
                    {
                        false
                    } else if domain_func_app
                        .function_name
                        .starts_with("destructor$Snap$ref$Shared$")
                    {
                        false
                    } else if domain_func_app
                        .function_name
                        .starts_with("destructor$Snap$ptr$")
                    {
                        false
                    } else {
                        unreachable!("address: {domain_func_app}")
                    }
                }
                _ => unreachable!("address: {address}"),
            }
        }
    }
}
