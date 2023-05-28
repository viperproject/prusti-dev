use super::{permission_mask::PredicatePermissionMaskKind, HeapEncoder};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::predicates::{OwnedPredicateInfo, SnapshotFunctionInfo},
};
use rustc_hash::FxHashMap;
use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

pub(super) struct Predicates<'p> {
    predicate_decls: FxHashMap<String, &'p vir_low::PredicateDecl>,
    snapshot_functions_to_predicates: BTreeMap<String, String>,
    predicates_to_snapshot_types: BTreeMap<String, vir_low::Type>,
}

impl<'p> Predicates<'p> {
    pub(super) fn new(
        predicate_decls: &'p [vir_low::PredicateDecl],
        predicate_info: BTreeMap<String, OwnedPredicateInfo>,
    ) -> Self {
        let mut snapshot_functions_to_predicates = BTreeMap::new();
        let mut predicates_to_snapshot_types = BTreeMap::new();
        for (
            predicate_name,
            OwnedPredicateInfo {
                current_snapshot_function: SnapshotFunctionInfo { function_name, .. },
                snapshot_type,
                ..
            },
        ) in predicate_info
        {
            snapshot_functions_to_predicates.insert(function_name, predicate_name.clone());
            predicates_to_snapshot_types.insert(predicate_name, snapshot_type);
        }
        Self {
            predicate_decls: predicate_decls
                .iter()
                .map(|predicate| (predicate.name.clone(), predicate))
                .collect(),
            snapshot_functions_to_predicates,
            predicates_to_snapshot_types,
        }
    }

    pub(super) fn iter_decls(&self) -> impl Iterator<Item = &'_ vir_low::PredicateDecl> {
        self.predicate_decls.values().cloned()
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> HeapEncoder<'p, 'v, 'tcx> {
    pub(super) fn get_predicate_decl(
        &self,
        predicate_name: &str,
    ) -> SpannedEncodingResult<&'p vir_low::PredicateDecl> {
        let decl = self
            .predicates
            .predicate_decls
            .get(predicate_name)
            .cloned()
            .unwrap();
        Ok(decl)
    }

    pub(super) fn get_predicate_parameters(
        &self,
        predicate_name: &str,
    ) -> &[vir_low::VariableDecl] {
        self.predicates
            .predicate_decls
            .get(predicate_name)
            .unwrap()
            .parameters
            .as_slice()
    }

    pub(super) fn get_predicate_parameters_as_arguments(
        &mut self,
        predicate_name: &str,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        let predicate_parameters = self.get_predicate_parameters(predicate_name).to_owned();
        Ok(predicate_parameters
            .iter()
            .map(|parameter| parameter.clone().into())
            .collect())
    }

    pub(super) fn get_predicate_name_for_function<'a>(
        &'a self,
        function_name: &str,
    ) -> SpannedEncodingResult<String> {
        let function = self.functions[function_name];
        let predicate_name = match function.kind {
            vir_low::FunctionKind::MemoryBlockBytes => todo!(),
            vir_low::FunctionKind::CallerFor => todo!(),
            vir_low::FunctionKind::SnapRange => unreachable!(),
            vir_low::FunctionKind::Snap => {
                self.predicates.snapshot_functions_to_predicates[function_name].clone()
            }
        };
        Ok(predicate_name)
    }

    pub(super) fn get_snapshot_type_for_predicate(
        &self,
        predicate_name: &str,
    ) -> Option<vir_low::Type> {
        let predicate = self.predicates.predicate_decls[predicate_name];
        match predicate.kind {
            vir_low::PredicateKind::MemoryBlock => {
                use vir_low::macros::*;
                Some(ty!(Bytes))
            }
            vir_low::PredicateKind::Owned => Some(
                self.predicates
                    .predicates_to_snapshot_types
                    .get(predicate_name)
                    .unwrap_or_else(|| unreachable!("predicate not found: {}", predicate_name))
                    .clone(),
            ),
            vir_low::PredicateKind::LifetimeToken
            | vir_low::PredicateKind::CloseFracRef
            | vir_low::PredicateKind::WithoutSnapshotWhole
            | vir_low::PredicateKind::WithoutSnapshotWholeNonAliased
            // | vir_low::PredicateKind::WithoutSnapshotFrac
            | vir_low::PredicateKind::DeadLifetimeToken
            | vir_low::PredicateKind::EndBorrowViewShift => None,
        }
    }

    pub(super) fn purify_predicate_arguments(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        expression_evaluation_state_label: Option<String>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        let mut arguments = Vec::new();
        for argument in &predicate.arguments {
            arguments.push(self.encode_pure_expression(
                statements,
                argument.clone(),
                expression_evaluation_state_label.clone(),
                position,
            )?);
        }
        Ok(arguments)
    }

    pub(super) fn get_predicate_permission_mask_kind(
        &self,
        predicate_name: &str,
    ) -> SpannedEncodingResult<PredicatePermissionMaskKind> {
        let predicate_decl = self.get_predicate_decl(predicate_name)?;
        let mask_kind = match predicate_decl.kind {
            vir_low::PredicateKind::MemoryBlock | vir_low::PredicateKind::Owned => {
                PredicatePermissionMaskKind::AliasedFractionalBoundedPerm
            }
            // vir_low::PredicateKind::WithoutSnapshotFrac |
            vir_low::PredicateKind::LifetimeToken => {
                PredicatePermissionMaskKind::AliasedFractionalBoundedPerm
            }
            vir_low::PredicateKind::CloseFracRef
            | vir_low::PredicateKind::WithoutSnapshotWhole
            | vir_low::PredicateKind::WithoutSnapshotWholeNonAliased
            | vir_low::PredicateKind::EndBorrowViewShift => {
                PredicatePermissionMaskKind::AliasedWholeBool
            }
            vir_low::PredicateKind::DeadLifetimeToken => {
                PredicatePermissionMaskKind::AliasedWholeNat
            }
        };
        Ok(mask_kind)
    }
}
