use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        adts::{AdtConstructor, AdtsInterface},
        lowerer::{DomainsLowererInterface, Lowerer, VariablesLowererInterface},
        predicates_memory_block::PredicatesMemoryBlockInterface,
        types::TypesInterface,
    },
    mir::errors::ErrorInterface,
};
use rustc_hash::FxHashSet;
use std::collections::BTreeMap;
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low, operations::ToLow},
    middle::{self as vir_mid, operations::ty::Typed},
};

use super::IntoSnapshot;

#[derive(Default)]
struct VariableVersionMap {
    /// Mapping from variable names to their versions.
    variable_versions: BTreeMap<String, u64>,
}

impl VariableVersionMap {
    fn get(&self, variable: &str) -> u64 {
        self.variable_versions.get(variable).cloned().unwrap_or(0)
    }
    fn set(&mut self, variable: String, version: u64) {
        self.variable_versions.insert(variable, version);
    }
}

#[derive(Default)]
struct AllVariablesMap {
    versions: BTreeMap<String, u64>,
    types: BTreeMap<String, vir_mid::Type>,
    positions: BTreeMap<String, vir_low::Position>,
}

impl AllVariablesMap {
    fn names_clone(&self) -> Vec<String> {
        self.versions.keys().cloned().collect()
    }
    fn get_type(&self, variable: &str) -> &vir_mid::Type {
        &self.types[variable]
    }
    fn get_position(&self, variable: &str) -> vir_low::Position {
        self.positions[variable]
    }
    fn new_version(&mut self, variable: &str) -> u64 {
        let current_version = self.versions.get_mut(variable).unwrap();
        *current_version += 1;
        *current_version
    }
    fn new_version_or_default(
        &mut self,
        variable: &vir_mid::VariableDecl,
        position: vir_low::Position,
    ) -> u64 {
        if self.versions.contains_key(&variable.name) {
            let version = self.versions.get_mut(&variable.name).unwrap();
            *version += 1;
            *version
        } else {
            self.versions.insert(variable.name.clone(), 1);
            self.types
                .insert(variable.name.clone(), variable.ty.clone());
            self.positions.insert(variable.name.clone(), position);
            1
        }
    }
}

#[derive(Default)]
pub(in super::super) struct SnapshotsState {
    /// Used for decoding domain names into original types.
    domain_types: BTreeMap<String, vir_mid::Type>,
    /// The list of types for which `to_bytes` was encoded.
    encoded_to_bytes: FxHashSet<vir_mid::Type>,
    all_variables: AllVariablesMap,
    variables: BTreeMap<vir_mid::BasicBlockId, VariableVersionMap>,
    current_variables: Option<VariableVersionMap>,
}

trait Private {
    fn insert_snapshot_axiom(
        &mut self,
        ty: &vir_mid::Type,
        axiom: vir_low::DomainAxiomDecl,
    ) -> SpannedEncodingResult<()>;
    #[allow(clippy::ptr_arg)] // Clippy false positive.
    fn snapshot_copy_except(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        old_snapshot_root: vir_low::VariableDecl,
        new_snapshot_root: vir_low::VariableDecl,
        place: &vir_mid::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)>;
    fn create_snapshot_variable(
        &mut self,
        name: &str,
        ty: &vir_mid::Type,
        version: u64,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn insert_snapshot_axiom(
        &mut self,
        ty: &vir_mid::Type,
        axiom: vir_low::DomainAxiomDecl,
    ) -> SpannedEncodingResult<()> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        self.declare_axiom(&domain_name, axiom)
    }
    /// Copy all values of the old snapshot into the new snapshot, except the
    /// ones that belong to `place`.
    ///
    /// FIXME: Rewrite to use the new ADT based snapshot interface.
    fn snapshot_copy_except(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        old_snapshot_root: vir_low::VariableDecl,
        new_snapshot_root: vir_low::VariableDecl,
        place: &vir_mid::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)> {
        use vir_low::macros::*;
        if let Some(parent) = place.get_parent_ref() {
            let (old_snapshot, new_snapshot) = self.snapshot_copy_except(
                statements,
                old_snapshot_root,
                new_snapshot_root,
                parent,
                position,
            )?;
            let parent_type = parent.get_type();
            let type_decl = self.encoder.get_type_decl_mid(parent_type)?;
            match &type_decl {
                vir_mid::TypeDecl::Bool
                | vir_mid::TypeDecl::Int(_)
                | vir_mid::TypeDecl::Float(_) => {
                    unreachable!("place: {}", place);
                }
                vir_mid::TypeDecl::TypeVar(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Tuple(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Struct(decl) => {
                    let place_field = place.clone().unwrap_field(); // FIXME: Implement a macro that takes a reference to avoid clonning.
                    for field in decl.iter_fields() {
                        if field.as_ref() != &place_field.field {
                            let old_field_snapshot = self.encode_field_snapshot(
                                parent_type,
                                &field,
                                old_snapshot.clone(),
                                Default::default(),
                            )?;
                            let new_field_snapshot = self.encode_field_snapshot(
                                parent_type,
                                &field,
                                new_snapshot.clone(),
                                Default::default(),
                            )?;
                            statements.push(
                                stmtp! { position => assume ([new_field_snapshot] == [old_field_snapshot])},
                            );
                        }
                    }
                    Ok((
                        self.encode_field_snapshot(
                            parent_type,
                            &place_field.field,
                            old_snapshot,
                            Default::default(),
                        )?,
                        self.encode_field_snapshot(
                            parent_type,
                            &place_field.field,
                            new_snapshot,
                            Default::default(),
                        )?,
                    ))
                }
                vir_mid::TypeDecl::Enum(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Array(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Reference(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Never => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Closure(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Unsupported(_) => unimplemented!("ty: {}", type_decl),
            }
        } else {
            // We reached the root. Nothing to do here.
            Ok((old_snapshot_root.into(), new_snapshot_root.into()))
        }
    }
    fn create_snapshot_variable(
        &mut self,
        name: &str,
        ty: &vir_mid::Type,
        version: u64,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let name = format!("{}$snapshot${}", name, version);
        let ty = ty.create_snapshot(self)?;
        self.create_variable(name, ty)
    }
}

pub(in super::super) trait SnapshotsInterface {
    fn encode_snapshot_domain_name(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<String>;
    fn try_decoding_snapshot_type(
        &self,
        domain_name: &str,
    ) -> SpannedEncodingResult<Option<vir_mid::Type>>;
    fn encode_snapshot_domain_type(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Type>;
    fn encode_snapshot_to_bytes_function(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    fn encode_snapshot_validity_expression(
        &mut self,
        argument: vir_low::Expression,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn declare_snapshot_constructors<'a>(
        &mut self,
        ty: &vir_mid::Type,
        constructors: impl Iterator<Item = &'a AdtConstructor>,
    ) -> SpannedEncodingResult<()>;
    fn encode_field_snapshot(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_snapshot: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_constant_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_snapshot_constructor_base_call(
        &mut self,
        ty: &vir_mid::Type,
        arguments: Vec<vir_low::Expression>,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_snapshot_deconstructor_constant_call(
        &mut self,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_unary_op_call(
        &mut self,
        op: vir_mid::UnaryOpKind,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_binary_op_call(
        &mut self,
        op: vir_mid::BinaryOpKind,
        ty: &vir_mid::Type,
        left: vir_low::Expression,
        right: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    #[allow(clippy::ptr_arg)] // Clippy false positive.
    fn encode_snapshot_update(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        target: &vir_mid::Expression,
        value: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    fn new_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
        span: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn current_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn set_current_block_for_snapshots(
        &mut self,
        label: &vir_mid::BasicBlockId,
        predecessors: &BTreeMap<vir_mid::BasicBlockId, Vec<vir_mid::BasicBlockId>>,
        basic_blocks: &mut BTreeMap<
            vir_mid::BasicBlockId,
            (Vec<vir_low::Statement>, vir_low::Successor),
        >,
    ) -> SpannedEncodingResult<()>;
    fn unset_current_block_for_snapshots(
        &mut self,
        label: vir_mid::BasicBlockId,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> SnapshotsInterface for Lowerer<'p, 'v, 'tcx> {
    fn encode_snapshot_domain_name(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<String> {
        let domain_name = format!("Snap${}", ty.get_identifier());
        if !self.snapshots_state.domain_types.contains_key(&domain_name) {
            self.snapshots_state
                .domain_types
                .insert(domain_name.clone(), ty.clone());
        }
        Ok(domain_name)
    }
    fn try_decoding_snapshot_type(
        &self,
        domain_name: &str,
    ) -> SpannedEncodingResult<Option<vir_mid::Type>> {
        Ok(self.snapshots_state.domain_types.get(domain_name).cloned())
    }
    fn encode_snapshot_domain_type(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Type> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        self.domain_type(domain_name)
    }
    fn encode_snapshot_to_bytes_function(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        if !self.snapshots_state.encoded_to_bytes.contains(ty) {
            self.snapshots_state.encoded_to_bytes.insert(ty.clone());
            let domain_name = self.encode_snapshot_domain_name(ty)?;
            let domain_type = self.encode_snapshot_domain_type(ty)?;
            let return_type = self.bytes_type()?;
            self.declare_domain_function(
                std::borrow::Cow::Owned(domain_name),
                std::borrow::Cow::Owned(format!("to_bytes${}", ty.get_identifier())),
                std::borrow::Cow::Owned(vec![vir_low::VariableDecl::new("snapshot", domain_type)]),
                std::borrow::Cow::Owned(return_type),
            )?;
        }
        Ok(())
    }
    // TODO: Rename this to type validity and move to
    // prusti-viper/src/encoder/middle/core_proof/types/interface.rs
    fn encode_snapshot_validity_expression(
        &mut self,
        argument: vir_low::Expression,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        self.create_domain_func_app(
            domain_name,
            format!("valid${}", ty.get_identifier()),
            vec![argument],
            vir_low::Type::Bool,
            Default::default(),
        )
    }
    fn declare_snapshot_constructors<'a>(
        &mut self,
        ty: &vir_mid::Type,
        constructors: impl Iterator<Item = &'a AdtConstructor>,
    ) -> SpannedEncodingResult<()> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        for constructor in constructors {
            self.insert_domain_function(
                &domain_name,
                constructor.create_constructor_function(&domain_name),
            )?;
            for function in constructor.create_destructor_functions(&domain_name) {
                self.insert_domain_function(&domain_name, function)?;
            }
            for axiom in constructor.create_injectivity_axioms(&domain_name) {
                self.declare_axiom(&domain_name, axiom)?;
            }
        }
        Ok(())
    }
    fn encode_field_snapshot(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_snapshot: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let domain_name = self.encode_snapshot_domain_name(base_type)?;
        let return_type = field.ty.create_snapshot(self)?;
        Ok(self
            .adt_destructor_base_call(&domain_name, &field.name, return_type, base_snapshot)?
            .set_default_position(position))
    }
    fn encode_constant_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        mut argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.ensure_type_definition(ty)?;
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let low_type = match &ty {
            vir_mid::Type::Bool => vir_low::Type::Bool,
            vir_mid::Type::Int(_) => vir_low::Type::Int,
            x => unimplemented!("{:?}", x),
        };
        vir_low::operations::ty::Typed::set_type(&mut argument, low_type);
        Ok(self
            .adt_constructor_constant_call(&domain_name, vec![argument])?
            .set_default_position(position))
    }
    fn encode_snapshot_constructor_base_call(
        &mut self,
        ty: &vir_mid::Type,
        arguments: Vec<vir_low::Expression>,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let function_name = self.adt_constructor_base_name(&domain_name)?;
        let return_type = ty.create_snapshot(self)?;
        self.create_domain_func_app(domain_name, function_name, arguments, return_type, position)
    }
    fn encode_snapshot_deconstructor_constant_call(
        &mut self,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let function_name = self.adt_destructor_constant_name(&domain_name)?;
        let return_type = match &ty {
            vir_mid::Type::Bool => vir_low::Type::Bool,
            vir_mid::Type::Int(_) => vir_low::Type::Int,
            x => unimplemented!("{:?}", x),
        };
        self.create_domain_func_app(
            domain_name,
            function_name,
            vec![argument],
            return_type,
            position,
        )
    }
    fn encode_unary_op_call(
        &mut self,
        op: vir_mid::UnaryOpKind,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // FIXME: Encode evaluation and simplification axioms.
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let op = op.to_low(self)?;
        let variant = self.encode_unary_op_variant(op, ty)?;
        let function_name = self.adt_constructor_variant_name(&domain_name, &variant)?;
        let return_type = ty.create_snapshot(self)?;
        self.create_domain_func_app(
            domain_name,
            function_name,
            vec![argument],
            return_type,
            position,
        )
    }
    fn encode_binary_op_call(
        &mut self,
        op: vir_mid::BinaryOpKind,
        ty: &vir_mid::Type,
        left: vir_low::Expression,
        right: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // FIXME: Encode evaluation and simplification axioms.
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let op = op.to_low(self)?;
        let variant = self.encode_binary_op_variant(op, ty)?;
        let function_name = self.adt_constructor_variant_name(&domain_name, &variant)?;
        let return_type = ty.create_snapshot(self)?;
        self.create_domain_func_app(
            domain_name,
            function_name,
            vec![left, right],
            return_type,
            position,
        )
    }
    fn encode_snapshot_update(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        target: &vir_mid::Expression,
        value: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let base = target.get_base();
        self.ensure_type_definition(&base.ty)?;
        let old_snapshot = base.create_snapshot(self)?;
        let new_snapshot = self.new_snapshot_variable_version(&base, position)?;
        self.snapshot_copy_except(statements, old_snapshot, new_snapshot, target, position)?;
        statements.push(stmtp! { position => assume ([target.create_snapshot(self)?] == [value]) });
        Ok(())
    }
    fn new_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let new_version = self
            .snapshots_state
            .all_variables
            .new_version_or_default(variable, position);
        self.snapshots_state
            .current_variables
            .as_mut()
            .unwrap()
            .set(variable.name.clone(), new_version);
        self.create_snapshot_variable(&variable.name, &variable.ty, new_version)
    }
    fn current_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let version = self
            .snapshots_state
            .current_variables
            .as_ref()
            .unwrap()
            .get(&variable.name);
        self.create_snapshot_variable(&variable.name, &variable.ty, version)
    }
    fn set_current_block_for_snapshots(
        &mut self,
        label: &vir_mid::BasicBlockId,
        predecessors: &BTreeMap<vir_mid::BasicBlockId, Vec<vir_mid::BasicBlockId>>,
        basic_blocks: &mut BTreeMap<
            vir_mid::BasicBlockId,
            (Vec<vir_low::Statement>, vir_low::Successor),
        >,
    ) -> SpannedEncodingResult<()> {
        let predecessor_labels = &predecessors[label];
        let mut new_map = VariableVersionMap::default();
        for variable in self.snapshots_state.all_variables.names_clone() {
            let predecessor_maps = predecessor_labels
                .iter()
                .map(|label| &self.snapshots_state.variables[label])
                .collect::<Vec<_>>();
            let first_version = predecessor_maps[0].get(&variable);
            let different = predecessor_maps
                .iter()
                .any(|map| map.get(&variable) != first_version);
            if different {
                let new_version = self.snapshots_state.all_variables.new_version(&variable);
                let ty = self
                    .snapshots_state
                    .all_variables
                    .get_type(&variable)
                    .clone();
                let new_variable = self.create_snapshot_variable(&variable, &ty, new_version)?;
                for label in predecessor_labels {
                    if let Some(&old_version) = self.snapshots_state.variables[label]
                        .variable_versions
                        .get(&variable)
                    {
                        let (statements, _) = basic_blocks.get_mut(label).unwrap();
                        let old_variable =
                            self.create_snapshot_variable(&variable, &ty, old_version)?;
                        let position = self.encoder.change_error_context(
                            // FIXME: Get a more precise span.
                            self.snapshots_state.all_variables.get_position(&variable),
                            ErrorCtxt::Unexpected,
                        );
                        let statement = vir_low::macros::stmtp! { position => assume (new_variable == old_variable) };
                        statements.push(statement);
                    }
                }
                new_map.set(variable, new_version);
            } else {
                new_map.set(variable, first_version);
            }
        }
        self.snapshots_state.current_variables = Some(new_map);
        Ok(())
    }
    fn unset_current_block_for_snapshots(
        &mut self,
        label: vir_mid::BasicBlockId,
    ) -> SpannedEncodingResult<()> {
        let current_variables = self.snapshots_state.current_variables.take().unwrap();
        assert!(self
            .snapshots_state
            .variables
            .insert(label, current_variables)
            .is_none());
        Ok(())
    }
}
