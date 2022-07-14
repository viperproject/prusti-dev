use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        lowerer::{Lowerer, VariablesLowererInterface},
        references::ReferencesInterface,
        snapshots::{
            IntoProcedureSnapshot, IntoSnapshot, SnapshotValidityInterface, SnapshotValuesInterface,
        },
        type_layouts::TypeLayoutsInterface,
        types::TypesInterface,
    },
    mir::errors::ErrorInterface,
};

use std::collections::BTreeMap;
use vir_crate::{
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

use super::VariableVersionMap;

trait Private {
    fn create_snapshot_variable(
        &mut self,
        name: &str,
        ty: &vir_mid::Type,
        version: u64,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    #[allow(clippy::ptr_arg)] // Clippy false positive.
    fn snapshot_copy_except(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        old_snapshot_root: vir_low::VariableDecl,
        new_snapshot_root: vir_low::VariableDecl,
        place: &vir_mid::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn create_snapshot_variable(
        &mut self,
        name: &str,
        ty: &vir_mid::Type,
        version: u64,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let name = format!("{}$snapshot${}", name, version);
        let ty = ty.to_snapshot(self)?;
        self.create_variable(name, ty)
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
                | vir_mid::TypeDecl::Float(_)
                | vir_mid::TypeDecl::Pointer(_) => {
                    unreachable!("place: {}", place);
                }
                vir_mid::TypeDecl::Trusted(_) | vir_mid::TypeDecl::TypeVar(_) => {
                    unimplemented!("ty: {}", type_decl)
                }
                vir_mid::TypeDecl::Tuple(decl) => {
                    // FIXME: Remove duplication with vir_mid::TypeDecl::Struct
                    let place_field = place.clone().unwrap_field(); // FIXME: Implement a macro that takes a reference to avoid clonning.
                    for field in decl.iter_fields() {
                        if field.as_ref() != &place_field.field {
                            let old_field_snapshot = self.obtain_struct_field_snapshot(
                                parent_type,
                                &field,
                                old_snapshot.clone(),
                                position,
                            )?;
                            let new_field_snapshot = self.obtain_struct_field_snapshot(
                                parent_type,
                                &field,
                                new_snapshot.clone(),
                                position,
                            )?;
                            statements.push(
                                stmtp! { position => assume ([new_field_snapshot] == [old_field_snapshot])},
                            );
                        }
                    }
                    Ok((
                        self.obtain_struct_field_snapshot(
                            parent_type,
                            &place_field.field,
                            old_snapshot,
                            position,
                        )?,
                        self.obtain_struct_field_snapshot(
                            parent_type,
                            &place_field.field,
                            new_snapshot,
                            position,
                        )?,
                    ))
                }
                vir_mid::TypeDecl::Struct(decl) => {
                    // FIXME: Remove duplication with vir_mid::TypeDecl::Tuple
                    let place_field = place.clone().unwrap_field(); // FIXME: Implement a macro that takes a reference to avoid clonning.
                    for field in decl.iter_fields() {
                        if field.as_ref() != &place_field.field {
                            let old_field_snapshot = self.obtain_struct_field_snapshot(
                                parent_type,
                                &field,
                                old_snapshot.clone(),
                                position,
                            )?;
                            let new_field_snapshot = self.obtain_struct_field_snapshot(
                                parent_type,
                                &field,
                                new_snapshot.clone(),
                                position,
                            )?;
                            statements.push(
                                stmtp! { position => assume ([new_field_snapshot] == [old_field_snapshot])},
                            );
                        }
                    }
                    Ok((
                        self.obtain_struct_field_snapshot(
                            parent_type,
                            &place_field.field,
                            old_snapshot,
                            position,
                        )?,
                        self.obtain_struct_field_snapshot(
                            parent_type,
                            &place_field.field,
                            new_snapshot,
                            position,
                        )?,
                    ))
                }
                vir_mid::TypeDecl::Union(_) | vir_mid::TypeDecl::Enum(_) => {
                    let place_variant = place.clone().unwrap_variant(); // FIXME: Implement a macro that takes a reference to avoid clonning.
                    Ok((
                        self.obtain_enum_variant_snapshot(
                            parent_type,
                            &place_variant.variant_index,
                            old_snapshot,
                            position,
                        )?,
                        self.obtain_enum_variant_snapshot(
                            parent_type,
                            &place_variant.variant_index,
                            new_snapshot,
                            position,
                        )?,
                    ))
                }
                vir_mid::TypeDecl::Array(_) => {
                    let call = place.clone().unwrap_builtin_func_app(); // FIXME: Implement a macro that takes a reference to avoid clonning.
                    assert_eq!(call.function, vir_mid::BuiltinFunc::Index);
                    let index = call.arguments[1].to_procedure_snapshot(self)?;
                    let index_int = self.obtain_constant_value(
                        call.arguments[1].get_type(),
                        index.clone(),
                        position,
                    )?;
                    let old_len = self.obtain_array_len_snapshot(old_snapshot.clone(), position)?;
                    let new_len = self.obtain_array_len_snapshot(new_snapshot.clone(), position)?;
                    let size_type = self.size_type()?;
                    let size_type_mid = self.size_type_mid()?;
                    var_decls! { i: {size_type.clone()} };
                    let i_int =
                        self.obtain_constant_value(&size_type_mid, i.clone().into(), position)?;
                    let i_validity =
                        self.encode_snapshot_valid_call_for_type(i.into(), &size_type_mid)?;
                    let new_element_snapshot = self.obtain_array_element_snapshot(
                        new_snapshot.clone(),
                        i_int.clone(),
                        position,
                    )?;
                    let old_element_snapshot = self.obtain_array_element_snapshot(
                        old_snapshot.clone(),
                        i_int.clone(),
                        position,
                    )?;
                    statements.push(stmtp! { position => assume ([new_len.clone()] == [old_len])});
                    statements.push(stmtp! { position =>
                        assume (
                            forall(
                                i: {size_type} :: [ {[new_element_snapshot.clone()]} ]
                                ([i_validity] && ([i_int] < [new_len]) && (i != [index])) ==>
                                ([new_element_snapshot] == [old_element_snapshot])
                            )
                        )
                    });
                    Ok((
                        self.obtain_array_element_snapshot(
                            old_snapshot,
                            index_int.clone(),
                            position,
                        )?,
                        self.obtain_array_element_snapshot(new_snapshot, index_int, position)?,
                    ))
                }
                vir_mid::TypeDecl::Reference(decl) => {
                    if place.is_deref() {
                        let old_address_snapshot =
                            self.reference_address(parent_type, old_snapshot.clone(), position)?;
                        let new_address_snapshot =
                            self.reference_address(parent_type, new_snapshot.clone(), position)?;
                        statements.push(stmtp! { position =>
                            assume ([new_address_snapshot] == [old_address_snapshot])
                        });
                        if decl.uniqueness.is_unique() {
                            let old_final_snapshot = self.reference_target_final_snapshot(
                                parent_type,
                                old_snapshot.clone(),
                                position,
                            )?;
                            let new_final_snapshot = self.reference_target_final_snapshot(
                                parent_type,
                                new_snapshot.clone(),
                                position,
                            )?;
                            statements.push(stmtp! { position =>
                                assume ([new_final_snapshot] == [old_final_snapshot])
                            });
                        }
                        Ok((
                            self.reference_target_current_snapshot(
                                parent_type,
                                old_snapshot,
                                position,
                            )?,
                            self.reference_target_current_snapshot(
                                parent_type,
                                new_snapshot,
                                position,
                            )?,
                        ))
                    } else {
                        unimplemented!("Place: {}", place);
                    }
                }
                vir_mid::TypeDecl::Sequence(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Map(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Never => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Closure(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Unsupported(_) => unimplemented!("ty: {}", type_decl),
            }
        } else {
            // We reached the root. Nothing to do here.
            Ok((old_snapshot_root.into(), new_snapshot_root.into()))
        }
    }
}

pub(in super::super::super) trait SnapshotVariablesInterface {
    fn new_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
        span: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn current_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn snapshot_variable_version_at_label(
        &mut self,
        variable: &vir_mid::VariableDecl,
        label: &str,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    #[allow(clippy::ptr_arg)] // Clippy false positive.
    fn encode_snapshot_update(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        target: &vir_mid::Expression,
        value: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    fn set_current_block_for_snapshots(
        &mut self,
        label: &vir_mid::BasicBlockId,
        predecessors: &BTreeMap<vir_mid::BasicBlockId, Vec<vir_mid::BasicBlockId>>,
        basic_block_edges: &mut BTreeMap<
            vir_mid::BasicBlockId,
            BTreeMap<vir_mid::BasicBlockId, Vec<vir_low::Statement>>,
        >,
    ) -> SpannedEncodingResult<()>;
    fn unset_current_block_for_snapshots(
        &mut self,
        label: vir_mid::BasicBlockId,
    ) -> SpannedEncodingResult<()>;
    fn save_old_label(&mut self, label: String) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> SnapshotVariablesInterface for Lowerer<'p, 'v, 'tcx> {
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
            .get_or_default(&variable.name);
        self.create_snapshot_variable(&variable.name, &variable.ty, version)
    }
    fn snapshot_variable_version_at_label(
        &mut self,
        variable: &vir_mid::VariableDecl,
        label: &str,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let version = self
            .snapshots_state
            .variables_at_label
            .get(label)
            .unwrap_or_else(|| panic!("not found label {}", label))
            .get_or_default(&variable.name);
        self.create_snapshot_variable(&variable.name, &variable.ty, version)
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
        let old_snapshot = base.to_procedure_snapshot(self)?;
        let new_snapshot = self.new_snapshot_variable_version(&base, position)?;
        self.snapshot_copy_except(statements, old_snapshot, new_snapshot, target, position)?;
        statements
            .push(stmtp! { position => assume ([target.to_procedure_snapshot(self)?] == [value]) });
        Ok(())
    }
    /// `basic_block_edges` are statements to be executed then going from one
    /// block to another.
    fn set_current_block_for_snapshots(
        &mut self,
        label: &vir_mid::BasicBlockId,
        predecessors: &BTreeMap<vir_mid::BasicBlockId, Vec<vir_mid::BasicBlockId>>,
        basic_block_edges: &mut BTreeMap<
            vir_mid::BasicBlockId,
            BTreeMap<vir_mid::BasicBlockId, Vec<vir_low::Statement>>,
        >,
    ) -> SpannedEncodingResult<()> {
        let predecessor_labels = &predecessors[label];
        let mut new_map = VariableVersionMap::default();
        for variable in self.snapshots_state.all_variables.names_clone() {
            let predecessor_maps = predecessor_labels
                .iter()
                .map(|label| &self.snapshots_state.variables[label])
                .collect::<Vec<_>>();
            let first_version = predecessor_maps[0].get_or_default(&variable);
            let different = predecessor_maps
                .iter()
                .any(|map| map.get_or_default(&variable) != first_version);
            if different {
                let new_version = self.snapshots_state.all_variables.new_version(&variable);
                let ty = self
                    .snapshots_state
                    .all_variables
                    .get_type(&variable)
                    .clone();
                let new_variable = self.create_snapshot_variable(&variable, &ty, new_version)?;
                for predecessor_label in predecessor_labels {
                    let old_version =
                        self.snapshots_state.variables[predecessor_label].get_or_default(&variable);
                    let statements = basic_block_edges
                        .entry(predecessor_label.clone())
                        .or_default()
                        .entry(label.clone())
                        .or_default();
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
    fn save_old_label(&mut self, label: String) -> SpannedEncodingResult<()> {
        let current_variables = self.snapshots_state.current_variables.clone().unwrap();
        assert!(self
            .snapshots_state
            .variables_at_label
            .insert(label, current_variables)
            .is_none());
        Ok(())
    }
}
