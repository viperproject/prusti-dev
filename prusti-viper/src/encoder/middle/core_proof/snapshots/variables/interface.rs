use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        heap::HeapInterface,
        lowerer::{Lowerer, VariablesLowererInterface},
        pointers::PointersInterface,
        references::ReferencesInterface,
        snapshots::{
            IntoProcedureSnapshot, IntoSnapshot, SnapshotValidityInterface, SnapshotValuesInterface,
        },
        type_layouts::TypeLayoutsInterface,
        types::TypesInterface,
    },
};

use std::collections::BTreeMap;
use vir_crate::{
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

// trait Private {
//     fn create_snapshot_variable(
//         &mut self,
//         name: &str,
//         ty: &vir_mid::Type,
//         version: u64,
//     ) -> SpannedEncodingResult<vir_low::VariableDecl>;
//     #[allow(clippy::ptr_arg)] // Clippy false positive.
//     /// Note: if `new_snapshot_root` is `Some`, the current encoding assumes
//     /// that the `place` is not behind a raw pointer.
//     fn snapshot_copy_except(
//         &mut self,
//         statements: &mut Vec<vir_low::Statement>,
//         base: vir_mid::VariableDecl,
//         // old_snapshot_root: vir_low::Expression,
//         // new_snapshot_root: vir_low::Expression,
//         place: &vir_mid::Expression,
//         position: vir_low::Position,
//     ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)>;
// }

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
    fn create_snapshot_variable(
        &mut self,
        name: &str,
        ty: &vir_mid::Type,
        version: u64,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        // let name = format!("{}$snapshot${}", name, version);
        let ty = ty.to_snapshot(self)?;
        // self.create_variable(name, ty)
        self.create_snapshot_variable_low(name, ty, version)
    }
    /// Copy all values of the old snapshot into the new snapshot, except the
    /// ones that belong to `place`.
    ///
    /// FIXME: Rewrite to use the new ADT based snapshot interface.
    fn snapshot_copy_except(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        base: vir_mid::VariableDecl,
        // old_snapshot_root: vir_low::Expression,
        // new_snapshot_root: vir_low::Expression,
        place: &vir_mid::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)> {
        use vir_low::macros::*;
        if let Some(parent) = place.get_parent_ref() {
            let parent_type = parent.get_type();
            let (old_snapshot, new_snapshot) =
                if let vir_mid::Type::Pointer(pointer_type) = parent_type {
                    let fresh_heap_chunk = self.fresh_heap_chunk(position)?;
                    let heap_chunk = self.heap_chunk_to_snapshot(
                        &pointer_type.target_type,
                        fresh_heap_chunk.clone().into(),
                        position,
                    )?;
                    if self.use_heap_variable()? {
                        let old_snapshot = parent.to_procedure_snapshot(self)?; // FIXME: This is most likely wrong.
                        let old_target_snapshot = self.pointer_target_snapshot(
                            parent.get_type(),
                            &None,
                            old_snapshot.clone(),
                            position,
                        )?;
                        let old_heap = self.heap_variable_version_at_label(&None)?;

                        // Note: All `old_*` need to be computed before the heap version
                        // is incremented.
                        let new_heap = self.new_heap_variable_version(position)?;
                        let address =
                            self.pointer_address(parent.get_type(), old_snapshot, position)?;
                        statements.push(vir_low::Statement::assign(
                            new_heap,
                            self.heap_update(
                                old_heap.into(),
                                address,
                                fresh_heap_chunk.into(),
                                position,
                            )?,
                            // vir_low::Expression::container_op(
                            //     vir_low::ContainerOpKind::MapUpdate,
                            //     self.heap_type()?,
                            //     vec![old_heap.into(), address, fresh_heap_chunk.into()],
                            //     position,
                            // ),
                            position,
                        ));
                        return Ok((old_target_snapshot, heap_chunk));
                    } else {
                        return Ok((heap_chunk.clone(), heap_chunk));
                    }
                } else {
                    self.snapshot_copy_except(
                        statements, base,
                        // old_snapshot_root,
                        // new_snapshot_root,
                        parent, position,
                    )?
                };

            let type_decl = self.encoder.get_type_decl_mid(parent_type)?;
            match &type_decl {
                vir_mid::TypeDecl::Bool
                | vir_mid::TypeDecl::Int(_)
                | vir_mid::TypeDecl::Float(_) => {
                    unreachable!("place: {}", place);
                }
                vir_mid::TypeDecl::Trusted(_) | vir_mid::TypeDecl::TypeVar(_) => {
                    unimplemented!("ty: {}", type_decl)
                }
                vir_mid::TypeDecl::Struct(decl) => {
                    // FIXME: Remove duplication with vir_mid::TypeDecl::Tuple
                    let place_field = place.clone().unwrap_field(); // FIXME: Implement a macro that takes a reference to avoid clonning.
                    for field in decl.fields.iter() {
                        if field != &place_field.field {
                            let old_field_snapshot = self.obtain_struct_field_snapshot(
                                parent_type,
                                field,
                                old_snapshot.clone(),
                                position,
                            )?;
                            let new_field_snapshot = self.obtain_struct_field_snapshot(
                                parent_type,
                                field,
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
                vir_mid::TypeDecl::Enum(_) => {
                    let place_variant = place.clone().unwrap_variant(); // FIXME: Implement a macro that takes a reference to avoid clonning.
                    let old_discriminant =
                        self.obtain_enum_discriminant(old_snapshot.clone(), parent_type, position)?;
                    let new_discriminant =
                        self.obtain_enum_discriminant(new_snapshot.clone(), parent_type, position)?;
                    statements.push(stmtp! {
                        position => assume ([new_discriminant] == [old_discriminant])
                    });
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
                vir_mid::TypeDecl::Pointer(_decl) => {
                    unreachable!("Should be handled by the caller.");
                    // let fresh_heap_chunk = self.fresh_heap_chunk()?;
                    // let heap_chunk = self.heap_chunk_to_snapshot(
                    //     &decl.target_type,
                    //     fresh_heap_chunk.clone().into(),
                    //     position,
                    // )?;
                    // let old_heap = self.heap_variable_version_at_label(&None)?;
                    // let new_heap = self.new_heap_variable_version(position)?;
                    // let address =
                    //     self.pointer_address(parent_type, old_snapshot.clone(), position)?;
                    // statements.push(vir_low::Statement::assign(
                    //     new_heap,
                    //     vir_low::Expression::container_op(
                    //         vir_low::ContainerOpKind::MapUpdate,
                    //         self.heap_type()?,
                    //         vec![old_heap.into(), address, fresh_heap_chunk.into()],
                    //         position,
                    //     ),
                    //     position,
                    // ));
                    // // statements.push(vir_low::Statement::assume(
                    // //     vir_low::Expression::equals(
                    // //         heap_chunk.clone(),

                    // //     )
                    // // ));
                    // let old_target_snapshot =
                    //     self.pointer_target_snapshot(parent_type, &None, old_snapshot, position)?;
                    // Ok((old_target_snapshot, heap_chunk))
                }
                vir_mid::TypeDecl::Sequence(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Map(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Closure(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Unsupported(_) => unimplemented!("ty: {}", type_decl),
            }
        } else {
            let old_snapshot_root = base.to_procedure_snapshot(self)?;
            let new_snapshot_root = self.new_snapshot_variable_version(&base, position)?;
            // We reached the root. Nothing to do here.
            Ok((old_snapshot_root.into(), new_snapshot_root.into()))
        }
    }
}

pub(in super::super::super) trait SnapshotVariablesInterface {
    fn create_snapshot_variable_low(
        &mut self,
        name: &str,
        ty: vir_low::Type,
        version: u64,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn new_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
        span: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn current_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn initial_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn snapshot_variable_version_at_label(
        &mut self,
        variable: &vir_mid::VariableDecl,
        label: &str,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn use_heap_variable(&self) -> SpannedEncodingResult<bool>;
    fn heap_variable_name(&self) -> SpannedEncodingResult<&'static str>;
    fn new_heap_variable_version(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn heap_variable_version_at_label(
        &mut self,
        old_label: &Option<String>,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn address_variable_version_at_label(
        &mut self,
        variable_name: &str,
        old_label: &Option<String>,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn fresh_heap_chunk(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn encode_snapshot_havoc(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        target: &vir_mid::Expression,
        position: vir_low::Position,
        // new_snapshot: Option<vir_low::VariableDecl>,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_snapshot_update_with_new_snapshot(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        target: &vir_mid::Expression,
        value: vir_low::Expression,
        position: vir_low::Position,
        // new_snapshot: Option<vir_low::VariableDecl>,
    ) -> SpannedEncodingResult<vir_low::Expression>;
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
            BTreeMap<
                vir_mid::BasicBlockId,
                Vec<(String, vir_low::Type, vir_low::Position, u64, u64)>,
            >,
        >,
        // basic_block_edges: &mut BTreeMap<
        //     vir_mid::BasicBlockId,
        //     BTreeMap<vir_mid::BasicBlockId, Vec<vir_low::Statement>>,
        // >,
    ) -> SpannedEncodingResult<()>;
    fn unset_current_block_for_snapshots(
        &mut self,
        label: vir_mid::BasicBlockId,
    ) -> SpannedEncodingResult<()>;
    fn save_old_label(&mut self, label: String) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> SnapshotVariablesInterface for Lowerer<'p, 'v, 'tcx> {
    fn create_snapshot_variable_low(
        &mut self,
        name: &str,
        ty: vir_low::Type,
        version: u64,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let name = format!("{name}$snapshot${version}");
        self.create_variable(name, ty)
    }
    fn new_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let ty = variable.ty.to_snapshot(self)?;
        // let new_version = self.snapshots_state.all_variables.new_version_or_default(
        //     &variable.name,
        //     &ty,
        //     position,
        // );
        // self.snapshots_state
        //     .current_variables
        //     .as_mut()
        //     .unwrap()
        //     .set(variable.name.clone(), new_version);
        let new_version =
            self.snapshots_state
                .ssa_state
                .new_variable_version(&variable.name, &ty, position);
        self.create_snapshot_variable_low(&variable.name, ty, new_version)
    }
    fn current_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        // let version = self
        //     .snapshots_state
        //     .current_variables
        //     .as_ref()
        //     .unwrap()
        //     .get_or_default(&variable.name);
        let version = self
            .snapshots_state
            .ssa_state
            .current_variable_version(&variable.name);
        self.create_snapshot_variable(&variable.name, &variable.ty, version)
    }
    fn initial_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        self.create_snapshot_variable(&variable.name, &variable.ty, 0)
    }
    fn snapshot_variable_version_at_label(
        &mut self,
        variable: &vir_mid::VariableDecl,
        label: &str,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        // let version = self
        //     .snapshots_state
        //     .variables_at_label
        //     .get(label)
        //     .unwrap_or_else(|| panic!("not found label {}", label))
        //     .get_or_default(&variable.name);
        let version = self
            .snapshots_state
            .ssa_state
            .variable_version_at_label(&variable.name, label);
        self.create_snapshot_variable(&variable.name, &variable.ty, version)
    }
    fn use_heap_variable(&self) -> SpannedEncodingResult<bool> {
        // Ok(self.check_mode.unwrap().is_purification_group())
        // FIXME: Rename to unsafe_cell_values.
        Ok(false) // FIXME: For now use only the heap-dependent proofs.
    }
    fn heap_variable_name(&self) -> SpannedEncodingResult<&'static str> {
        assert!(
            self.use_heap_variable()?,
            "The heap variable is not used when the check mode is Both"
        );
        Ok("heap$")
    }
    fn new_heap_variable_version(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        // let name = "heap$";
        let name = self.heap_variable_name()?;
        let ty = self.heap_type()?;
        let new_version = self
            .snapshots_state
            .ssa_state
            .new_variable_version(name, &ty, position);
        // let new_version = self
        //     .snapshots_state
        //     .all_variables
        //     .new_version_or_default(name, &ty, position);
        // self.snapshots_state
        //     .current_variables
        //     .as_mut()
        //     .unwrap()
        //     .set(name.to_string(), new_version);
        self.create_snapshot_variable_low(name, ty, new_version)
    }
    fn heap_variable_version_at_label(
        &mut self,
        old_label: &Option<String>,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        // let name = "heap$";
        let name = self.heap_variable_name()?;
        let version = self
            .snapshots_state
            .ssa_state
            .variable_version_at_maybe_label(name, old_label);
        // let version = if let Some(label) = old_label {
        //     self.snapshots_state
        //         .variables_at_label
        //         .get(label)
        //         .unwrap_or_else(|| panic!("not found label {}", label))
        //         .get_or_default(name)
        // } else {
        //     self.snapshots_state
        //         .current_variables
        //         .as_ref()
        //         .unwrap()
        //         .get_or_default(name)
        // };
        let ty = self.heap_type()?;
        // let name = format!("{}${}", name, version);
        // self.create_variable(name, ty)
        self.create_snapshot_variable_low(name, ty, version)
    }
    fn address_variable_version_at_label(
        &mut self,
        variable_name: &str,
        old_label: &Option<String>,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let name = format!("{variable_name}$address");
        let version = self
            .snapshots_state
            .ssa_state
            .variable_version_at_maybe_label(&name, old_label);
        // let version = if let Some(label) = old_label {
        //     self.snapshots_state
        //         .variables_at_label
        //         .get(label)
        //         .unwrap_or_else(|| panic!("not found label {}", label))
        //         .get_or_default(&name)
        // } else {
        //     self.snapshots_state
        //         .current_variables
        //         .as_ref()
        //         .unwrap()
        //         .get_or_default(&name)
        // };
        let ty = self.address_type()?;
        self.create_snapshot_variable_low(&name, ty, version)
    }
    fn fresh_heap_chunk(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let name = "heap_chunk$";
        let ty = self.heap_chunk_type()?;
        let new_version = self
            .snapshots_state
            .ssa_state
            .new_variable_version(name, &ty, position);
        // let new_version = self
        //     .snapshots_state
        //     .all_variables
        //     .new_version_or_default(name, &ty, position);
        // self.snapshots_state
        //     .current_variables
        //     .as_mut()
        //     .unwrap()
        //     .set(name.to_string(), new_version);
        // let name = format!("{}${}", name, new_version);
        // self.create_variable(name, ty)
        self.create_snapshot_variable_low(name, ty, new_version)
    }
    fn encode_snapshot_havoc(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        target: &vir_mid::Expression,
        position: vir_low::Position,
        // new_snapshot_root: Option<vir_low::VariableDecl>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // let base = target.get_base();
        // self.ensure_type_definition(&base.ty)?;
        // let old_snapshot = base.to_procedure_snapshot(self)?;
        // let new_snapshot = if let Some(new_snapshot) = new_snapshot {
        //     new_snapshot
        // } else {
        //     self.new_snapshot_variable_version(&base, position)?
        // };
        // self.snapshot_copy_except(statements, old_snapshot, new_snapshot, target, position)?;
        // Ok(())
        let base = target.get_base();
        self.ensure_type_definition(&base.ty)?;

        // if let Some(pointer_place) = target.get_last_dereferenced_pointer() {
        //     let pointer_type = pointer_place.get_type().clone().unwrap_pointer();
        //     let fresh_heap_chunk = self.fresh_heap_chunk()?;
        //     let heap_chunk = self.heap_chunk_to_snapshot(
        //         &pointer_type.target_type,
        //         fresh_heap_chunk.clone().into(),
        //         position,
        //     )?;
        //     let old_heap = self.heap_variable_version_at_label(&None)?;
        //     let new_heap = self.new_heap_variable_version(position)?;
        //     let address =
        //         self.pointer_address(pointer_place.get_type(), old_snapshot.clone().into(), position)?;
        //     statements.push(vir_low::Statement::assign(
        //         new_heap,
        //         vir_low::Expression::container_op(
        //             vir_low::ContainerOpKind::MapUpdate,
        //             self.heap_type()?,
        //             vec![old_heap.into(), address, fresh_heap_chunk.into()],
        //             position,
        //         ),
        //         position,
        //     ));
        //     let old_target_snapshot =
        //         self.pointer_target_snapshot(pointer_place.get_type(), &None, old_snapshot.into(), position)?;
        //     // Ok((old_target_snapshot, heap_chunk)
        //     let (_old_snapshot, new_snapshot) =
        //         self.snapshot_copy_except(statements, old_target_snapshot, heap_chunk, pointer_place, position)?;
        //     Ok(new_snapshot)
        // } else {

        // let (_old_snapshot, new_snapshot) =
        //     self.snapshot_copy_except(statements, old_snapshot, new_snapshot, target, position)?;
        let (_old_snapshot, new_snapshot) =
            self.snapshot_copy_except(statements, base, target, position)?;
        Ok(new_snapshot)
        // }
    }
    /// `new_snapshot_root` is used when we want to use a specific variable
    /// version as the root of the new snapshot.
    fn encode_snapshot_update_with_new_snapshot(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        target: &vir_mid::Expression,
        value: vir_low::Expression,
        position: vir_low::Position,
        // new_snapshot_root: Option<vir_low::VariableDecl>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        // self.encode_snapshot_havoc(statements, target, position, new_snapshot)?;
        // statements
        //     .push(stmtp! { position => assume ([target.to_procedure_snapshot(self)?] == [value]) });
        let new_snapshot = self.encode_snapshot_havoc(statements, target, position)?;
        statements.push(stmtp! { position => assume ([new_snapshot.clone()] == [value]) });
        Ok(new_snapshot)
    }
    fn encode_snapshot_update(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        target: &vir_mid::Expression,
        value: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        self.encode_snapshot_update_with_new_snapshot(statements, target, value, position)?;
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
            BTreeMap<
                vir_mid::BasicBlockId,
                Vec<(String, vir_low::Type, vir_low::Position, u64, u64)>,
            >,
        >,
        // basic_block_edges: &mut BTreeMap<
        //     vir_mid::BasicBlockId,
        //     BTreeMap<vir_mid::BasicBlockId, Vec<vir_low::Statement>>,
        // >,
    ) -> SpannedEncodingResult<()> {
        self.snapshots_state.ssa_state.prepare_new_current_block(
            label,
            predecessors,
            basic_block_edges,
        );
        // let predecessor_labels = &predecessors[label];
        // let mut new_map = VariableVersionMap::default();
        // for variable in self.snapshots_state.all_variables.names_clone() {
        //     let predecessor_maps = predecessor_labels
        //         .iter()
        //         .map(|label| &self.snapshots_state.variables[label])
        //         .collect::<Vec<_>>();
        //     let first_version = predecessor_maps[0].get_or_default(&variable);
        //     let different = predecessor_maps
        //         .iter()
        //         .any(|map| map.get_or_default(&variable) != first_version);
        //     if different {
        //         let new_version = self.snapshots_state.all_variables.new_version(&variable);
        //         let ty = self
        //             .snapshots_state
        //             .all_variables
        //             .get_type(&variable)
        //             .clone();
        //         let new_variable =
        //             self.create_snapshot_variable_low(&variable, ty.clone(), new_version)?;
        //         for predecessor_label in predecessor_labels {
        //             let old_version =
        //                 self.snapshots_state.variables[predecessor_label].get_or_default(&variable);
        //             let statements = basic_block_edges
        //                 .entry(predecessor_label.clone())
        //                 .or_default()
        //                 .entry(label.clone())
        //                 .or_default();
        //             let old_variable =
        //                 self.create_snapshot_variable_low(&variable, ty.clone(), old_version)?;
        //             let position = self.encoder.change_error_context(
        //                 // FIXME: Get a more precise span.
        //                 self.snapshots_state.all_variables.get_position(&variable),
        //                 ErrorCtxt::Unexpected,
        //             );
        //             let statement = vir_low::macros::stmtp! { position => assume (new_variable == old_variable) };
        //             statements.push(statement);
        //         }
        //         new_map.set(variable, new_version);
        //     } else {
        //         new_map.set(variable, first_version);
        //     }
        // }
        // self.snapshots_state.current_variables = Some(new_map);
        Ok(())
    }
    fn unset_current_block_for_snapshots(
        &mut self,
        label: vir_mid::BasicBlockId,
    ) -> SpannedEncodingResult<()> {
        self.snapshots_state.ssa_state.finish_current_block(label);
        // let current_variables = self.snapshots_state.current_variables.take().unwrap();
        // assert!(self
        //     .snapshots_state
        //     .variables
        //     .insert(label, current_variables)
        //     .is_none());
        Ok(())
    }
    fn save_old_label(&mut self, label: String) -> SpannedEncodingResult<()> {
        self.snapshots_state.ssa_state.save_state_at_label(label);
        // let current_variables = self.snapshots_state.current_variables.clone().unwrap();
        // assert!(self
        //     .snapshots_state
        //     .variables_at_label
        //     .insert(label, current_variables)
        //     .is_none());
        Ok(())
    }
}
