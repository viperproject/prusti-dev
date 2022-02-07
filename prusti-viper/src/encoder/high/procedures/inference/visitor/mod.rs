use super::{
    ensurer::{ensure_required_permissions, ExpandedPermissionKind},
    state::FoldUnfoldState,
};
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    high::{
        procedures::inference::{
            action::Action, permission::PermissionKind, semantics::collect_permission_changes,
        },
        type_layouts::HighTypeLayoutsEncoderInterface,
    },
    mir::{errors::ErrorInterface, types::MirTypeEncoderInterface},
    Encoder,
};
use log::debug;
use prusti_common::config;
use rustc_hash::FxHashSet;
use rustc_hir::def_id::DefId;
use std::collections::BTreeMap;
use vir_crate::{
    common::position::Positioned,
    high::{self as vir_high, operations::ty::Typed},
    middle::{
        self as vir_mid,
        operations::{ToMiddleExpression, ToMiddleStatement},
    },
};

mod debugging;

pub(super) struct Visitor<'p, 'v, 'tcx> {
    encoder: &'p mut Encoder<'v, 'tcx>,
    _proc_def_id: DefId,
    state_at_entry: FoldUnfoldState,
    procedure_name: Option<String>,
    entry_label: Option<vir_mid::BasicBlockId>,
    basic_blocks: BTreeMap<vir_mid::BasicBlockId, vir_mid::BasicBlock>,
    successfully_processed_blocks: FxHashSet<vir_mid::BasicBlockId>,
    current_label: Option<vir_mid::BasicBlockId>,
    current_statements: Vec<vir_mid::Statement>,
    /// Should we dump a Graphviz plot in case we crash during inference?
    graphviz_on_crash: bool,
}

impl<'p, 'v, 'tcx> Visitor<'p, 'v, 'tcx> {
    pub(super) fn new(
        encoder: &'p mut Encoder<'v, 'tcx>,
        proc_def_id: DefId,
        state_at_entry: FoldUnfoldState,
    ) -> Self {
        Self {
            encoder,
            _proc_def_id: proc_def_id,
            state_at_entry,
            procedure_name: None,
            entry_label: None,
            basic_blocks: Default::default(),
            successfully_processed_blocks: Default::default(),
            current_label: None,
            current_statements: Default::default(),
            graphviz_on_crash: config::dump_debug_info(),
        }
    }
    pub(super) fn infer_procedure(
        &mut self,
        mut procedure: vir_high::ProcedureDecl,
    ) -> SpannedEncodingResult<vir_mid::ProcedureDecl> {
        self.procedure_name = Some(procedure.name.clone());

        let traversal_order = procedure.get_topological_sort();
        for (label, block) in &procedure.basic_blocks {
            let successor = self.lower_successor(&block.successor)?;
            self.basic_blocks.insert(
                self.lower_label(label),
                vir_mid::BasicBlock {
                    statements: Vec::new(),
                    successor,
                },
            );
        }
        let entry = self.lower_label(&procedure.entry);
        let entry_block = self.basic_blocks.get_mut(&entry).unwrap();
        self.entry_label = Some(entry);
        for ret in procedure.returns {
            let position = ret.position;
            let mir_type = self.encoder.decode_type_high(&ret.variable.ty);
            let size = self.encoder.encode_type_size_expression_mid(mir_type)?;
            let place: vir_high::Expression = ret.into();
            let statement =
                vir_mid::Statement::inhale_no_pos(vir_mid::Predicate::memory_block_stack_no_pos(
                    place.to_middle_expression(self.encoder)?,
                    size,
                ))
                .set_default_position(
                    self.encoder
                        .change_error_context(position, ErrorCtxt::UnexpectedStorageLive),
                );
            entry_block.statements.push(statement);
        }
        for _parameter in procedure.parameters {
            unimplemented!();
            // entry_block.statements.push(
            //     vir_mid::Statement::inhale_no_pos(vir_mid::Predicate::owned_non_aliased(...))
            // );
        }
        for old_label in traversal_order {
            let old_block = procedure.basic_blocks.remove(&old_label).unwrap();
            self.current_label = Some(self.lower_label(&old_label));
            self.lower_block(old_label, old_block)?;
            self.successfully_processed_blocks
                .insert(self.current_label.take().unwrap());
        }
        let new_procedure = vir_mid::ProcedureDecl {
            name: self.procedure_name.take().unwrap(),
            parameters: Vec::new(), // FIXME: Unused fields.
            returns: Vec::new(),    // FIXME: Unused fields.
            entry: self.entry_label.take().unwrap(),
            basic_blocks: std::mem::take(&mut self.basic_blocks),
        };
        Ok(new_procedure)
    }

    fn lower_successor(
        &mut self,
        successor: &vir_high::Successor,
    ) -> SpannedEncodingResult<vir_mid::Successor> {
        let result = match successor {
            vir_high::Successor::Return => vir_mid::Successor::Return,
            vir_high::Successor::Goto(target) => vir_mid::Successor::Goto(self.lower_label(target)),
            vir_high::Successor::GotoSwitch(targets) => {
                let mut new_targets = Vec::new();
                for (test, target) in targets {
                    let new_test: vir_mid::Expression =
                        test.clone().to_middle_expression(self.encoder)?;
                    new_targets.push((new_test, self.lower_label(target)));
                }
                vir_mid::Successor::GotoSwitch(new_targets)
            }
        };
        Ok(result)
    }

    fn lower_label(&self, label: &vir_high::BasicBlockId) -> vir_mid::BasicBlockId {
        vir_mid::BasicBlockId {
            name: label.name.clone(),
        }
    }

    fn lower_block(
        &mut self,
        _old_label: vir_high::BasicBlockId,
        old_block: vir_high::BasicBlock,
    ) -> SpannedEncodingResult<()> {
        for statement in old_block.statements {
            self.lower_statement(statement)?;
        }
        Ok(())
    }

    fn lower_statement(&mut self, statement: vir_high::Statement) -> SpannedEncodingResult<()> {
        assert!(
            statement.is_comment() || !statement.position().is_default(),
            "Statement has default position: {}",
            statement
        );
        let (required_permissions, ensured_permissions) = collect_permission_changes(&statement)?;
        debug!("lower_statement {}: {:?}", statement, required_permissions);
        let actions = ensure_required_permissions(self, required_permissions.clone())?;
        for action in actions {
            let statement = match action {
                Action::Unfold(PermissionKind::Owned, place) => vir_mid::Statement::unfold_owned(
                    place.to_middle_expression(self.encoder)?,
                    statement.position(),
                ),
                Action::Fold(PermissionKind::Owned, place) => vir_mid::Statement::fold_owned(
                    place.to_middle_expression(self.encoder)?,
                    statement.position(),
                ),
                Action::Unfold(PermissionKind::MemoryBlock, place) => {
                    vir_mid::Statement::split_block(
                        place.to_middle_expression(self.encoder)?,
                        statement.position(),
                    )
                }
                Action::Fold(PermissionKind::MemoryBlock, place) => vir_mid::Statement::join_block(
                    place.to_middle_expression(self.encoder)?,
                    statement.position(),
                ),
            };
            self.current_statements.push(statement);
        }
        self.state_at_entry
            .remove_permissions(&required_permissions)?;
        self.state_at_entry
            .insert_permissions(ensured_permissions)?;
        self.state_at_entry.debug_print();
        self.current_statements
            .push(statement.to_middle_statement(self.encoder)?);
        let new_block = self
            .basic_blocks
            .get_mut(self.current_label.as_ref().unwrap())
            .unwrap();
        new_block
            .statements
            .extend(std::mem::take(&mut self.current_statements));
        Ok(())
    }

    pub(super) fn cancel_crash_graphviz(mut self) {
        self.graphviz_on_crash = false;
    }
}

impl<'p, 'v, 'tcx> super::ensurer::Context for Visitor<'p, 'v, 'tcx> {
    fn state(&self) -> &FoldUnfoldState {
        &self.state_at_entry
    }

    fn state_mut(&mut self) -> &mut FoldUnfoldState {
        &mut self.state_at_entry
    }

    fn expand_place(
        &mut self,
        place: &vir_high::Expression,
    ) -> SpannedEncodingResult<Vec<(ExpandedPermissionKind, vir_high::Expression)>> {
        let ty = place.get_type();
        let type_decl = self.encoder.encode_type_def(ty)?;
        let expansion = match type_decl {
            vir_high::TypeDecl::Bool
            | vir_high::TypeDecl::Int(_)
            | vir_high::TypeDecl::Float(_) => {
                // Primitive type. Convert.
                vec![(ExpandedPermissionKind::MemoryBlock, place.clone())]
            }
            vir_high::TypeDecl::TypeVar(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Tuple(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Struct(struct_decl) => struct_decl
                .fields
                .into_iter()
                .map(|field| {
                    (
                        ExpandedPermissionKind::Same,
                        vir_high::Expression::field_no_pos(place.clone(), field),
                    )
                })
                .collect(),
            vir_high::TypeDecl::Enum(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Array(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Reference(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Never => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Closure(_) => unimplemented!("ty: {}", ty),
            vir_high::TypeDecl::Unsupported(_) => unimplemented!("ty: {}", ty),
        };
        Ok(expansion)
    }
}
