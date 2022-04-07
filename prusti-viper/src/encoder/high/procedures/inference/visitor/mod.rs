use super::{ensurer::ensure_required_permissions, state::FoldUnfoldState};
use crate::encoder::{
    errors::SpannedEncodingResult,
    high::procedures::inference::{
        action::{Action, ConversionState, FoldingActionState},
        permission::PermissionKind,
        semantics::collect_permission_changes,
    },
    Encoder,
};
use log::debug;
use prusti_common::config;
use rustc_hash::FxHashSet;
use rustc_hir::def_id::DefId;
use std::collections::{btree_map::Entry, BTreeMap};
use vir_crate::{
    common::{display::cjoin, position::Positioned},
    high::{self as vir_high},
    middle::{
        self as vir_mid,
        operations::{ToMiddleExpression, ToMiddleStatement},
    },
};

mod context;
mod debugging;

pub(super) struct Visitor<'p, 'v, 'tcx> {
    encoder: &'p mut Encoder<'v, 'tcx>,
    _proc_def_id: DefId,
    state_at_entry: BTreeMap<vir_mid::BasicBlockId, FoldUnfoldState>,
    /// Used only for debugging purposes.
    state_at_exit: BTreeMap<vir_mid::BasicBlockId, FoldUnfoldState>,
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
    pub(super) fn new(encoder: &'p mut Encoder<'v, 'tcx>, proc_def_id: DefId) -> Self {
        Self {
            encoder,
            _proc_def_id: proc_def_id,
            state_at_entry: Default::default(),
            state_at_exit: Default::default(),
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
        entry_state: FoldUnfoldState,
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
        self.state_at_entry.insert(entry.clone(), entry_state);
        self.entry_label = Some(entry);
        for old_label in traversal_order {
            let old_block = procedure.basic_blocks.remove(&old_label).unwrap();
            self.current_label = Some(self.lower_label(&old_label));
            self.lower_block(old_label, old_block)?;
            self.successfully_processed_blocks
                .insert(self.current_label.take().unwrap());
        }
        let new_procedure = vir_mid::ProcedureDecl {
            name: self.procedure_name.take().unwrap(),
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
            vir_high::Successor::Exit => vir_mid::Successor::Exit,
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
            vir_high::Successor::NonDetChoice(first, second) => {
                vir_mid::Successor::NonDetChoice(self.lower_label(first), self.lower_label(second))
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
        let mut state = if config::dump_debug_info() {
            self.state_at_entry
                .get(self.current_label.as_ref().unwrap())
                .unwrap()
                .clone()
        } else {
            self.state_at_entry
                .remove(self.current_label.as_ref().unwrap())
                .unwrap()
        };
        for statement in old_block.statements {
            self.lower_statement(statement, &mut state)?;
        }
        let successor_blocks = self.current_successors()?;
        assert!(
            !successor_blocks.is_empty() || state.is_empty(),
            "some predicates are leaked"
        );
        if config::dump_debug_info() {
            self.state_at_exit
                .insert(self.current_label.clone().unwrap(), state.clone());
        }
        for successor in successor_blocks {
            self.update_state_at_entry(successor, state.clone())?;
        }
        Ok(())
    }

    fn lower_statement(
        &mut self,
        statement: vir_high::Statement,
        state: &mut FoldUnfoldState,
    ) -> SpannedEncodingResult<()> {
        assert!(
            statement.is_comment() || statement.is_leak_all() || !statement.position().is_default(),
            "Statement has default position: {}",
            statement
        );
        let (consumed_permissions, produced_permissions) = collect_permission_changes(&statement)?;
        debug!(
            "lower_statement {}: {}",
            statement,
            cjoin(&consumed_permissions)
        );
        let actions = ensure_required_permissions(self, state, consumed_permissions.clone())?;
        for action in actions {
            let statement = match action {
                Action::Unfold(FoldingActionState {
                    kind: PermissionKind::Owned,
                    place,
                    enum_variant: _,
                    condition,
                }) => {
                    let position = place.position();
                    vir_mid::Statement::unfold_owned(
                        place.to_middle_expression(self.encoder)?,
                        condition,
                        position,
                    )
                }
                Action::Fold(FoldingActionState {
                    kind: PermissionKind::Owned,
                    place,
                    enum_variant: _,
                    condition,
                }) => {
                    let position = place.position();
                    vir_mid::Statement::fold_owned(
                        place.to_middle_expression(self.encoder)?,
                        condition,
                        position,
                    )
                }
                Action::Unfold(FoldingActionState {
                    kind: PermissionKind::MemoryBlock,
                    place,
                    enum_variant,
                    condition,
                }) => {
                    let position = place.position();
                    vir_mid::Statement::split_block(
                        place.to_middle_expression(self.encoder)?,
                        condition,
                        enum_variant
                            .map(|variant| variant.to_middle_expression(self.encoder))
                            .transpose()?,
                        position,
                    )
                }
                Action::Fold(FoldingActionState {
                    kind: PermissionKind::MemoryBlock,
                    place,
                    enum_variant,
                    condition,
                }) => {
                    let position = place.position();
                    vir_mid::Statement::join_block(
                        place.to_middle_expression(self.encoder)?,
                        condition,
                        enum_variant
                            .map(|variant| variant.to_middle_expression(self.encoder))
                            .transpose()?,
                        position,
                    )
                }
                Action::OwnedIntoMemoryBlock(ConversionState { place, condition }) => {
                    let position = place.position();
                    vir_mid::Statement::convert_owned_into_memory_block(
                        place.to_middle_expression(self.encoder)?,
                        condition,
                        position,
                    )
                }
            };
            self.current_statements.push(statement);
        }
        state.remove_permissions(&consumed_permissions)?;
        state.insert_permissions(produced_permissions)?;
        if let vir_high::Statement::LeakAll(vir_high::LeakAll {}) = &statement {
            // FIXME: Instead of leaking, we should:
            // 1. Unfold all Owned into MemoryBlock.
            // 2. Deallocate all MemoryBlock.
            // 3. Perform a leak check (this actually should be done always at
            //    the end of the exit block).
            state.clear()?;
        } else {
            self.current_statements
                .push(statement.to_middle_statement(self.encoder)?);
        }
        let new_block = self
            .basic_blocks
            .get_mut(self.current_label.as_ref().unwrap())
            .unwrap();
        new_block
            .statements
            .extend(std::mem::take(&mut self.current_statements));
        Ok(())
    }

    pub(crate) fn update_state_at_entry(
        &mut self,
        to_label: vir_mid::BasicBlockId,
        mut state: FoldUnfoldState,
    ) -> SpannedEncodingResult<()> {
        let from_label = self.current_label.as_ref().unwrap();
        match self.state_at_entry.entry(to_label) {
            Entry::Vacant(entry) => {
                state.reset_incoming_labels_with(from_label.clone())?;
                entry.insert(state);
            }
            Entry::Occupied(mut entry) => {
                entry.get_mut().merge(from_label.clone(), state)?;
            }
        }
        Ok(())
    }

    fn current_successors(&self) -> SpannedEncodingResult<Vec<vir_mid::BasicBlockId>> {
        let current_block = self
            .basic_blocks
            .get(self.current_label.as_ref().unwrap())
            .unwrap();
        Ok(current_block
            .successor
            .get_following()
            .into_iter()
            .cloned()
            .collect())
    }

    pub(super) fn cancel_crash_graphviz(mut self) {
        self.graphviz_on_crash = false;
    }
}
