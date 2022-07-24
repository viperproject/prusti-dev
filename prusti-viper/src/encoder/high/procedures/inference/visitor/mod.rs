use super::{
    ensurer::ensure_required_permissions,
    state::{FoldUnfoldState, PlaceWithDeadLifetimes, PredicateState},
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    high::procedures::inference::{
        action::{Action, ConversionState, FoldingActionState, RestorationState, UnreachableState},
        permission::PermissionKind,
        semantics::collect_permission_changes,
    },
    Encoder,
};
use log::debug;
use prusti_common::config;
use prusti_rustc_interface::hir::def_id::DefId;
use rustc_hash::FxHashSet;
use std::collections::{btree_map::Entry, BTreeMap};
use vir_crate::{
    common::{display::cjoin, position::Positioned},
    high::{self as vir_high},
    middle::{
        self as vir_mid,
        operations::{ToMiddleExpression, ToMiddleStatement, ToMiddleType},
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
    path_disambiguators: Option<
        BTreeMap<(vir_mid::BasicBlockId, vir_mid::BasicBlockId), Vec<vir_mid::BasicBlockId>>,
    >,
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
            path_disambiguators: Default::default(),
            graphviz_on_crash: config::dump_debug_info(),
        }
    }

    pub(super) fn infer_procedure(
        &mut self,
        mut procedure: vir_high::ProcedureDecl,
        entry_state: FoldUnfoldState,
    ) -> SpannedEncodingResult<vir_mid::ProcedureDecl> {
        self.procedure_name = Some(procedure.name.clone());

        let mut path_disambiguators = BTreeMap::new();
        for ((from, to), value) in procedure.get_path_disambiguators() {
            path_disambiguators.insert(
                (self.lower_label(&from), self.lower_label(&to)),
                value
                    .into_iter()
                    .map(|label| self.lower_label(&label))
                    .collect(),
            );
        }
        self.path_disambiguators = Some(path_disambiguators);

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
            self.lower_block(old_block)?;
            self.successfully_processed_blocks
                .insert(self.current_label.take().unwrap());
        }
        let check_mode = procedure.check_mode;
        let new_procedure = vir_mid::ProcedureDecl {
            name: self.procedure_name.take().unwrap(),
            check_mode,
            entry: self.entry_label.take().unwrap(),
            exit: self.lower_label(&procedure.exit),
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

    fn lower_block(&mut self, old_block: vir_high::BasicBlock) -> SpannedEncodingResult<()> {
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
            !successor_blocks.is_empty() || state.contains_only_leakable(),
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
        if let vir_high::Statement::DeadLifetime(dead_lifetime) = statement {
            self.process_dead_lifetime(dead_lifetime, state)?;
            return Ok(());
        }
        let (consumed_permissions, produced_permissions) =
            collect_permission_changes(self.encoder, &statement)?;
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
                    if let Some((lifetime, uniqueness)) = place.get_dereference_kind() {
                        let position = place.position();
                        vir_mid::Statement::unfold_ref(
                            place.to_middle_expression(self.encoder)?,
                            lifetime.to_middle_type(self.encoder)?,
                            uniqueness.to_middle_type(self.encoder)?,
                            condition,
                            position,
                        )
                    } else {
                        let position = place.position();
                        vir_mid::Statement::unfold_owned(
                            place.to_middle_expression(self.encoder)?,
                            condition,
                            position,
                        )
                    }
                }
                Action::Fold(FoldingActionState {
                    kind: PermissionKind::Owned,
                    place,
                    enum_variant: _,
                    condition,
                }) => {
                    if let Some((lifetime, uniqueness)) = place.get_dereference_kind() {
                        let position = place.position();
                        vir_mid::Statement::fold_ref(
                            place.to_middle_expression(self.encoder)?,
                            lifetime.to_middle_type(self.encoder)?,
                            uniqueness.to_middle_type(self.encoder)?,
                            condition,
                            position,
                        )
                    } else {
                        let position = place.position();
                        vir_mid::Statement::fold_owned(
                            place.to_middle_expression(self.encoder)?,
                            condition,
                            position,
                        )
                    }
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
                Action::RestoreMutBorrowed(RestorationState {
                    lifetime,
                    place,
                    condition,
                }) => {
                    let position = place.position();
                    vir_mid::Statement::restore_mut_borrowed(
                        lifetime.to_middle_type(self.encoder)?,
                        place.to_middle_expression(self.encoder)?,
                        condition,
                        position,
                    )
                }
                Action::Unreachable(UnreachableState {
                    position,
                    condition,
                }) => {
                    let statement = vir_mid::Statement::assert_no_pos(false.into(), condition);
                    statement.set_default_position(position)
                }
            };
            self.current_statements.push(statement);
        }
        state.remove_permissions(&consumed_permissions)?;
        state.insert_permissions(produced_permissions)?;
        match &statement {
            vir_high::Statement::LeakAll(vir_high::LeakAll {}) => {
                // FIXME: Instead of leaking, we should:
                // 1. Unfold all Owned into MemoryBlock.
                // 2. Deallocate all MemoryBlock.
                // 3. Perform a leak check (this actually should be done always at
                //    the end of the exit block).
                state.clear()?;
            }
            vir_high::Statement::SetUnionVariant(statement) => {
                let position = statement.position();
                // Split the memory block for the union itself.
                let parent = statement.variant_place.get_parent_ref().unwrap();
                let place = parent
                    .get_parent_ref()
                    .unwrap()
                    .clone()
                    .to_middle_expression(self.encoder)?;
                let variant = parent.clone().unwrap_variant().variant_index;
                let encoded_statement = vir_mid::Statement::split_block(
                    place,
                    None,
                    Some(variant.to_middle_type(self.encoder)?),
                    position,
                );
                self.current_statements.push(encoded_statement);
                // Split the memory block for the union's field.
                let place = parent.clone().to_middle_expression(self.encoder)?;
                let encoded_statement =
                    vir_mid::Statement::split_block(place, None, None, position);
                self.current_statements.push(encoded_statement);
            }
            _ => {
                self.current_statements
                    .push(statement.to_middle_statement(self.encoder)?);
            }
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

    fn process_dead_lifetime_for_predicate_state(
        &mut self,
        statement: &vir_high::DeadLifetime,
        state: &mut PredicateState,
        condition: Option<vir_mid::BlockMarkerCondition>,
    ) -> SpannedEncodingResult<()> {
        let (dead_references, places_with_dead_lifetimes) =
            state.mark_lifetime_dead(&statement.lifetime);
        for place in dead_references {
            let place = place.to_middle_expression(self.encoder)?;
            self.current_statements
                .push(vir_mid::Statement::dead_reference(
                    place,
                    condition.clone(),
                    statement.position,
                ));
        }
        for PlaceWithDeadLifetimes {
            place,
            lifetimes_dead_before,
            lifetimes_dead_after,
        } in places_with_dead_lifetimes
        {
            let place = place.to_middle_expression(self.encoder)?;
            self.current_statements
                .push(vir_mid::Statement::dead_lifetime(
                    place,
                    lifetimes_dead_before,
                    lifetimes_dead_after,
                    condition.clone(),
                    statement.position,
                ));
        }
        Ok(())
    }

    fn process_dead_lifetime(
        &mut self,
        statement: vir_high::DeadLifetime,
        state: &mut FoldUnfoldState,
    ) -> SpannedEncodingResult<()> {
        self.process_dead_lifetime_for_predicate_state(
            &statement,
            state.get_unconditional_state()?,
            None,
        )?;
        for (condition, conditional_predicate_state) in state.get_conditional_states()? {
            self.process_dead_lifetime_for_predicate_state(
                &statement,
                conditional_predicate_state,
                Some(condition.clone()),
            )?;
        }

        Ok(())
    }

    pub(crate) fn update_state_at_entry(
        &mut self,
        to_label: vir_mid::BasicBlockId,
        mut state: FoldUnfoldState,
    ) -> SpannedEncodingResult<()> {
        let from_label = self.current_label.as_ref().unwrap();
        match self.state_at_entry.entry(to_label.clone()) {
            Entry::Vacant(entry) => {
                state.reset_incoming_labels_with(
                    from_label.clone(),
                    self.path_disambiguators
                        .as_ref()
                        .unwrap()
                        .get(&(from_label.clone(), to_label))
                        .unwrap_or(&Vec::new()),
                )?;
                entry.insert(state);
            }
            Entry::Occupied(mut entry) => {
                entry.get_mut().merge(
                    from_label.clone(),
                    to_label,
                    self.path_disambiguators.as_ref().unwrap(),
                    state,
                )?;
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
