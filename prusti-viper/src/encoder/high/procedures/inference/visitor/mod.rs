use super::{
    ensurer::{
        ensure_required_permission, ensure_required_permissions,
        try_ensure_enum_discriminant_by_unfolding,
    },
    state::{
        DeadLifetimeReport, FoldUnfoldState, PlaceWithDeadLifetimes, PredicateState,
        PredicateStateOnPath,
    },
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
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::{btree_map::Entry, BTreeMap};
use vir_crate::{
    common::{cfg::Cfg, check_mode::CheckMode, display::cjoin, position::Positioned},
    middle::{
        self as vir_mid,
        operations::{
            ty::Typed, TypedToMiddleExpression, TypedToMiddlePredicate, TypedToMiddleStatement,
            TypedToMiddleType,
        },
    },
    typed::{self as vir_typed},
};

mod context;
mod debugging;

pub(super) struct Visitor<'p, 'v, 'tcx> {
    encoder: &'p mut Encoder<'v, 'tcx>,
    _proc_def_id: DefId,
    check_mode: Option<CheckMode>,
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
            check_mode: None,
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
        mut procedure: vir_typed::ProcedureDecl,
        entry_state: FoldUnfoldState,
    ) -> SpannedEncodingResult<vir_mid::ProcedureDecl> {
        self.procedure_name = Some(procedure.name.clone());
        self.check_mode = Some(procedure.check_mode);

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
        if let Some(path) = config::dump_fold_unfold_state_of_blocks() {
            let label_markers: FxHashMap<String, bool> =
                serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
            self.render_crash_graphviz(Some(&label_markers));
        }
        let check_mode = procedure.check_mode;
        let non_aliased_places = procedure
            .non_aliased_places
            .into_iter()
            .map(|place| place.typed_to_middle_expression(self.encoder))
            .collect::<Result<_, _>>()?;
        let new_procedure = vir_mid::ProcedureDecl {
            name: self.procedure_name.take().unwrap(),
            check_mode,
            position: procedure.position,
            non_aliased_places,
            entry: self.entry_label.take().unwrap(),
            exit: self.lower_label(&procedure.exit),
            basic_blocks: std::mem::take(&mut self.basic_blocks),
        };
        Ok(new_procedure)
    }

    fn lower_successor(
        &mut self,
        successor: &vir_typed::Successor,
    ) -> SpannedEncodingResult<vir_mid::Successor> {
        let result = match successor {
            vir_typed::Successor::Exit => vir_mid::Successor::Exit,
            vir_typed::Successor::Goto(target) => {
                vir_mid::Successor::Goto(self.lower_label(target))
            }
            vir_typed::Successor::GotoSwitch(targets) => {
                let mut new_targets = Vec::new();
                for (test, target) in targets {
                    let new_test: vir_mid::Expression =
                        test.clone().typed_to_middle_expression(self.encoder)?;
                    new_targets.push((new_test, self.lower_label(target)));
                }
                vir_mid::Successor::GotoSwitch(new_targets)
            }
            vir_typed::Successor::NonDetChoice(first, second) => {
                vir_mid::Successor::NonDetChoice(self.lower_label(first), self.lower_label(second))
            }
        };
        Ok(result)
    }

    fn lower_label(&self, label: &vir_typed::BasicBlockId) -> vir_mid::BasicBlockId {
        vir_mid::BasicBlockId {
            name: label.name.clone(),
        }
    }

    fn lower_block(&mut self, old_block: vir_typed::BasicBlock) -> SpannedEncodingResult<()> {
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
        let mut skip_automatic_close_ref = Vec::new();
        for statement in old_block.statements {
            self.lower_statement(statement, &mut state, &mut skip_automatic_close_ref)?;
        }
        assert!(
            skip_automatic_close_ref.is_empty(),
            "Automatic opening of references cannot span multiple blocks."
        );
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

    #[tracing::instrument(level = "debug", skip(self, state))]
    fn lower_statement(
        &mut self,
        statement: vir_typed::Statement,
        state: &mut FoldUnfoldState,
        skip_automatic_close_ref: &mut Vec<vir_typed::Expression>,
    ) -> SpannedEncodingResult<()> {
        assert!(
            statement.is_comment() || statement.is_leak_all() || !statement.position().is_default(),
            "Statement has default position: {statement}"
        );
        if let vir_typed::Statement::DeadLifetime(dead_lifetime) = statement {
            self.process_dead_lifetime(dead_lifetime, state)?;
            self.add_statements_to_current_block();
            return Ok(());
        }
        if let vir_typed::Statement::Assign(vir_typed::Assign {
            target,
            value: vir_typed::Rvalue::Discriminant(discriminant),
            position,
        }) = statement
        {
            self.process_assign_discriminant(target, discriminant, position, state)?;
            self.add_statements_to_current_block();
            return Ok(());
        }
        let (consumed_permissions, produced_permissions) =
            collect_permission_changes(self.encoder, &statement)?;
        debug!(
            "lower_statement {}: {} → {}",
            statement,
            cjoin(&consumed_permissions),
            cjoin(&produced_permissions)
        );
        match &statement {
            vir_typed::Statement::OpenMutRef(open_mut_ref_statement)
                if !open_mut_ref_statement.is_user_written
                    && state
                        .is_opened_ref(&open_mut_ref_statement.place)?
                        .is_some() =>
            {
                skip_automatic_close_ref.push(open_mut_ref_statement.place.clone());
                return Ok(());
            }
            vir_typed::Statement::CloseMutRef(close_mut_ref_statement)
                if !close_mut_ref_statement.is_user_written
                    && skip_automatic_close_ref.contains(&close_mut_ref_statement.place) =>
            {
                let place = skip_automatic_close_ref.pop().unwrap();
                assert_eq!(place, close_mut_ref_statement.place);
                return Ok(());
            }
            _ => {}
        }
        state.check_consistency();
        let actions = ensure_required_permissions(self, state, consumed_permissions.clone())?;
        self.process_actions(state, actions)?;
        state.remove_permissions(&consumed_permissions)?;
        state.insert_permissions(produced_permissions)?;
        match statement {
            vir_typed::Statement::ObtainMutRef(_) => {
                // The requirements already performed the needed changes.
            }
            vir_typed::Statement::LeakAll(vir_typed::LeakAll {}) => {
                // FIXME: Instead of leaking, we should:
                // 1. Unfold all Owned into MemoryBlock.
                // 2. Deallocate all MemoryBlock.
                // 3. Perform a leak check (this actually should be done always at
                //    the end of the exit block).
                state.clear()?;
            }
            vir_typed::Statement::SetUnionVariant(ref variant_statement) => {
                let position = variant_statement.position();
                // Split the memory block for the union itself.
                let parent = variant_statement.variant_place.get_parent_ref().unwrap();
                let place = parent
                    .get_parent_ref()
                    .unwrap()
                    .clone()
                    .typed_to_middle_expression(self.encoder)?;
                let variant = parent.clone().unwrap_variant().variant_index;
                let encoded_statement = vir_mid::Statement::split_block(
                    place,
                    None,
                    Some(variant.typed_to_middle_type(self.encoder)?),
                    position,
                );
                self.current_statements.push(encoded_statement);
                // Split the memory block for the union's field.
                let place = parent.clone().typed_to_middle_expression(self.encoder)?;
                let encoded_statement =
                    vir_mid::Statement::split_block(place, None, None, position);
                self.current_statements.push(encoded_statement);
                self.current_statements
                    .push(statement.typed_to_middle_statement(self.encoder)?);
            }
            vir_typed::Statement::Pack(pack_statement) => {
                // state.remove_manually_managed(&pack_statement.place)?;
                let position = pack_statement.position();
                let permission =
                    self.get_permission_for_maybe_opened_place(state, &pack_statement.place)?;
                let place = pack_statement
                    .place
                    .clone()
                    .typed_to_middle_expression(self.encoder)?;
                // let permission = pack_statement
                //     .permission
                //     .map(|permission| permission.clone().typed_to_middle_expression(self.encoder))
                //     .transpose()?;
                // let encoded_statement = vir_mid::Statement::fold_owned(place, None, position);
                // FIXME: Code duplication.
                let encoded_statement = match pack_statement.predicate_kind {
                    vir_typed::ast::statement::PredicateKind::Owned => {
                        vir_mid::Statement::fold_owned(place, None, permission, position)
                    }
                    vir_typed::ast::statement::PredicateKind::UniqueRef(predicate_kind) => {
                        // let first_reference = place
                        //     .get_first_dereferenced_reference()
                        //     .expect("TODO: Report a proper error");
                        // let vir_mid::Type::Reference(reference) = first_reference.get_type() else {
                        //     unreachable!()
                        // };
                        // let lifetime = reference.lifetime.clone();
                        vir_mid::Statement::fold_ref(
                            place,
                            predicate_kind.lifetime.typed_to_middle_type(self.encoder)?,
                            vir_mid::ty::Uniqueness::Unique,
                            None,
                            position,
                        )
                    }
                    vir_typed::ast::statement::PredicateKind::FracRef(_) => todo!(),
                };
                self.current_statements.push(encoded_statement);
            }
            vir_typed::Statement::Unpack(unpack_statement) => {
                // state.insert_manually_managed(unpack_statement.place.clone())?;
                let position = unpack_statement.position();
                let permission =
                    self.get_permission_for_maybe_opened_place(state, &unpack_statement.place)?;
                let place = unpack_statement
                    .place
                    .typed_to_middle_expression(self.encoder)?;
                // let permission = unpack_statement
                //     .permission
                //     .map(|permission| permission.clone().typed_to_middle_expression(self.encoder))
                //     .transpose()?;
                // FIXME: Code duplication.
                let encoded_statement = match unpack_statement.predicate_kind {
                    vir_typed::ast::statement::PredicateKind::Owned => {
                        vir_mid::Statement::unfold_owned(place, None, permission, position)
                    }
                    vir_typed::ast::statement::PredicateKind::UniqueRef(predicate_kind) => {
                        // let first_reference = place
                        //     .get_first_dereferenced_reference()
                        //     .expect("TODO: Report a proper error");
                        // let vir_mid::Type::Reference(reference) = first_reference.get_type() else {
                        //     unreachable!()
                        // };
                        // let lifetime = reference.lifetime.clone();
                        vir_mid::Statement::unfold_ref(
                            place,
                            predicate_kind.lifetime.typed_to_middle_type(self.encoder)?,
                            vir_mid::ty::Uniqueness::Unique,
                            None,
                            position,
                        )
                    }
                    vir_typed::ast::statement::PredicateKind::FracRef(predicate_kind) => {
                        vir_mid::Statement::unfold_ref(
                            place,
                            predicate_kind.lifetime.typed_to_middle_type(self.encoder)?,
                            vir_mid::ty::Uniqueness::Shared,
                            None,
                            position,
                        )
                    }
                };
                self.current_statements.push(encoded_statement);
            }
            vir_typed::Statement::Obtain(_) => {
                // Nothing to do because the fold-unfold already handled it.
            }
            vir_typed::Statement::Join(join_statement) => {
                let position = join_statement.position();
                let place = join_statement
                    .place
                    .typed_to_middle_expression(self.encoder)?;
                let encoded_statement = vir_mid::Statement::join_block(place, None, None, position);
                self.current_statements.push(encoded_statement);
            }
            vir_typed::Statement::Split(split_statement) => {
                let position = split_statement.position();
                let place = split_statement
                    .place
                    .typed_to_middle_expression(self.encoder)?;
                let encoded_statement =
                    vir_mid::Statement::split_block(place, None, None, position);
                self.current_statements.push(encoded_statement);
            }
            vir_typed::Statement::ForgetInitialization(forget_statement) => {
                // state.insert_manually_managed(forget_statement.place.clone())?;
                let position = forget_statement.position();
                let place = forget_statement
                    .place
                    .typed_to_middle_expression(self.encoder)?;
                let encoded_statement =
                    vir_mid::Statement::convert_owned_into_memory_block(place, None, position);
                self.current_statements.push(encoded_statement);
            }
            vir_typed::Statement::ForgetInitializationRange(forget_statement) => {
                let position = forget_statement.position();
                let address = forget_statement
                    .address
                    .typed_to_middle_expression(self.encoder)?;
                let start_index = forget_statement
                    .start_index
                    .typed_to_middle_expression(self.encoder)?;
                let end_index = forget_statement
                    .end_index
                    .typed_to_middle_expression(self.encoder)?;
                let encoded_statement = vir_mid::Statement::range_convert_owned_into_memory_block(
                    address,
                    start_index,
                    end_index,
                    position,
                );
                self.current_statements.push(encoded_statement);
            }
            vir_typed::Statement::InhalePredicate(inhale_statement) => {
                if let vir_typed::Predicate::OwnedNonAliased(predicate) =
                    &inhale_statement.predicate
                {
                    if predicate.place.get_last_dereferenced_reference().is_some() {
                        // We are inhale Owned of a pointer dereference. This,
                        // currently, can happen only in the encoding of
                        // `Drop::drop` where we replace `&mut self` with `self`
                        // by opening it. Therefore, we need to mark `self` as
                        // openned.
                        let base = predicate.place.get_base();
                        assert_eq!(base.name, "_1", "self should be _1, got: {base}");
                        state.open_ref(predicate.place.clone(), None)?;
                    }
                }
                let inhale_statement = inhale_statement.typed_to_middle_statement(self.encoder)?;
                self.current_statements
                    .push(vir_mid::Statement::InhalePredicate(inhale_statement));
            }
            vir_typed::Statement::InhaleExpression(mut inhale_statement) => {
                if self.check_mode.unwrap() != CheckMode::PurificationFunctional {
                    // inhale_statement.expression =
                    //     super::unfolding_expressions::add_unfolding_expressions(
                    //         inhale_statement.expression,
                    //     )?;
                    inhale_statement.expression = super::eval_using::wrap_in_eval_using(
                        self.encoder,
                        state,
                        inhale_statement.expression,
                    )?;
                }
                let inhale_statement = inhale_statement.typed_to_middle_statement(self.encoder)?;
                self.current_statements
                    .push(vir_mid::Statement::InhaleExpression(inhale_statement));
            }
            vir_typed::Statement::ExhaleExpression(mut exhale_statement) => {
                if self.check_mode.unwrap() != CheckMode::PurificationFunctional {
                    // exhale_statement.expression =
                    //     super::unfolding_expressions::add_unfolding_expressions(
                    //         exhale_statement.expression,
                    //     )?;
                    exhale_statement.expression = super::eval_using::wrap_in_eval_using(
                        self.encoder,
                        state,
                        exhale_statement.expression,
                    )?;
                }
                let exhale_statement = exhale_statement.typed_to_middle_statement(self.encoder)?;
                self.current_statements
                    .push(vir_mid::Statement::ExhaleExpression(exhale_statement));
            }
            vir_typed::Statement::Assert(mut assert_statement) => {
                if self.check_mode.unwrap() != CheckMode::PurificationFunctional {
                    assert_statement.expression = super::eval_using::wrap_in_eval_using(
                        self.encoder,
                        state,
                        assert_statement.expression,
                    )?;
                    // super::unfolding_expressions::add_unfolding_expressions(
                    //     assert_statement.expression,
                    // )?;
                }
                let assert_statement = assert_statement.typed_to_middle_statement(self.encoder)?;
                self.current_statements
                    .push(vir_mid::Statement::Assert(assert_statement));
            }
            vir_typed::Statement::OpenMutRef(open_mut_ref_statement) => {
                if !open_mut_ref_statement.is_user_written
                    && state
                        .is_opened_ref(&open_mut_ref_statement.place)?
                        .is_some()
                {
                    // skip_automatic_close_ref.push(open_mut_ref_statement.place.clone());
                    unreachable!();
                } else {
                    state.open_ref(open_mut_ref_statement.place.clone(), None)?;
                    let lifetime = open_mut_ref_statement
                        .lifetime
                        .typed_to_middle_type(self.encoder)?;
                    let lifetime_token_permission = open_mut_ref_statement
                        .lifetime_token_permission
                        .typed_to_middle_expression(self.encoder)?;
                    let place = open_mut_ref_statement
                        .place
                        .typed_to_middle_expression(self.encoder)?;
                    let position = open_mut_ref_statement.position;
                    let encoded_statement = vir_mid::Statement::open_mut_ref(
                        lifetime,
                        lifetime_token_permission,
                        place,
                        position,
                    );
                    self.current_statements.push(encoded_statement);
                }
            }
            vir_typed::Statement::CloseMutRef(close_mut_ref_statement) => {
                if !close_mut_ref_statement.is_user_written
                    && skip_automatic_close_ref.contains(&close_mut_ref_statement.place)
                {
                    unreachable!();
                    // let place = skip_automatic_close_ref.pop().unwrap();
                    // assert_eq!(place, close_mut_ref_statement.place);
                } else {
                    assert!(state.close_ref(&close_mut_ref_statement.place)?.is_none());
                    let lifetime = close_mut_ref_statement
                        .lifetime
                        .typed_to_middle_type(self.encoder)?;
                    let lifetime_token_permission = close_mut_ref_statement
                        .lifetime_token_permission
                        .typed_to_middle_expression(self.encoder)?;
                    let place = close_mut_ref_statement
                        .place
                        .typed_to_middle_expression(self.encoder)?;
                    let position = close_mut_ref_statement.position;
                    let encoded_statement = vir_mid::Statement::close_mut_ref(
                        lifetime,
                        lifetime_token_permission,
                        place,
                        position,
                    );
                    self.current_statements.push(encoded_statement);
                }
            }
            vir_typed::Statement::OpenFracRef(open_frac_ref_statement) => {
                if !open_frac_ref_statement.is_user_written
                    && state
                        .is_opened_ref(&open_frac_ref_statement.place)?
                        .is_some()
                {
                    skip_automatic_close_ref.push(open_frac_ref_statement.place);
                } else {
                    state.open_ref(
                        open_frac_ref_statement.place.clone(),
                        Some(open_frac_ref_statement.predicate_permission_amount.clone()),
                    )?;
                    let lifetime = open_frac_ref_statement
                        .lifetime
                        .typed_to_middle_type(self.encoder)?;
                    let predicate_permission_amount = open_frac_ref_statement
                        .predicate_permission_amount
                        .typed_to_middle_expression(self.encoder)?;
                    let lifetime_token_permission = open_frac_ref_statement
                        .lifetime_token_permission
                        .typed_to_middle_expression(self.encoder)?;
                    let place = open_frac_ref_statement
                        .place
                        .typed_to_middle_expression(self.encoder)?;
                    let position = open_frac_ref_statement.position;
                    let encoded_statement = vir_mid::Statement::open_frac_ref(
                        lifetime,
                        predicate_permission_amount,
                        lifetime_token_permission,
                        place,
                        position,
                    );
                    self.current_statements.push(encoded_statement);
                }
            }
            vir_typed::Statement::CloseFracRef(close_frac_ref_statement) => {
                if !close_frac_ref_statement.is_user_written
                    && skip_automatic_close_ref.contains(&close_frac_ref_statement.place)
                {
                    let place = skip_automatic_close_ref.pop().unwrap();
                    assert_eq!(place, close_frac_ref_statement.place);
                } else {
                    let predicate_permission_amount =
                        state.close_ref(&close_frac_ref_statement.place)?;
                    assert_eq!(
                        predicate_permission_amount.unwrap(),
                        close_frac_ref_statement.predicate_permission_amount
                    );
                    let lifetime = close_frac_ref_statement
                        .lifetime
                        .typed_to_middle_type(self.encoder)?;
                    let predicate_permission_amount = close_frac_ref_statement
                        .predicate_permission_amount
                        .typed_to_middle_expression(self.encoder)?;
                    let lifetime_token_permission = close_frac_ref_statement
                        .lifetime_token_permission
                        .typed_to_middle_expression(self.encoder)?;
                    let place = close_frac_ref_statement
                        .place
                        .typed_to_middle_expression(self.encoder)?;
                    let position = close_frac_ref_statement.position;
                    let encoded_statement = vir_mid::Statement::close_frac_ref(
                        lifetime,
                        lifetime_token_permission,
                        place,
                        predicate_permission_amount,
                        position,
                    );
                    self.current_statements.push(encoded_statement);
                }
            }
            vir_typed::Statement::CopyPlace(copy_place_statement) => {
                let target_place = copy_place_statement
                    .target
                    .typed_to_middle_expression(self.encoder)?;
                let source_permission = self
                    .get_permission_for_maybe_opened_place(state, &copy_place_statement.source)?;
                // if let Some(predicate_permission_amount) =
                //     state.is_opened_ref(&copy_place_statement.source)?
                // {
                //     predicate_permission_amount
                //         .as_ref()
                //         .map(|amount| amount.clone().typed_to_middle_expression(self.encoder))
                //         .transpose()?
                // } else {
                //     None
                // };
                let source_place = copy_place_statement
                    .source
                    .typed_to_middle_expression(self.encoder)?;
                let encoded_statement = vir_mid::Statement::copy_place(
                    target_place,
                    source_place,
                    source_permission,
                    copy_place_statement.position,
                );
                self.current_statements.push(encoded_statement);
            }
            vir_typed::Statement::Havoc(havoc_statement) => {
                // The procedure encoder provides only Owned predicates. Based
                // on the place and whether the reference is opened or not, we
                // produce the actual predicate.
                let predicate = match havoc_statement.predicate {
                    vir_typed::Predicate::LifetimeToken(_) => todo!(),
                    vir_typed::Predicate::MemoryBlockStack(predicate) => {
                        vir_mid::Predicate::MemoryBlockStack(
                            predicate.typed_to_middle_predicate(self.encoder)?,
                        )
                    }
                    vir_typed::Predicate::MemoryBlockStackDrop(_) => todo!(),
                    vir_typed::Predicate::MemoryBlockHeap(_) => todo!(),
                    vir_typed::Predicate::MemoryBlockHeapRange(_) => todo!(),
                    vir_typed::Predicate::MemoryBlockHeapDrop(_) => todo!(),
                    vir_typed::Predicate::OwnedNonAliased(predicate) => {
                        // TODO: Take into account whether the reference is opened or not.
                        if let Some((lifetime, uniqueness)) = predicate.place.get_dereference_kind()
                        {
                            let lifetime = lifetime.typed_to_middle_type(self.encoder)?;
                            let place = predicate.place.typed_to_middle_expression(self.encoder)?;
                            match uniqueness {
                                vir_typed::ty::Uniqueness::Unique => {
                                    vir_mid::Predicate::unique_ref(
                                        lifetime,
                                        place,
                                        predicate.position,
                                    )
                                }
                                vir_typed::ty::Uniqueness::Shared => vir_mid::Predicate::frac_ref(
                                    lifetime,
                                    place,
                                    predicate.position,
                                ),
                            }
                        } else {
                            vir_mid::Predicate::OwnedNonAliased(
                                predicate.typed_to_middle_predicate(self.encoder)?,
                            )
                        }
                    }
                    vir_typed::Predicate::OwnedRange(_) => todo!(),
                    vir_typed::Predicate::OwnedSet(_) => todo!(),
                    vir_typed::Predicate::UniqueRef(_) => todo!(),
                    vir_typed::Predicate::UniqueRefRange(_) => todo!(),
                    vir_typed::Predicate::FracRef(_) => todo!(),
                    vir_typed::Predicate::FracRefRange(_) => todo!(),
                };
                let encoded_statement =
                    vir_mid::Statement::havoc(predicate, havoc_statement.position);
                self.current_statements.push(encoded_statement);
            }
            _ => {
                self.current_statements
                    .push(statement.typed_to_middle_statement(self.encoder)?);
            }
        }
        self.add_statements_to_current_block();
        Ok(())
    }

    fn add_statements_to_current_block(&mut self) {
        let new_block = self
            .basic_blocks
            .get_mut(self.current_label.as_ref().unwrap())
            .unwrap();
        new_block
            .statements
            .extend(std::mem::take(&mut self.current_statements));
    }

    fn get_permission_for_maybe_opened_place(
        &self,
        state: &FoldUnfoldState,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<Option<vir_mid::VariableDecl>> {
        if let Some(predicate_permission_amount) = state.is_opened_ref(place)? {
            Ok(predicate_permission_amount
                .as_ref()
                .map(|amount| amount.clone().typed_to_middle_expression(self.encoder))
                .transpose()?)
        } else {
            Ok(None)
        }
    }

    #[tracing::instrument(level = "debug", skip(self, actions))]
    fn process_actions(
        &mut self,
        state: &FoldUnfoldState,
        actions: Vec<Action>,
    ) -> SpannedEncodingResult<()> {
        for action in actions {
            debug!("  action: {}", action);
            let statement = match action {
                Action::Unfold(FoldingActionState {
                    kind: PermissionKind::Owned,
                    place,
                    enum_variant: _,
                    condition,
                }) => {
                    if let Some((lifetime, uniqueness)) = place.get_dereference_kind() {
                        let position = place.position();
                        if let Some(predicate_permission_amount) = state.is_opened_ref(&place)? {
                            let predicate_permission_amount = predicate_permission_amount
                                .as_ref()
                                .map(|amount| {
                                    amount.clone().typed_to_middle_expression(self.encoder)
                                })
                                .transpose()?;
                            vir_mid::Statement::unfold_owned(
                                place.typed_to_middle_expression(self.encoder)?,
                                condition,
                                predicate_permission_amount,
                                position,
                            )
                        } else {
                            vir_mid::Statement::unfold_ref(
                                place.typed_to_middle_expression(self.encoder)?,
                                lifetime.typed_to_middle_type(self.encoder)?,
                                uniqueness.typed_to_middle_type(self.encoder)?,
                                condition,
                                position,
                            )
                        }
                    } else {
                        let position = place.position();
                        vir_mid::Statement::unfold_owned(
                            place.typed_to_middle_expression(self.encoder)?,
                            condition,
                            None,
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
                        if let Some(predicate_permission_amount) = state.is_opened_ref(&place)? {
                            let predicate_permission_amount = predicate_permission_amount
                                .as_ref()
                                .map(|amount| {
                                    amount.clone().typed_to_middle_expression(self.encoder)
                                })
                                .transpose()?;
                            vir_mid::Statement::fold_owned(
                                place.typed_to_middle_expression(self.encoder)?,
                                condition,
                                predicate_permission_amount,
                                position,
                            )
                        } else {
                            vir_mid::Statement::fold_ref(
                                place.typed_to_middle_expression(self.encoder)?,
                                lifetime.typed_to_middle_type(self.encoder)?,
                                uniqueness.typed_to_middle_type(self.encoder)?,
                                condition,
                                position,
                            )
                        }
                    } else {
                        let position = place.position();
                        vir_mid::Statement::fold_owned(
                            place.typed_to_middle_expression(self.encoder)?,
                            condition,
                            None,
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
                        place.typed_to_middle_expression(self.encoder)?,
                        condition,
                        enum_variant
                            .map(|variant| variant.typed_to_middle_expression(self.encoder))
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
                        place.typed_to_middle_expression(self.encoder)?,
                        condition,
                        enum_variant
                            .map(|variant| variant.typed_to_middle_expression(self.encoder))
                            .transpose()?,
                        position,
                    )
                }
                Action::OwnedIntoMemoryBlock(ConversionState { place, condition }) => {
                    let position = place.position();
                    vir_mid::Statement::convert_owned_into_memory_block(
                        place.typed_to_middle_expression(self.encoder)?,
                        condition,
                        position,
                    )
                }
                Action::RestoreMutBorrowed(RestorationState {
                    lifetime,
                    place,
                    is_reborrow,
                    condition,
                }) => {
                    let position = place.position();
                    vir_mid::Statement::restore_mut_borrowed(
                        lifetime.typed_to_middle_type(self.encoder)?,
                        place.typed_to_middle_expression(self.encoder)?,
                        is_reborrow,
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
        Ok(())
    }

    fn process_dead_lifetime_for_predicate_state(
        &mut self,
        statement: &vir_typed::DeadLifetime,
        state: &mut PredicateStateOnPath,
        condition: Option<vir_mid::BlockMarkerCondition>,
    ) -> SpannedEncodingResult<()> {
        let Some(DeadLifetimeReport {dead_dereferences, dead_references, places_with_dead_lifetimes, blocked_dead_dereferences}) =
            state.mark_lifetime_dead(&statement.lifetime)? else {
            return Ok(());
        };
        for place in dead_references {
            let place = place.typed_to_middle_expression(self.encoder)?;
            let target_position = place.position();
            let vir_mid::Type::Reference(reference_type) = place.get_type() else {
                unreachable!();
            };
            let target_type = (*reference_type.target_type).clone();
            self.current_statements
                .push(vir_mid::Statement::unfold_owned(
                    place.clone(),
                    condition.clone(),
                    None,
                    statement.position,
                ));
            self.current_statements
                .push(vir_mid::Statement::dead_reference(
                    place.deref(target_type, target_position),
                    None,
                    condition.clone(),
                    statement.position,
                ));
        }
        for place in dead_dereferences {
            let place = place.typed_to_middle_expression(self.encoder)?;
            self.current_statements
                .push(vir_mid::Statement::dead_reference(
                    place,
                    None,
                    condition.clone(),
                    statement.position,
                ));
        }
        for PlaceWithDeadLifetimes { place, lifetime } in places_with_dead_lifetimes {
            let place = place.typed_to_middle_expression(self.encoder)?;
            self.current_statements
                .push(vir_mid::Statement::dead_lifetime(
                    place,
                    lifetime.typed_to_middle_type(self.encoder)?,
                    condition.clone(),
                    statement.position,
                ));
        }
        for (place, reborrowing_lifetime) in blocked_dead_dereferences {
            let place = place.typed_to_middle_expression(self.encoder)?;
            let reborowing_lifetime = reborrowing_lifetime.typed_to_middle_type(self.encoder)?;
            self.current_statements
                .push(vir_mid::Statement::dead_reference(
                    place,
                    Some(reborowing_lifetime),
                    condition.clone(),
                    statement.position,
                ));
        }
        Ok(())
    }

    fn process_dead_lifetime(
        &mut self,
        statement: vir_typed::DeadLifetime,
        state: &mut FoldUnfoldState,
    ) -> SpannedEncodingResult<()> {
        for predicate in state.iter_mut()? {
            match predicate {
                PredicateState::Unconditional(state) => {
                    self.process_dead_lifetime_for_predicate_state(&statement, state, None)?;
                }
                PredicateState::Conditional(states) => {
                    for (condition, conditional_predicate_state) in states {
                        self.process_dead_lifetime_for_predicate_state(
                            &statement,
                            conditional_predicate_state,
                            Some(condition.clone()),
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    fn process_assign_discriminant(
        &mut self,
        target: vir_typed::Expression,
        value: vir_typed::ast::rvalue::Discriminant,
        position: vir_typed::Position,
        state: &mut FoldUnfoldState,
    ) -> SpannedEncodingResult<()> {
        let source_permission = value
            .source_permission
            .map(|permission| permission.typed_to_middle_expression(self.encoder))
            .transpose()?;
        let (conditions, mut actions) = try_ensure_enum_discriminant_by_unfolding(
            self,
            state,
            &value.place,
            PermissionKind::Owned,
        )?;
        ensure_required_permission(
            self,
            state,
            super::permission::Permission::new(target.clone(), PermissionKind::MemoryBlock),
            &mut actions,
        )?;
        self.process_actions(state, actions)?;
        state.remove_permission(&super::permission::Permission::new(
            target.clone(),
            PermissionKind::MemoryBlock,
        ))?;
        state.insert_permission(super::permission::Permission::new(
            target.clone(),
            PermissionKind::Owned,
        ))?;
        let statement = vir_mid::Statement::assign(
            target.typed_to_middle_expression(self.encoder)?,
            vir_mid::Rvalue::discriminant(
                conditions,
                value.place.typed_to_middle_expression(self.encoder)?,
                source_permission,
            ),
            position,
        );
        self.current_statements.push(statement);
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

    pub(super) fn render_crash_graphviz(&self, label_markers: Option<&FxHashMap<String, bool>>) {
        self.to_crashing_graphviz("graphviz_method_custom_foldunfold", label_markers);
    }

    pub(super) fn cancel_crash_graphviz(mut self) {
        self.graphviz_on_crash = false;
    }
}
