use self::{
    builtin_function_encoder::BuiltinFuncAppEncoder, initialisation::InitializationData,
    lifetimes::LifetimesEncoder, specification_blocks::SpecificationBlocks,
};
use super::MirProcedureEncoderInterface;
use crate::encoder::{
    errors::{ErrorCtxt, PanicCause, SpannedEncodingResult, WithSpan},
    mir::{
        casts::CastsEncoderInterface,
        constants::ConstantsEncoderInterface,
        contracts::{ContractsEncoderInterface, ProcedureContractMirDef},
        errors::ErrorInterface,
        generics::MirGenericsEncoderInterface,
        panics::MirPanicsEncoderInterface,
        places::PlacesEncoderInterface,
        predicates::MirPredicateEncoderInterface,
        pure::{PureFunctionEncoderInterface, SpecificationEncoderInterface},
        spans::SpanInterface,
        specifications::SpecificationsInterface,
        type_layouts::MirTypeLayoutsEncoderInterface,
    },
    mir_encoder::PRECONDITION_LABEL,
    Encoder,
};
use log::debug;
use prusti_common::config;
use prusti_interface::environment::{
    debug_utils::to_text::ToText,
    mir_analyses::{
        allocation::{compute_definitely_allocated, DefinitelyAllocatedAnalysisResult},
        initialization::{compute_definitely_initialized, DefinitelyInitializedAnalysisResult},
    },
    mir_body::borrowck::{facts::RichLocation, lifetimes::Lifetimes},
    Procedure,
};
use prusti_rustc_interface::{
    data_structures::graph::WithStartNode,
    hir::def_id::DefId,
    middle::{mir, ty, ty::subst::SubstsRef},
    span::Span,
};
use rustc_hash::FxHashSet;
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    common::{
        check_mode::CheckMode,
        expression::{BinaryOperationHelpers, UnaryOperationHelpers},
        position::Positioned,
    },
    high::{
        self as vir_high,
        builders::procedure::{
            BasicBlockBuilder, ProcedureBuilder, SuccessorBuilder, SuccessorExitKind,
        },
        operations::{lifetimes::WithLifetimes, ty::Typed},
    },
};

mod builtin_function_encoder;
mod elaborate_drops;
mod ghost;
mod initialisation;
mod lifetimes;
mod loops;
mod scc;
mod specification_blocks;

pub(super) fn encode_procedure<'v, 'tcx: 'v>(
    encoder: &mut Encoder<'v, 'tcx>,
    def_id: DefId,
    check_mode: CheckMode,
) -> SpannedEncodingResult<vir_high::ProcedureDecl> {
    let procedure = Procedure::new(encoder.env(), def_id);
    let tcx = encoder.env().tcx();
    let (mir, lifetimes) = self::elaborate_drops::elaborate_drops(encoder, def_id, &procedure)?;
    let mir = &mir; // Mark body as immutable.
    let move_env = self::initialisation::create_move_data_param_env(tcx, mir, def_id);
    let init_data = InitializationData::new(tcx, mir, &move_env);
    let locals_without_explicit_allocation: BTreeSet<_> = mir.vars_and_temps_iter().collect();
    let specification_blocks = SpecificationBlocks::build(tcx, mir, &procedure);
    let initialization = compute_definitely_initialized(def_id, mir, encoder.env().tcx());
    let allocation = compute_definitely_allocated(def_id, mir);
    let lifetime_count = lifetimes.lifetime_count();
    let lifetime_token_permission = None;
    let old_lifetime_ctr: usize = 0;
    let function_call_ctr: usize = 0;
    let derived_lifetimes_yet_to_kill: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let reborrow_lifetimes_to_remove_for_block: BTreeMap<mir::BasicBlock, BTreeSet<String>> =
        BTreeMap::new();
    let points_to_reborrow: BTreeSet<vir_high::Local> = BTreeSet::new();
    let current_basic_block = None;
    let mut procedure_encoder = ProcedureEncoder {
        encoder,
        def_id,
        check_mode,
        procedure: &procedure,
        mir,
        init_data,
        initialization,
        allocation,
        lifetimes,
        reachable_blocks: Default::default(),
        specification_blocks,
        specification_block_encoding: Default::default(),
        loop_invariant_encoding: Default::default(),
        check_panics: config::check_panics() && check_mode != CheckMode::CoreProof,
        locals_without_explicit_allocation,
        used_locals: Default::default(),
        fresh_id_generator: 0,
        lifetime_count,
        lifetime_token_permission,
        old_lifetime_ctr,
        function_call_ctr,
        derived_lifetimes_yet_to_kill,
        points_to_reborrow,
        reborrow_lifetimes_to_remove_for_block,
        current_basic_block,
    };
    procedure_encoder.encode()
}

struct ProcedureEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p mut Encoder<'v, 'tcx>,
    def_id: DefId,
    check_mode: CheckMode,
    procedure: &'p Procedure<'tcx>,
    mir: &'p mir::Body<'tcx>,
    init_data: InitializationData<'p, 'tcx>,
    initialization: DefinitelyInitializedAnalysisResult<'tcx>,
    allocation: DefinitelyAllocatedAnalysisResult,
    lifetimes: Lifetimes,
    /// Blocks that we managed to reach when traversing from the entry block.
    reachable_blocks: FxHashSet<mir::BasicBlock>,
    /// Information about the specification blocks.
    specification_blocks: SpecificationBlocks,
    /// Specifications to be inserted at the given point.
    specification_block_encoding: BTreeMap<mir::BasicBlock, Vec<vir_high::Statement>>,
    /// The loop invariant to be inserted at the end of the given basic block.
    loop_invariant_encoding: BTreeMap<mir::BasicBlock, vir_high::Statement>,
    check_panics: bool,
    /// Locals that are not explicitly allocated or deallocated with
    /// `StorageLive`/`StorageDead`. Such locals are assumed to be alive through
    /// the entire body of the function.
    locals_without_explicit_allocation: BTreeSet<mir::Local>,
    /// Locals that are used in the function. The unused locals are assumed to
    /// be a side effect of specification generation code and are not generated.
    used_locals: BTreeSet<mir::Local>,
    fresh_id_generator: usize,
    lifetime_count: usize,
    lifetime_token_permission: Option<vir_high::VariableDecl>,
    old_lifetime_ctr: usize,
    function_call_ctr: usize,
    derived_lifetimes_yet_to_kill: BTreeMap<String, BTreeSet<String>>,
    points_to_reborrow: BTreeSet<vir_high::Local>,
    reborrow_lifetimes_to_remove_for_block: BTreeMap<mir::BasicBlock, BTreeSet<String>>,
    current_basic_block: Option<mir::BasicBlock>,
}

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    fn encode(&mut self) -> SpannedEncodingResult<vir_high::ProcedureDecl> {
        let name = format!(
            "{}${}",
            self.encoder.encode_item_name(self.def_id),
            self.check_mode
        );
        let (allocate_parameters, deallocate_parameters) = self.encode_parameters()?;
        let (allocate_returns, deallocate_returns) = self.encode_returns()?;
        self.lifetime_token_permission =
            Some(self.fresh_ghost_variable("lifetime_token_perm_amount", vir_high::Type::MPerm));
        let (assume_preconditions, assert_postconditions) = match self.check_mode {
            CheckMode::CoreProof => {
                // Unsafe functions will come with CheckMode::Both because they
                // are allowed to have preconditions.
                (Vec::new(), Vec::new())
            }
            CheckMode::Both | CheckMode::Specifications => {
                self.encode_functional_specifications()?
            }
        };
        let (assume_lifetime_preconditions, assert_lifetime_postconditions) =
            self.encode_lifetime_specifications()?;
        let mut pre_statements = assume_lifetime_preconditions;
        pre_statements.extend(allocate_parameters);
        pre_statements.extend(assume_preconditions);
        pre_statements.extend(allocate_returns);
        let mut post_statements = assert_postconditions;
        post_statements.extend(deallocate_parameters);
        post_statements.extend(deallocate_returns);
        post_statements.extend(assert_lifetime_postconditions);
        let mut procedure_builder =
            ProcedureBuilder::new(name, self.check_mode, pre_statements, post_statements);
        self.encode_body(&mut procedure_builder)?;
        self.encode_implicit_allocations(&mut procedure_builder)?;
        Ok(procedure_builder.build())
    }

    fn encode_local(
        &mut self,
        mir_local: mir::Local,
    ) -> SpannedEncodingResult<vir_high::expression::Local> {
        let span = self.encoder.get_local_span(self.mir, mir_local)?;
        let position = self
            .encoder
            .register_error(span, ErrorCtxt::Unexpected, self.def_id);
        let variable = self.encoder.encode_local_high(self.mir, mir_local)?;
        self.used_locals.insert(mir_local);
        Ok(vir_high::expression::Local::new_with_pos(
            variable, position,
        ))
    }

    fn encode_place(
        &mut self,
        place: mir::Place<'tcx>,
        use_span: Option<Span>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        self.used_locals.insert(place.local);
        self.encoder.encode_place_high(self.mir, place, use_span)
    }

    fn encode_parameters(
        &mut self,
    ) -> SpannedEncodingResult<(Vec<vir_high::Statement>, Vec<vir_high::Statement>)> {
        let mut allocation = vec![vir_high::Statement::comment(
            "Allocate the parameters.".to_string(),
        )];
        let mut deallocation = vec![vir_high::Statement::comment(
            "Deallocate the parameters.".to_string(),
        )];
        for mir_arg in self.mir.args_iter() {
            let parameter = self.encode_local(mir_arg)?;
            let alloc_statement = vir_high::Statement::inhale_no_pos(
                vir_high::Predicate::owned_non_aliased_no_pos(parameter.clone().into()),
            );
            allocation.push(self.encoder.set_surrounding_error_context_for_statement(
                alloc_statement,
                parameter.position,
                ErrorCtxt::UnexpectedStorageLive,
            )?);
            let mir_type = self.encoder.get_local_type(self.mir, mir_arg)?;
            let size = self.encoder.encode_type_size_expression(mir_type)?;
            let dealloc_statement = vir_high::Statement::exhale_no_pos(
                vir_high::Predicate::memory_block_stack_no_pos(parameter.clone().into(), size),
            );
            deallocation.push(self.encoder.set_surrounding_error_context_for_statement(
                dealloc_statement,
                parameter.position,
                ErrorCtxt::UnexpectedStorageDead,
            )?);
        }
        Ok((allocation, deallocation))
    }

    fn encode_returns(
        &mut self,
    ) -> SpannedEncodingResult<(Vec<vir_high::Statement>, Vec<vir_high::Statement>)> {
        let return_local = self.encode_local(mir::RETURN_PLACE)?;
        let mir_type = self.encoder.get_local_type(self.mir, mir::RETURN_PLACE)?;
        let size = self.encoder.encode_type_size_expression(mir_type)?;
        let alloc_statement = self.encoder.set_surrounding_error_context_for_statement(
            vir_high::Statement::inhale_no_pos(vir_high::Predicate::memory_block_stack_no_pos(
                return_local.clone().into(),
                size,
            )),
            return_local.position,
            ErrorCtxt::UnexpectedStorageLive,
        )?;
        let dealloc_statement = self.encoder.set_surrounding_error_context_for_statement(
            vir_high::Statement::exhale_no_pos(vir_high::Predicate::owned_non_aliased_no_pos(
                return_local.clone().into(),
            )),
            return_local.position,
            ErrorCtxt::UnexpectedStorageDead,
        )?;
        Ok((
            vec![
                vir_high::Statement::comment("Allocate the return place.".to_string()),
                alloc_statement,
            ],
            vec![
                vir_high::Statement::comment("Deallocate the return place.".to_string()),
                dealloc_statement,
            ],
        ))
    }

    fn encode_precondition_expressions(
        &mut self,
        procedure_contract: &ProcedureContractMirDef<'tcx>,
        call_substs: SubstsRef<'tcx>,
        arguments: &[vir_high::Expression],
    ) -> SpannedEncodingResult<Vec<vir_high::Expression>> {
        let mut preconditions = Vec::new();
        for (assertion, assertion_substs) in
            procedure_contract.functional_precondition(self.encoder.env(), call_substs)
        {
            let expression = self.encoder.encode_assertion_high(
                &assertion,
                None,
                arguments,
                None,
                self.def_id,
                assertion_substs,
            )?;
            preconditions.push(expression);
        }
        Ok(preconditions)
    }

    fn encode_postcondition_expressions(
        &mut self,
        procedure_contract: &ProcedureContractMirDef<'tcx>,
        call_substs: SubstsRef<'tcx>,
        arguments: Vec<vir_high::Expression>,
        result: &vir_high::Expression,
        precondition_label: &str,
    ) -> SpannedEncodingResult<Vec<vir_high::Expression>> {
        let mut postconditions = Vec::new();
        let arguments_in_old: Vec<_> = arguments
            .into_iter()
            .map(|argument| {
                let position = argument.position();
                vir_high::Expression::labelled_old(
                    precondition_label.to_string(),
                    argument,
                    position,
                )
            })
            .collect();
        for (assertion, assertion_substs) in
            procedure_contract.functional_postcondition(self.encoder.env(), call_substs)
        {
            let expression = self.encoder.encode_assertion_high(
                &assertion,
                Some(precondition_label),
                &arguments_in_old,
                Some(result),
                self.def_id,
                assertion_substs,
            )?;
            postconditions.push(expression);
        }
        Ok(postconditions)
    }

    fn encode_functional_specifications(
        &mut self,
    ) -> SpannedEncodingResult<(Vec<vir_high::Statement>, Vec<vir_high::Statement>)> {
        let mir_span = self.mir.span;
        let substs = self.encoder.env().identity_substs(self.def_id);
        // Retrieve the contract
        let procedure_contract = self
            .encoder
            .get_mir_procedure_contract_for_def(self.def_id, substs)
            .with_span(mir_span)?;
        let mut preconditions = vec![vir_high::Statement::comment(
            "Assume functional preconditions.".to_string(),
        )];
        let mut arguments: Vec<vir_high::Expression> = Vec::new();
        for local in self.mir.args_iter() {
            arguments.push(self.encode_local(local)?.into());
        }
        for expression in
            self.encode_precondition_expressions(&procedure_contract, substs, &arguments)?
        {
            let assume_statement = self.encoder.set_statement_error_ctxt(
                vir_high::Statement::assume_no_pos(expression),
                mir_span,
                ErrorCtxt::UnexpectedAssumeMethodPrecondition,
                self.def_id,
            )?;
            preconditions.push(assume_statement);
        }
        let old_label = self.encoder.set_statement_error_ctxt(
            vir_high::Statement::old_label_no_pos(PRECONDITION_LABEL.to_string()),
            mir_span,
            ErrorCtxt::UnexpectedAssumeMethodPrecondition,
            self.def_id,
        )?;
        preconditions.push(old_label);
        let mut postconditions = vec![vir_high::Statement::comment(
            "Assert functional postconditions.".to_string(),
        )];
        let result: vir_high::Expression = self.encode_local(mir::RETURN_PLACE)?.into();
        for expression in self.encode_postcondition_expressions(
            &procedure_contract,
            substs,
            arguments,
            &result,
            PRECONDITION_LABEL,
        )? {
            let assert_statement = self.encoder.set_statement_error_ctxt(
                vir_high::Statement::assert_no_pos(expression),
                mir_span,
                ErrorCtxt::AssertMethodPostcondition,
                self.def_id,
            )?;
            postconditions.push(assert_statement);
        }
        Ok((preconditions, postconditions))
    }

    fn encode_implicit_allocations(
        &mut self,
        procedure_builder: &mut ProcedureBuilder,
    ) -> SpannedEncodingResult<()> {
        procedure_builder.add_alloc_statement(vir_high::Statement::comment(
            "Allocate implicitly allocated statements.".to_string(),
        ));
        for local in std::mem::take(&mut self.locals_without_explicit_allocation) {
            if self.used_locals.contains(&local) {
                let encoded_local = self.encode_local(local)?;
                let mir_type = self.encoder.get_local_type(self.mir, local)?;
                let size = self.encoder.encode_type_size_expression(mir_type)?;
                let predicate = vir_high::Predicate::memory_block_stack_no_pos(
                    encoded_local.clone().into(),
                    size,
                );
                procedure_builder.add_alloc_statement(
                    self.encoder.set_surrounding_error_context_for_statement(
                        vir_high::Statement::inhale_no_pos(predicate.clone()),
                        encoded_local.position,
                        ErrorCtxt::UnexpectedStorageLive,
                    )?,
                );
                procedure_builder.add_dealloc_statement(
                    self.encoder.set_surrounding_error_context_for_statement(
                        vir_high::Statement::exhale_no_pos(predicate.clone()),
                        encoded_local.position,
                        ErrorCtxt::UnexpectedStorageLive,
                    )?,
                );
            }
        }
        Ok(())
    }

    fn encode_body(
        &mut self,
        procedure_builder: &mut ProcedureBuilder,
    ) -> SpannedEncodingResult<()> {
        let entry_label = vir_high::BasicBlockId::new("label_entry".to_string());
        let mut block_builder = procedure_builder.create_basic_block_builder(entry_label.clone());
        if self.mir.basic_blocks().is_empty() {
            block_builder.set_successor_exit(SuccessorExitKind::Return);
        } else {
            block_builder.set_successor_jump(vir_high::Successor::Goto(
                self.encode_basic_block_label(self.mir.basic_blocks.start_node()),
            ));
        }
        block_builder.build();
        procedure_builder.set_entry(entry_label);
        self.encode_specification_blocks()?;
        self.reachable_blocks
            .insert(self.mir.basic_blocks.start_node());
        for (bb, data) in
            prusti_rustc_interface::middle::mir::traversal::reverse_postorder(self.mir)
        {
            if !self.specification_blocks.is_specification_block(bb)
                && self.reachable_blocks.contains(&bb)
            {
                self.encode_basic_block(procedure_builder, bb, data)?;
            }
        }
        assert!(
            self.loop_invariant_encoding.is_empty(),
            "not consumed loop invariant: {:?}",
            self.loop_invariant_encoding.keys()
        );
        Ok(())
    }

    fn encode_basic_block(
        &mut self,
        procedure_builder: &mut ProcedureBuilder,
        bb: mir::BasicBlock,
        data: &mir::BasicBlockData<'tcx>,
    ) -> SpannedEncodingResult<()> {
        self.derived_lifetimes_yet_to_kill.clear();
        self.reborrow_lifetimes_to_remove_for_block
            .entry(bb)
            .or_insert_with(BTreeSet::new);
        self.current_basic_block = Some(bb);
        let label = self.encode_basic_block_label(bb);
        let mut block_builder = procedure_builder.create_basic_block_builder(label);
        let mir::BasicBlockData {
            statements,
            terminator,
            ..
        } = data;
        let mut location = mir::Location {
            block: bb,
            statement_index: 0,
        };
        let terminator_index = statements.len();
        let mut original_lifetimes: BTreeSet<String> =
            self.lifetimes.get_loan_live_at_start(location);
        let mut derived_lifetimes: BTreeMap<String, BTreeSet<String>> =
            self.lifetimes.get_origin_contains_loan_at_start(location);
        while location.statement_index < terminator_index {
            self.encode_lft_for_statement_mid(
                &mut block_builder,
                location,
                &mut original_lifetimes,
                &mut derived_lifetimes,
                Some(&statements[location.statement_index]),
            )?;
            self.encode_lifetimes_dead_on_edge(
                &mut block_builder,
                RichLocation::Start(location),
                RichLocation::Mid(location),
            )?;
            self.encode_statement(
                &mut block_builder,
                location,
                &statements[location.statement_index],
            )?;
            self.encode_lifetimes_dead_on_edge(
                &mut block_builder,
                RichLocation::Mid(location),
                RichLocation::Mid(mir::Location {
                    block: location.block,
                    statement_index: location.statement_index + 1,
                }),
            )?;
            location.statement_index += 1;
            if location.statement_index < terminator_index {
                self.encode_lft_for_statement_start(
                    &mut block_builder,
                    location,
                    &mut original_lifetimes,
                    &mut derived_lifetimes,
                    Some(&statements[location.statement_index]),
                )?;
            }
        }
        if let Some(terminator) = terminator {
            self.encode_lft_for_statement_mid(
                &mut block_builder,
                location,
                &mut original_lifetimes,
                &mut derived_lifetimes,
                None,
            )?;
            let terminator = &terminator.kind;
            self.encode_terminator(&mut block_builder, location, terminator)?;
        }
        if let Some(statement) = self.loop_invariant_encoding.remove(&bb) {
            block_builder.add_statement(statement);
        }
        block_builder.build();
        Ok(())
    }

    fn encode_statement(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        statement: &mir::Statement<'tcx>,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_comment(format!("{:?} {:?}", location, statement));
        match &statement.kind {
            mir::StatementKind::StorageLive(local) => {
                self.locals_without_explicit_allocation.remove(local);
                let memory_block = self
                    .encoder
                    .encode_memory_block_for_local(self.mir, *local)?;
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::UnexpectedStorageLive,
                    vir_high::Statement::inhale_no_pos(memory_block),
                )?);
                let memory_block_drop = self
                    .encoder
                    .encode_memory_block_drop_for_local(self.mir, *local)?;
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::UnexpectedStorageLive,
                    vir_high::Statement::inhale_no_pos(memory_block_drop),
                )?);
            }
            mir::StatementKind::StorageDead(local) => {
                self.locals_without_explicit_allocation.remove(local);
                let memory_block = self
                    .encoder
                    .encode_memory_block_for_local(self.mir, *local)?;
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::UnexpectedStorageDead,
                    vir_high::Statement::exhale_no_pos(memory_block),
                )?);
                let memory_block_drop = self
                    .encoder
                    .encode_memory_block_drop_for_local(self.mir, *local)?;
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::UnexpectedStorageDead,
                    vir_high::Statement::exhale_no_pos(memory_block_drop),
                )?);
            }
            mir::StatementKind::Assign(box (target, source)) => {
                let position = self.register_error(location, ErrorCtxt::Unexpected);
                let encoded_target = self
                    .encode_place(*target, None)?
                    .set_default_position(position);
                self.encode_statement_assign(block_builder, location, encoded_target, source)?;
            }
            _ => {
                block_builder.add_comment("encode_statement: not encoded".to_string());
            }
        }
        Ok(())
    }

    fn encode_statement_assign(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        encoded_target: vir_crate::high::Expression,
        source: &mir::Rvalue<'tcx>,
    ) -> SpannedEncodingResult<()> {
        match source {
            mir::Rvalue::Use(operand) => {
                self.encode_assign_operand(block_builder, location, encoded_target, operand)?;
            }
            mir::Rvalue::Repeat(operand, count) => {
                let encoded_operand = self.encode_statement_operand(location, operand)?;
                let encoded_count = self.encoder.compute_array_len(*count);
                let encoded_rvalue = vir_high::Rvalue::repeat(encoded_operand, encoded_count);
                let assign_statement = vir_high::Statement::assign(
                    encoded_target,
                    encoded_rvalue,
                    self.register_error(location, ErrorCtxt::Assign),
                );
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::Assign,
                    assign_statement,
                )?);
            }
            mir::Rvalue::Ref(region, borrow_kind, place) => {
                let is_reborrow = place
                    .iter_projections()
                    .any(|(_ref, projection)| projection == mir::ProjectionElem::Deref);
                let is_mut = matches!(
                    borrow_kind,
                    mir::BorrowKind::Mut {
                        allow_two_phase_borrow: _,
                    }
                );
                let encoded_place = self.encode_place(*place, None)?;
                let region_name = region.to_text();
                let operand_lifetime = vir_high::ty::LifetimeConst { name: region_name };
                let root: vir_high::Expression = self
                    .encoder
                    .encode_local_high(self.mir, place.local)?
                    .into();
                let place_lifetimes = root.get_lifetimes();

                let encoded_rvalue = if is_reborrow {
                    if let vir_high::Expression::Local(local) = &encoded_target {
                        self.points_to_reborrow.insert(local.clone());
                    }
                    vir_high::Rvalue::reborrow(
                        encoded_place,
                        operand_lifetime,
                        place_lifetimes,
                        is_mut,
                        self.lifetime_token_fractional_permission(self.lifetime_count),
                        encoded_target.clone(),
                    )
                } else {
                    vir_high::Rvalue::ref_(
                        encoded_place,
                        operand_lifetime,
                        place_lifetimes,
                        is_mut,
                        self.lifetime_token_fractional_permission(self.lifetime_count),
                        encoded_target.clone(),
                    )
                };
                let assign_statement = vir_high::Statement::assign(
                    encoded_target,
                    encoded_rvalue,
                    self.register_error(location, ErrorCtxt::Assign),
                );
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::Assign,
                    assign_statement,
                )?);
            }
            // mir::Rvalue::ThreadLocalRef(DefId),
            mir::Rvalue::AddressOf(_, place) => {
                let encoded_place = self.encode_place(*place, None)?;
                let encoded_rvalue = vir_high::Rvalue::address_of(encoded_place);
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::Assign,
                    vir_high::Statement::assign_no_pos(encoded_target, encoded_rvalue),
                )?);
            }
            mir::Rvalue::Len(place) => {
                let encoded_place = self.encode_place(*place, None)?;
                let encoded_rvalue = vir_high::Rvalue::len(encoded_place);
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::Assign,
                    vir_high::Statement::assign_no_pos(encoded_target, encoded_rvalue),
                )?);
            }
            // mir::Rvalue::Cast(CastKind, Operand<'tcx>, Ty<'tcx>),
            mir::Rvalue::BinaryOp(op, box (left, right)) => {
                let encoded_left = self.encode_statement_operand(location, left)?;
                let encoded_right = self.encode_statement_operand(location, right)?;
                let kind = self.encode_binary_op_kind(*op)?;
                let encoded_rvalue = vir_high::Rvalue::binary_op(kind, encoded_left, encoded_right);
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::Assign,
                    vir_high::Statement::assign_no_pos(encoded_target, encoded_rvalue),
                )?);
            }
            mir::Rvalue::CheckedBinaryOp(op, box (left, right)) => {
                let encoded_left = self.encode_statement_operand(location, left)?;
                let encoded_right = self.encode_statement_operand(location, right)?;
                let kind = self.encode_binary_op_kind(*op)?;
                let encoded_rvalue =
                    vir_high::Rvalue::checked_binary_op(kind, encoded_left, encoded_right);
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::Assign,
                    vir_high::Statement::assign_no_pos(encoded_target, encoded_rvalue),
                )?);
            }
            // mir::Rvalue::NullaryOp(NullOp, Ty<'tcx>),
            mir::Rvalue::UnaryOp(op, operand) => {
                let encoded_operand = self.encode_statement_operand(location, operand)?;
                let kind = match op {
                    mir::UnOp::Not => vir_high::UnaryOpKind::Not,
                    mir::UnOp::Neg => vir_high::UnaryOpKind::Minus,
                };
                let encoded_rvalue = vir_high::Rvalue::unary_op(kind, encoded_operand);
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::Assign,
                    vir_high::Statement::assign_no_pos(encoded_target, encoded_rvalue),
                )?);
            }
            mir::Rvalue::Discriminant(place) => {
                let encoded_place = self.encode_place(*place, None)?;

                let deref_base = encoded_place.get_dereference_base().cloned();
                let source_permission = self.encode_open_reference(
                    block_builder,
                    location,
                    &deref_base,
                    encoded_place.clone(),
                )?;

                let encoded_rvalue = vir_high::Rvalue::discriminant(
                    encoded_place.clone(),
                    source_permission.clone(),
                );
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::Assign,
                    vir_high::Statement::assign_no_pos(encoded_target, encoded_rvalue),
                )?);

                self.encode_close_reference(
                    block_builder,
                    location,
                    &deref_base,
                    encoded_place,
                    source_permission,
                )?;
            }
            mir::Rvalue::Aggregate(box aggregate_kind, operands) => {
                self.encode_statement_assign_aggregate(
                    block_builder,
                    location,
                    encoded_target,
                    aggregate_kind,
                    operands,
                )?;
            }
            // mir::Rvalue::ShallowInitBox(Operand<'tcx>, Ty<'tcx>),
            _ => {
                block_builder.add_comment("encode_statement_assign: not encoded".to_string());
                unimplemented!("{:?}", source);
            }
        }
        Ok(())
    }

    fn encode_statement_assign_aggregate(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        encoded_target: vir_crate::high::Expression,
        aggregate_kind: &mir::AggregateKind<'tcx>,
        operands: &[mir::Operand<'tcx>],
    ) -> SpannedEncodingResult<()> {
        let ty = match aggregate_kind {
            mir::AggregateKind::Array(_) | mir::AggregateKind::Tuple => {
                encoded_target.get_type().clone()
            }
            mir::AggregateKind::Adt(adt_did, variant_index, _substs, _, active_field_index) => {
                let mut ty = encoded_target.get_type().clone();
                let tcx = self.encoder.env().tcx();
                if ty.is_enum() {
                    let adt_def = tcx.adt_def(*adt_did);
                    let variant_def = &adt_def.variants()[*variant_index];
                    let variant_name = variant_def.ident(tcx).to_string();
                    ty = ty.variant(variant_name.into());
                } else {
                    assert_eq!(
                        variant_index.index(),
                        0,
                        "Unexpected value of the variant index."
                    );
                }
                if let Some(active_field_index) = active_field_index {
                    assert!(ty.is_union());
                    let adt_def = tcx.adt_def(*adt_did);
                    let variant_def = adt_def.non_enum_variant();
                    let field_name = variant_def.fields[*active_field_index]
                        .ident(tcx)
                        .to_string();
                    ty = ty.variant(field_name.into());
                }
                ty
            }
            mir::AggregateKind::Closure(_, _) => unimplemented!(),
            mir::AggregateKind::Generator(_, _, _) => unimplemented!(),
        };
        let mut encoded_operands = Vec::new();
        for operand in operands {
            encoded_operands.push(self.encode_statement_operand(location, operand)?);
        }
        let encoded_rvalue = vir_high::Rvalue::aggregate(ty, encoded_operands);
        block_builder.add_statement(vir_high::Statement::assign(
            encoded_target,
            encoded_rvalue,
            self.register_error(location, ErrorCtxt::Assign),
        ));
        Ok(())
    }

    fn encode_close_reference(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        deref_base: &Option<vir_high::Expression>,
        place: vir_high::Expression,
        permission: Option<vir_high::VariableDecl>,
    ) -> SpannedEncodingResult<()> {
        if let Some(base) = deref_base {
            if let vir_high::ty::Type::Reference(vir_high::ty::Reference {
                lifetime,
                uniqueness,
                ..
            }) = base.get_type()
            {
                if *uniqueness == vir_high::ty::Uniqueness::Unique {
                    block_builder.add_statement(self.set_statement_error(
                        location,
                        ErrorCtxt::CloseMutRef,
                        vir_high::Statement::close_mut_ref_no_pos(
                            lifetime.clone(),
                            self.lifetime_token_fractional_permission(self.lifetime_count),
                            place,
                        ),
                    )?);
                } else {
                    block_builder.add_statement(self.set_statement_error(
                        location,
                        ErrorCtxt::CloseFracRef,
                        vir_high::Statement::close_frac_ref_no_pos(
                            lifetime.clone(),
                            self.lifetime_token_fractional_permission(self.lifetime_count),
                            place,
                            permission.unwrap(),
                        ),
                    )?);
                }
            } else {
                unreachable!();
            };
        }
        Ok(())
    }

    fn encode_open_reference(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        deref_base: &Option<vir_high::Expression>,
        place: vir_high::Expression,
    ) -> SpannedEncodingResult<Option<vir_high::VariableDecl>> {
        let mut variable = None;
        if let Some(base) = deref_base {
            if let vir_high::ty::Type::Reference(vir_high::ty::Reference {
                lifetime,
                uniqueness,
                ..
            }) = base.get_type()
            {
                if *uniqueness == vir_high::ty::Uniqueness::Unique {
                    block_builder.add_statement(self.set_statement_error(
                        location,
                        ErrorCtxt::OpenMutRef,
                        vir_high::Statement::open_mut_ref_no_pos(
                            lifetime.clone(),
                            self.lifetime_token_fractional_permission(self.lifetime_count),
                            place,
                        ),
                    )?);
                } else {
                    let permission =
                        self.fresh_ghost_variable("tmp_frac_ref_perm", vir_high::Type::MPerm);
                    variable = Some(permission.clone());
                    block_builder.add_statement(self.set_statement_error(
                        location,
                        ErrorCtxt::OpenFracRef,
                        vir_high::Statement::open_frac_ref_no_pos(
                            lifetime.clone(),
                            permission,
                            self.lifetime_token_fractional_permission(self.lifetime_count),
                            place,
                        ),
                    )?);
                }
            } else {
                unreachable!("place: {} deref_base: {:?}", place, deref_base);
            }
        };
        Ok(variable)
    }

    fn encode_assign_operand(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        encoded_target: vir_crate::high::Expression,
        operand: &mir::Operand<'tcx>,
    ) -> SpannedEncodingResult<()> {
        let span = self.encoder.get_span_of_location(self.mir, location);

        let deref_base = encoded_target.get_dereference_base().cloned();
        let target_permission = self.encode_open_reference(
            block_builder,
            location,
            &deref_base,
            encoded_target.clone(),
        )?;
        match operand {
            mir::Operand::Move(source) => {
                let encoded_source = self.encode_place(*source, Some(span))?;
                if let vir_high::Expression::Local(local_source) = &encoded_source {
                    if self.points_to_reborrow.contains(local_source) {
                        if let vir_high::Expression::Local(local_target) = &encoded_target {
                            self.points_to_reborrow.insert(local_target.clone());
                        }
                    }
                }
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::MovePlace,
                    vir_high::Statement::move_place_no_pos(encoded_target.clone(), encoded_source),
                )?);
            }
            mir::Operand::Copy(source) => {
                let encoded_source = self.encode_place(*source, Some(span))?;
                assert!(
                    encoded_source.is_place(),
                    "{} is not place (encoded from: {:?}",
                    encoded_source,
                    source
                );

                let deref_base = encoded_source.get_dereference_base().cloned();
                let source_permission = self.encode_open_reference(
                    block_builder,
                    location,
                    &deref_base,
                    encoded_source.clone(),
                )?;

                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::CopyPlace,
                    vir_high::Statement::copy_place_no_pos(
                        encoded_target.clone(),
                        encoded_source.clone(),
                        source_permission.clone(),
                    ),
                )?);

                self.encode_close_reference(
                    block_builder,
                    location,
                    &deref_base,
                    encoded_source,
                    source_permission,
                )?;
            }
            mir::Operand::Constant(constant) => {
                let encoded_constant = self
                    .encoder
                    .encode_constant_high(constant)
                    .with_span(span)?;
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::WritePlace,
                    vir_high::Statement::write_place_no_pos(
                        encoded_target.clone(),
                        encoded_constant,
                    ),
                )?);
            }
        }

        self.encode_close_reference(
            block_builder,
            location,
            &deref_base,
            encoded_target,
            target_permission,
        )?;

        Ok(())
    }

    fn encode_statement_operand(
        &mut self,
        location: mir::Location,
        operand: &mir::Operand<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Operand> {
        let span = self.encoder.get_span_of_location(self.mir, location);
        let encoded_operand = match operand {
            mir::Operand::Move(source) => {
                let position = self.register_error(location, ErrorCtxt::MovePlace);
                let encoded_source = self
                    .encode_place(*source, Some(span))?
                    .set_default_position(position);
                vir_high::Operand::new(vir_high::OperandKind::Move, encoded_source)
            }
            mir::Operand::Copy(source) => {
                let position = self.register_error(location, ErrorCtxt::CopyPlace);
                let encoded_source = self
                    .encode_place(*source, Some(span))?
                    .set_default_position(position);
                vir_high::Operand::new(vir_high::OperandKind::Copy, encoded_source)
            }
            mir::Operand::Constant(constant) => {
                let position = self.register_error(location, ErrorCtxt::WritePlace);
                let encoded_constant = self
                    .encoder
                    .encode_constant_high(constant)
                    .with_span(span)?
                    .set_default_position(position);
                vir_high::Operand::new(vir_high::OperandKind::Constant, encoded_constant)
            }
        };
        Ok(encoded_operand)
    }

    fn encode_binary_op_kind(
        &self,
        op: mir::BinOp,
    ) -> SpannedEncodingResult<vir_high::BinaryOpKind> {
        let kind = match op {
            mir::BinOp::Add => vir_high::BinaryOpKind::Add,
            mir::BinOp::Sub => vir_high::BinaryOpKind::Sub,
            mir::BinOp::Mul => vir_high::BinaryOpKind::Mul,
            mir::BinOp::Div => vir_high::BinaryOpKind::Div,
            mir::BinOp::Rem => vir_high::BinaryOpKind::Mod,
            // mir::BinOp::BitXor => vir_high::BinaryOpKind::BitXor,
            // mir::BinOp::BitAnd => vir_high::BinaryOpKind::BitAnd,
            // mir::BinOp::BitOr => vir_high::BinaryOpKind::BitOr,
            // mir::BinOp::Shl => vir_high::BinaryOpKind::Shl,
            // mir::BinOp::Shr => vir_high::BinaryOpKind::Shr,
            mir::BinOp::Eq => vir_high::BinaryOpKind::EqCmp,
            mir::BinOp::Lt => vir_high::BinaryOpKind::LtCmp,
            mir::BinOp::Le => vir_high::BinaryOpKind::LeCmp,
            mir::BinOp::Ne => vir_high::BinaryOpKind::NeCmp,
            mir::BinOp::Ge => vir_high::BinaryOpKind::GeCmp,
            mir::BinOp::Gt => vir_high::BinaryOpKind::GtCmp,
            // mir::BinOp::Offset => vir_high::BinaryOpKind::Offset,
            _ => unimplemented!("op kind: {:?}", op),
        };
        Ok(kind)
    }

    fn needed_derived_lifetimes_for_block(
        &mut self,
        bb: &mir::BasicBlock,
    ) -> BTreeMap<String, BTreeSet<String>> {
        let first_location = mir::Location {
            block: *bb,
            statement_index: 0,
        };
        self.lifetimes
            .get_origin_contains_loan_at_start(first_location)
    }

    fn encode_terminator(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        terminator: &mir::TerminatorKind<'tcx>,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_comment(format!("{:?} {:?}", location, terminator));
        let span = self.encoder.get_span_of_location(self.mir, location);
        use prusti_rustc_interface::middle::mir::TerminatorKind;
        let successor = match &terminator {
            TerminatorKind::Goto { target } => {
                self.encode_lft_for_block(*target, location, block_builder)?;
                SuccessorBuilder::jump(vir_high::Successor::Goto(
                    self.encode_basic_block_label(*target),
                ))
            }
            TerminatorKind::SwitchInt {
                targets,
                discr,
                switch_ty,
            } => self.encode_terminator_switch_int(
                block_builder,
                location,
                span,
                targets,
                discr,
                *switch_ty,
            )?,
            TerminatorKind::Resume => SuccessorBuilder::exit_resume_panic(),
            // TerminatorKind::Abort => {
            //     graph.add_exit_edge(bb, "abort");
            // }
            TerminatorKind::Return => SuccessorBuilder::exit_return(),
            TerminatorKind::Unreachable => {
                block_builder
                    .add_comment("Target marked as unreachable by the compiler".to_string());
                block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                    vir_high::Statement::assert_no_pos(false.into()),
                    span,
                    ErrorCtxt::UnreachableTerminator,
                    self.def_id,
                )?);
                SuccessorBuilder::exit_resume_panic()
            }
            // TerminatorKind::DropAndReplace { target, unwind, .. }
            TerminatorKind::Drop {
                place,
                target,
                unwind,
            } => self.encode_terminator_drop(block_builder, span, *place, *target, unwind)?,
            TerminatorKind::Call {
                func: mir::Operand::Constant(box mir::Constant { literal, .. }),
                args,
                destination,
                target,
                cleanup,
                fn_span,
                from_hir_call: _,
            } => {
                self.encode_terminator_call(
                    block_builder,
                    location,
                    span,
                    literal.ty(),
                    args,
                    *destination,
                    target,
                    cleanup,
                    *fn_span,
                )?;
                // The encoding of the call is expected to set the successor.
                return Ok(());
            }
            TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                cleanup,
            } => self.encode_terminator_assert(
                block_builder,
                span,
                cond,
                *expected,
                msg,
                *target,
                *cleanup,
            )?,
            // TerminatorKind::Yield { .. } => {
            //     graph.add_exit_edge(bb, "yield");
            // }
            // TerminatorKind::GeneratorDrop => {
            //     graph.add_exit_edge(bb, "generator_drop");
            // }
            TerminatorKind::FalseEdge {
                real_target,
                imaginary_target: _,
            }
            | TerminatorKind::FalseUnwind {
                real_target,
                unwind: _,
            } => {
                self.encode_lft_for_block(*real_target, location, block_builder)?;
                SuccessorBuilder::jump(vir_high::Successor::Goto(
                    self.encode_basic_block_label(*real_target),
                ))
            }
            // TerminatorKind::InlineAsm { .. } => {
            //     graph.add_exit_edge(bb, "inline_asm");
            // }
            x => unimplemented!("terminator: {:?}", x),
        };
        block_builder.set_successor(successor);
        Ok(())
    }

    fn encode_terminator_switch_int(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        span: Span,
        targets: &mir::SwitchTargets,
        discr: &mir::Operand<'tcx>,
        switch_ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<SuccessorBuilder> {
        {
            // Check whether we should not omit the spec block.
            let all_targets = targets.all_targets();
            if all_targets.len() == 2 {
                if let Some(spec) = all_targets
                    .iter()
                    .position(|target| self.specification_blocks.is_specification_block(*target))
                {
                    let real_target = all_targets[(spec + 1) % 2];
                    let spec_target = all_targets[spec];
                    block_builder.add_comment(format!("Spefication from block: {:?}", spec_target));
                    if let Some(statements) = self.specification_block_encoding.remove(&spec_target)
                    {
                        block_builder.add_statements(statements);
                    }
                    self.encode_lft_for_block(real_target, location, block_builder)?;
                    return Ok(SuccessorBuilder::jump(vir_high::Successor::Goto(
                        self.encode_basic_block_label(real_target),
                    )));
                }
            }
        }
        let discriminant = self
            .encoder
            .encode_operand_high(self.mir, discr, span)
            .with_default_span(span)?;
        debug!(
            "discriminant: {:?} switch_ty: {:?}",
            discriminant, switch_ty
        );
        let mut successors = Vec::new();
        for (value, target) in targets.iter() {
            let encoded_condition = match switch_ty.kind() {
                ty::TyKind::Bool => {
                    if value == 0 {
                        // If discr is 0 (false)
                        vir_high::Expression::not(discriminant.clone())
                    } else {
                        // If discr is not 0 (true)
                        discriminant.clone()
                    }
                }
                ty::TyKind::Int(_) | ty::TyKind::Uint(_) | ty::TyKind::Char => {
                    vir_high::Expression::equals(
                        discriminant.clone(),
                        self.encoder
                            .encode_int_cast_high(value, switch_ty)
                            .with_span(span)?,
                    )
                }
                x => unreachable!("{:?}", x),
            };
            let encoded_target = self.encode_basic_block_label(target);
            let encoded_target = self.encode_lft_for_block_with_edge(
                target,
                encoded_target,
                location,
                block_builder,
            )?;
            successors.push((encoded_condition, encoded_target));
        }
        let otherwise = self.encode_basic_block_label(targets.otherwise());
        let otherwise = self.encode_lft_for_block_with_edge(
            targets.otherwise(),
            otherwise,
            location,
            block_builder,
        )?;
        successors.push((true.into(), otherwise));
        Ok(SuccessorBuilder::jump(vir_high::Successor::GotoSwitch(
            successors,
        )))
    }

    fn encode_terminator_drop(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        span: Span,
        place: mir::Place<'tcx>,
        target: mir::BasicBlock,
        unwind: &Option<mir::BasicBlock>,
    ) -> SpannedEncodingResult<SuccessorBuilder> {
        let target_block_label = self.encode_basic_block_label(target);

        if config::check_no_drops() {
            let statement = self.encoder.set_statement_error_ctxt(
                vir_high::Statement::assert_no_pos(false.into()),
                span,
                ErrorCtxt::DropCall,
                self.def_id,
            )?;
            block_builder.add_statement(statement);
        }

        // FIXME: Assert that the lifetimes used in type of the place are alive
        // at this point (by exhaling them and inhaling). Do not forget to take
        // into account
        // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.GenericParamDef.html#structfield.pure_wrt_drop
        let argument =
            vir_high::Operand::new(vir_high::OperandKind::Move, self.encode_place(place, None)?);
        let statement = self.encoder.set_statement_error_ctxt(
            vir_high::Statement::consume_no_pos(argument),
            span,
            ErrorCtxt::DropCall,
            self.def_id,
        )?;
        statement.check_no_default_position();
        block_builder.add_statement(statement);
        if let Some(unwind_block) = unwind {
            let encoded_unwind_block_label = self.encode_basic_block_label(*unwind_block);
            Ok(SuccessorBuilder::jump(vir_high::Successor::NonDetChoice(
                target_block_label,
                encoded_unwind_block_label,
            )))
        } else {
            Ok(SuccessorBuilder::jump(vir_high::Successor::Goto(
                target_block_label,
            )))
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn encode_terminator_call(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        span: Span,
        ty: ty::Ty<'tcx>,
        args: &[mir::Operand<'tcx>],
        destination: mir::Place<'tcx>,
        target: &Option<mir::BasicBlock>,
        cleanup: &Option<mir::BasicBlock>,
        _fn_span: Span,
    ) -> SpannedEncodingResult<()> {
        if let ty::TyKind::FnDef(called_def_id, call_substs) = ty.kind() {
            if !self.try_encode_builtin_call(
                block_builder,
                location,
                span,
                *called_def_id,
                call_substs,
                args,
                destination,
                target,
                cleanup,
            )? {
                self.encode_function_call(
                    block_builder,
                    location,
                    span,
                    *called_def_id,
                    call_substs,
                    args,
                    destination,
                    target,
                    cleanup,
                )?;
            }
        } else {
            // Other kind of calls?
            unimplemented!();
        };
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn encode_function_call(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        span: Span,
        called_def_id: DefId,
        call_substs: SubstsRef<'tcx>,
        args: &[mir::Operand<'tcx>],
        destination: mir::Place<'tcx>,
        target: &Option<mir::BasicBlock>,
        cleanup: &Option<mir::BasicBlock>,
    ) -> SpannedEncodingResult<()> {
        // The called method might be a trait method.
        // We try to resolve it to the concrete implementation
        // and type substitutions.
        let (called_def_id, call_substs) =
            self.encoder
                .env()
                .resolve_method_call(self.def_id, called_def_id, call_substs);

        // find static lifetime to exhale
        let mut lifetimes_to_exhale_inhale: Vec<String> = Vec::new();
        let opaque_lifetimes: BTreeMap<String, BTreeSet<String>> =
            self.lifetimes.get_opaque_lifetimes_with_inclusions_names();
        for (lifetime, derived_from) in opaque_lifetimes {
            if derived_from.is_empty() {
                lifetimes_to_exhale_inhale.push(lifetime.to_text());
            }
        }
        assert_eq!(lifetimes_to_exhale_inhale.len(), 1); // there must be exactly one static lifetime

        // find generic argument lifetimes
        let mut subst_lifetimes: Vec<String> = call_substs
            .iter()
            .filter_map(|generic| match generic.unpack() {
                ty::subst::GenericArgKind::Lifetime(region) => Some(region.to_text()),
                _ => None,
            })
            .collect();
        if subst_lifetimes.is_empty() {
            // If subst_lifetimes is empty, check args for a lifetime
            for arg in args {
                if let &mir::Operand::Move(place) = arg {
                    let place_high = self.encode_place(place, None)?;
                    let lifetimes = place_high.get_lifetimes();
                    for lifetime in lifetimes {
                        subst_lifetimes.push(lifetime.name.clone());
                    }
                }
            }
        }
        for lifetime in subst_lifetimes {
            lifetimes_to_exhale_inhale.push(lifetime);
        }

        // construct function lifetime
        self.function_call_ctr += 1;
        let function_call_lifetime_name = format!("lft_function_call_{}", self.function_call_ctr);
        let function_call_lifetime = vir_high::VariableDecl {
            name: function_call_lifetime_name.clone(),
            ty: vir_high::ty::Type::Lifetime,
        };
        let mut derived_from: Vec<vir_high::VariableDecl> = Vec::new();
        for name in &lifetimes_to_exhale_inhale {
            derived_from.push(self.encode_lft_variable(name.to_string())?);
        }
        let function_lifetime_take = vir_high::Statement::lifetime_take_no_pos(
            function_call_lifetime.clone(),
            derived_from.clone(),
            self.lifetime_token_fractional_permission(self.lifetime_count * derived_from.len()),
        );
        block_builder.add_statement(self.set_statement_error(
            location,
            ErrorCtxt::LifetimeEncoding,
            function_lifetime_take,
        )?);
        lifetimes_to_exhale_inhale.push(function_call_lifetime_name);

        // encode subset_base conditions which contain a lifetime which we are going to exhale
        // FIXME: Ideally, before a function call, assert *exactly* what is assumed in the function.
        //   In this case, that is the opaque lifetimes conditions. Finding the right lifetimes
        //   which correspond to the the lifetimes in the function seems to be hard.
        let subset_base: Vec<(String, String)> = self
            .lifetimes
            .get_subset_base_at_mid(location)
            .iter()
            .map(|(x, y)| (x.to_text(), y.to_text()))
            .collect();
        for (lifetime_lhs, lifetime_rhs) in subset_base {
            if lifetimes_to_exhale_inhale.contains(&lifetime_lhs)
                || lifetimes_to_exhale_inhale.contains(&lifetime_rhs)
            {
                self.encode_lft_assert_subset(block_builder, location, lifetime_lhs, lifetime_rhs)?;
            }
        }

        let old_label = self.fresh_old_label();
        block_builder.add_statement(self.encoder.set_statement_error_ctxt(
            vir_high::Statement::old_label_no_pos(old_label.clone()),
            span,
            ErrorCtxt::ProcedureCall,
            self.def_id,
        )?);
        let mut arguments = Vec::new();
        for arg in args {
            arguments.push(
                self.encoder
                    .encode_operand_high(self.mir, arg, span)
                    .with_span(span)?,
            );
            let encoded_arg = self.encode_statement_operand(location, arg)?;
            let statement = vir_high::Statement::consume_no_pos(encoded_arg);
            block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                statement,
                span,
                ErrorCtxt::ProcedureCall,
                self.def_id,
            )?);
        }
        self.encode_exhale_lifetime_tokens(
            block_builder,
            &lifetimes_to_exhale_inhale,
            derived_from.len() + 1,
        )?;

        let procedure_contract = self
            .encoder
            .get_mir_procedure_contract_for_call(self.def_id, called_def_id, call_substs)
            .with_span(span)?;

        for expression in
            self.encode_precondition_expressions(&procedure_contract, call_substs, &arguments)?
        {
            let assert_statement = self.encoder.set_statement_error_ctxt(
                vir_high::Statement::assert_no_pos(expression),
                span,
                ErrorCtxt::ExhaleMethodPrecondition,
                self.def_id,
            )?;
            if self.check_mode != CheckMode::CoreProof {
                block_builder.add_statement(assert_statement);
            }
        }

        if self.encoder.env().tcx().is_closure(called_def_id) {
            // Closure calls are wrapped around std::ops::Fn::call(), which receives
            // two arguments: The closure instance, and the tupled-up arguments
            assert_eq!(args.len(), 2);
            unimplemented!();
        }

        if let Some(target_block) = target {
            let position = self.register_error(location, ErrorCtxt::ProcedureCall);
            let encoded_target_place = self
                .encode_place(destination, None)?
                .set_default_position(position);
            let postcondition_expressions = self.encode_postcondition_expressions(
                &procedure_contract,
                call_substs,
                arguments.clone(),
                &encoded_target_place,
                &old_label,
            )?;
            if let Some(target_place_local) = destination.as_local() {
                let size = self.encoder.encode_type_size_expression(
                    self.encoder.get_local_type(self.mir, target_place_local)?,
                )?;
                let target_memory_block = vir_high::Predicate::memory_block_stack_no_pos(
                    encoded_target_place.clone(),
                    size,
                );
                block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                    vir_high::Statement::exhale_no_pos(target_memory_block.clone()),
                    span,
                    ErrorCtxt::ProcedureCall,
                    self.def_id,
                )?);
                let target_label = self.encode_basic_block_label(*target_block);

                let fresh_destination_label = self.fresh_basic_block_label();
                let mut post_call_block_builder =
                    block_builder.create_basic_block_builder(fresh_destination_label.clone());
                post_call_block_builder.set_successor_jump(vir_high::Successor::Goto(target_label));
                let statement = vir_high::Statement::inhale_no_pos(
                    vir_high::Predicate::owned_non_aliased_no_pos(encoded_target_place.clone()),
                );
                post_call_block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                    statement,
                    span,
                    ErrorCtxt::ProcedureCall,
                    self.def_id,
                )?);
                self.encode_inhale_lifetime_tokens(
                    &mut post_call_block_builder,
                    &lifetimes_to_exhale_inhale,
                    derived_from.len(),
                )?;
                let function_lifetime_return = self.encoder.set_statement_error_ctxt(
                    vir_high::Statement::lifetime_return_no_pos(
                        function_call_lifetime.clone(),
                        derived_from.clone(),
                        self.lifetime_token_fractional_permission(
                            self.lifetime_count * derived_from.len(),
                        ),
                    ),
                    self.mir.span,
                    ErrorCtxt::LifetimeInhale,
                    self.def_id,
                )?;
                post_call_block_builder.add_statement(function_lifetime_return);

                self.encode_lft_for_block(*target_block, location, &mut post_call_block_builder)?;

                for expression in postcondition_expressions {
                    let assume_statement = self.encoder.set_statement_error_ctxt(
                        vir_high::Statement::assume_no_pos(expression),
                        span,
                        ErrorCtxt::UnexpectedAssumeMethodPostcondition,
                        self.def_id,
                    )?;
                    if self.check_mode != CheckMode::CoreProof {
                        post_call_block_builder.add_statement(assume_statement);
                    }
                }
                if self.encoder.is_pure(called_def_id, Some(call_substs))
                    && self.def_id != called_def_id
                {
                    // If we are verifying a pure function, we always need
                    // to encode it as a method
                    //
                    // FIXME: This is not enough, we also need to handle
                    // mutual-recursion case.
                    let (function_name, return_type) = self
                        .encoder
                        .encode_pure_function_use_high(called_def_id, self.def_id, call_substs)
                        .with_span(span)?;
                    let type_arguments = self
                        .encoder
                        .encode_generic_arguments_high(called_def_id, call_substs)
                        .with_span(span)?;
                    let expression = vir_high::Expression::equals(
                        encoded_target_place,
                        vir_high::Expression::function_call(
                            function_name,
                            type_arguments,
                            arguments,
                            return_type,
                        ),
                    );
                    let assume_statement = self.encoder.set_statement_error_ctxt(
                        vir_high::Statement::assume_no_pos(expression),
                        span,
                        ErrorCtxt::UnexpectedAssumeMethodPostcondition,
                        self.def_id,
                    )?;
                    if self.check_mode != CheckMode::CoreProof {
                        post_call_block_builder.add_statement(assume_statement);
                    }
                }
                post_call_block_builder.build();

                if let Some(cleanup_block) = cleanup {
                    let encoded_cleanup_block = self.encode_basic_block_label(*cleanup_block);
                    let fresh_cleanup_label = self.fresh_basic_block_label();
                    let mut cleanup_block_builder =
                        block_builder.create_basic_block_builder(fresh_cleanup_label.clone());
                    cleanup_block_builder
                        .set_successor_jump(vir_high::Successor::Goto(encoded_cleanup_block));

                    let statement = vir_high::Statement::inhale_no_pos(target_memory_block);
                    cleanup_block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                        statement,
                        span,
                        ErrorCtxt::ProcedureCall,
                        self.def_id,
                    )?);

                    self.encode_inhale_lifetime_tokens(
                        &mut cleanup_block_builder,
                        &lifetimes_to_exhale_inhale,
                        derived_from.len(),
                    )?;
                    let function_lifetime_return = self.encoder.set_statement_error_ctxt(
                        vir_high::Statement::lifetime_return_no_pos(
                            function_call_lifetime,
                            derived_from.clone(),
                            self.lifetime_token_fractional_permission(
                                self.lifetime_count * derived_from.len(),
                            ),
                        ),
                        self.mir.span,
                        ErrorCtxt::LifetimeInhale,
                        self.def_id,
                    )?;
                    cleanup_block_builder.add_statement(function_lifetime_return);
                    self.encode_lft_for_block(
                        *cleanup_block,
                        location,
                        &mut cleanup_block_builder,
                    )?;

                    cleanup_block_builder.build();
                    block_builder.set_successor_jump(vir_high::Successor::NonDetChoice(
                        fresh_destination_label,
                        fresh_cleanup_label,
                    ));
                } else {
                    unimplemented!();
                }
            } else {
                unimplemented!();
            }
        } else if let Some(_cleanup_block) = cleanup {
            // TODO: add panic postconditions.
            unimplemented!();
        } else {
            // TODO: Can we always soundly assume false here?
            unimplemented!();
        }

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn encode_terminator_assert(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        span: Span,
        cond: &mir::Operand<'tcx>,
        expected: bool,
        msg: &mir::AssertMessage<'tcx>,
        target: mir::BasicBlock,
        cleanup: Option<mir::BasicBlock>,
    ) -> SpannedEncodingResult<SuccessorBuilder> {
        let condition = self
            .encoder
            .encode_operand_high(self.mir, cond, span)
            .with_default_span(span)?;

        let guard = if expected {
            condition
        } else {
            vir_high::Expression::not(condition)
        };

        let (assert_msg, error_ctxt) = if let mir::AssertKind::BoundsCheck { .. } = msg {
            let mut s = String::new();
            msg.fmt_assert_args(&mut s).unwrap();
            (s, ErrorCtxt::BoundsCheckAssert)
        } else {
            let assert_msg = msg.description().to_string();
            (assert_msg.clone(), ErrorCtxt::AssertTerminator(assert_msg))
        };

        let target_label = self.encode_basic_block_label(target);
        block_builder.add_comment(format!("Rust assertion: {}", assert_msg));
        if self.check_panics {
            block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                vir_high::Statement::assert_no_pos(guard.clone()),
                span,
                error_ctxt,
                self.def_id,
            )?);
        }
        let successor = if let Some(cleanup) = cleanup {
            let successors = vec![
                (guard, target_label),
                (true.into(), self.encode_basic_block_label(cleanup)),
            ];
            SuccessorBuilder::jump(vir_high::Successor::GotoSwitch(successors))
        } else {
            SuccessorBuilder::jump(vir_high::Successor::Goto(target_label))
        };
        Ok(successor)
    }

    /// Also marks it as reachable.
    fn encode_basic_block_label(&mut self, bb: mir::BasicBlock) -> vir_high::BasicBlockId {
        self.reachable_blocks.insert(bb);
        vir_high::BasicBlockId::new(format!("label_{:?}", bb))
    }

    fn fresh_basic_block_label(&mut self) -> vir_high::BasicBlockId {
        let name = format!("label_{}_custom", self.fresh_id_generator);
        self.fresh_id_generator += 1;
        vir_high::BasicBlockId::new(name)
    }

    fn fresh_old_label(&mut self) -> String {
        let name = format!("label_{}_old", self.fresh_id_generator);
        self.fresh_id_generator += 1;
        name
    }

    fn fresh_ghost_variable(
        &mut self,
        name_template: &str,
        ty: vir_high::Type,
    ) -> vir_high::VariableDecl {
        let name = format!("{}${}", name_template, self.fresh_id_generator);
        self.fresh_id_generator += 1;
        vir_high::VariableDecl::new(name, ty)
    }

    fn register_error(&self, location: mir::Location, error_ctxt: ErrorCtxt) -> vir_high::Position {
        let span = self.encoder.get_mir_location_span(self.mir, location);
        self.encoder
            .error_manager()
            .register_error(span, error_ctxt, self.def_id)
            .into()
    }

    fn set_statement_error(
        &mut self,
        location: mir::Location,
        error_ctxt: ErrorCtxt,
        statement: vir_high::Statement,
    ) -> SpannedEncodingResult<vir_high::Statement> {
        let position = self.register_error(location, error_ctxt.clone());
        self.encoder
            .set_surrounding_error_context_for_statement(statement, position, error_ctxt)
    }

    fn encode_specification_blocks(&mut self) -> SpannedEncodingResult<()> {
        // Collect the entry points into the specification blocks.
        let mut entry_points: BTreeMap<_, _> = self
            .specification_blocks
            .entry_points()
            .map(|bb| (bb, Vec::new()))
            .collect();

        // Encode the specification blocks.
        for (bb, statements) in &mut entry_points {
            self.encode_specification_block(*bb, statements)?;
        }
        assert!(self.specification_block_encoding.is_empty());
        self.specification_block_encoding = entry_points;

        // Encode loop invariants.
        let mut loop_invariant_blocks = self.specification_blocks.loop_invariant_blocks().clone();
        for loop_head in &self.procedure.loop_info().loop_heads {
            let (invariant_location, specification_blocks) =
                if let Some(blocks) = loop_invariant_blocks.remove(loop_head) {
                    (blocks.location, blocks.specification_blocks)
                } else {
                    (*loop_head, Vec::new())
                };
            let statement =
                self.encode_loop_invariant(*loop_head, invariant_location, specification_blocks)?;
            self.loop_invariant_encoding
                .insert(invariant_location, statement);
        }

        self.encode_ghost_blocks()?;

        Ok(())
    }

    #[allow(clippy::nonminimal_bool)]
    fn encode_specification_block(
        &mut self,
        bb: mir::BasicBlock,
        encoded_statements: &mut Vec<vir_high::Statement>,
    ) -> SpannedEncodingResult<()> {
        let block = &self.mir[bb];
        if false
            || self.try_encode_assert(bb, block, encoded_statements)?
            || self.try_encode_assume(bb, block, encoded_statements)?
            || self.try_encode_ghost_markers(bb, block, encoded_statements)?
            || self.try_encode_specification_function_call(bb, block, encoded_statements)?
        {
            Ok(())
        } else {
            unreachable!()
        }
    }

    fn try_encode_assert(
        &mut self,
        bb: mir::BasicBlock,
        block: &mir::BasicBlockData<'tcx>,
        encoded_statements: &mut Vec<vir_high::Statement>,
    ) -> SpannedEncodingResult<bool> {
        for stmt in &block.statements {
            if let mir::StatementKind::Assign(box (
                _,
                mir::Rvalue::Aggregate(box mir::AggregateKind::Closure(cl_def_id, cl_substs), _),
            )) = stmt.kind
            {
                let assertion = match self.encoder.get_prusti_assertion(cl_def_id) {
                    Some(spec) => spec,
                    None => return Ok(false),
                };

                let span = self
                    .encoder
                    .get_definition_span(assertion.assertion.to_def_id());

                let error_ctxt = ErrorCtxt::Panic(PanicCause::Assert);

                let assert_expr = self.encoder.set_expression_error_ctxt(
                    self.encoder
                        .encode_invariant_high(self.mir, bb, self.def_id, cl_substs)?,
                    span,
                    error_ctxt.clone(),
                    self.def_id,
                );

                let assert_stmt = vir_high::Statement::assert_no_pos(assert_expr);
                let assert_stmt = self.encoder.set_statement_error_ctxt(
                    assert_stmt,
                    span,
                    error_ctxt,
                    self.def_id,
                )?;

                if self.check_mode != CheckMode::CoreProof {
                    encoded_statements.push(assert_stmt);
                }

                return Ok(true);
            }
        }
        Ok(false)
    }

    fn try_encode_assume(
        &mut self,
        bb: mir::BasicBlock,
        block: &mir::BasicBlockData<'tcx>,
        encoded_statements: &mut Vec<vir_high::Statement>,
    ) -> SpannedEncodingResult<bool> {
        for stmt in &block.statements {
            if let mir::StatementKind::Assign(box (
                _,
                mir::Rvalue::Aggregate(box mir::AggregateKind::Closure(cl_def_id, cl_substs), _),
            )) = stmt.kind
            {
                let assumption = match self.encoder.get_prusti_assumption(cl_def_id) {
                    Some(spec) => spec,
                    None => return Ok(false),
                };

                let span = self
                    .encoder
                    .get_definition_span(assumption.assumption.to_def_id());

                // I don't expect an assumption to raise an error
                let error_ctxt = ErrorCtxt::Assumption;

                let expr = self.encoder.set_expression_error_ctxt(
                    self.encoder
                        .encode_invariant_high(self.mir, bb, self.def_id, cl_substs)?,
                    span,
                    error_ctxt.clone(),
                    self.def_id,
                );

                let stmt = vir_high::Statement::assume_no_pos(expr);
                let stmt =
                    self.encoder
                        .set_statement_error_ctxt(stmt, span, error_ctxt, self.def_id)?;

                if self.check_mode != CheckMode::CoreProof {
                    encoded_statements.push(stmt);
                }

                return Ok(true);
            }
        }
        Ok(false)
    }

    fn try_encode_ghost_markers(
        &mut self,
        _bb: mir::BasicBlock,
        block: &mir::BasicBlockData<'tcx>,
        _encoded_statements: &mut [vir_high::Statement],
    ) -> SpannedEncodingResult<bool> {
        for stmt in &block.statements {
            if let mir::StatementKind::Assign(box (
                _,
                mir::Rvalue::Aggregate(box mir::AggregateKind::Closure(cl_def_id, _), _),
            )) = stmt.kind
            {
                let is_begin = self.encoder.get_ghost_begin(cl_def_id).is_some();
                let is_end = self.encoder.get_ghost_end(cl_def_id).is_some();
                return Ok(is_begin || is_end);
            }
        }
        Ok(false)
    }

    fn try_encode_specification_function_call(
        &mut self,
        bb: mir::BasicBlock,
        block: &mir::BasicBlockData<'tcx>,
        encoded_statements: &mut Vec<vir_high::Statement>,
    ) -> SpannedEncodingResult<bool> {
        let span = self.encoder.get_mir_terminator_span(block.terminator());
        match &block.terminator().kind {
            mir::TerminatorKind::Call {
                func: mir::Operand::Constant(box mir::Constant { literal, .. }),
                args,
                destination: _,
                target: _,
                cleanup: _,
                fn_span: _,
                from_hir_call: _,
            } => {
                if let ty::TyKind::FnDef(def_id, _substs) = literal.ty().kind() {
                    let full_called_function_name = self.encoder.env().tcx().def_path_str(*def_id);
                    match full_called_function_name.as_ref() {
                        "prusti_contracts::prusti_set_union_active_field" => {
                            assert_eq!(args.len(), 1);
                            let argument_place = if let mir::Operand::Move(place) = args[0] {
                                place
                            } else {
                                unreachable!()
                            };
                            // Find the place whose address was stored in the argument by
                            // iterating backwards through statements.
                            let mut statement_index = block.statements.len() - 1;
                            let union_variant_place = loop {
                                if let Some(statement) = block.statements.get(statement_index) {
                                    if let mir::StatementKind::Assign(box (
                                        target_place,
                                        mir::Rvalue::AddressOf(_, union_variant_place),
                                    )) = &statement.kind
                                    {
                                        if *target_place == argument_place {
                                            break union_variant_place;
                                        }
                                    }
                                    statement_index -= 1;
                                } else {
                                    unreachable!();
                                }
                            };
                            let encoded_variant_place =
                                self.encode_place(*union_variant_place, None)?;
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::set_union_variant_no_pos(
                                    encoded_variant_place,
                                ),
                                span,
                                ErrorCtxt::SetEnumVariant,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        _ => unreachable!(),
                    }
                } else {
                    unreachable!();
                }
            }
            _ => unreachable!("block: {:?}", bb),
        }
    }
}
