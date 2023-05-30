use self::{
    builtin_function_encoder::BuiltinFuncAppEncoder,
    initialisation::InitializationData,
    lifetimes::LifetimesEncoder,
    specification_blocks::SpecificationBlocks,
    // specification_regions::SpecificationRegionEncoding,
};
use super::MirProcedureEncoderInterface;
use crate::encoder::{
    errors::{ErrorCtxt, PanicCause, SpannedEncodingError, SpannedEncodingResult, WithSpan},
    mir::{
        casts::CastsEncoderInterface,
        constants::ConstantsEncoderInterface,
        contracts::{ContractsEncoderInterface, ProcedureContractMirDef},
        errors::ErrorInterface,
        generics::MirGenericsEncoderInterface,
        panics::MirPanicsEncoderInterface,
        places::PlacesEncoderInterface,
        predicates::MirPredicateEncoderInterface,
        procedures::encoder::specification_blocks::specification_blocks_to_graph,
        pure::{PureFunctionEncoderInterface, SpecificationEncoderInterface},
        spans::SpanInterface,
        specifications::SpecificationsInterface,
        type_layouts::MirTypeLayoutsEncoderInterface,
        types::MirTypeEncoderInterface,
    },
    mir_encoder::PRECONDITION_LABEL,
    Encoder,
};
use log::{debug, trace};
use prusti_common::config;
use prusti_interface::{
    environment::{
        debug_utils::to_text::ToText,
        is_checked_block_begin_marker, is_checked_block_end_marker, is_specification_begin_marker,
        is_specification_end_marker, is_try_finally_begin_marker, is_try_finally_end_marker,
        mir_analyses::{
            allocation::{compute_definitely_allocated, DefinitelyAllocatedAnalysisResult},
            initialization::{compute_definitely_initialized, DefinitelyInitializedAnalysisResult},
        },
        mir_body::borrowck::{facts::RichLocation, lifetimes::Lifetimes},
        Procedure,
    },
    specs::typed::{Pledge, SpecificationItem},
};
use prusti_rustc_interface::{
    data_structures::graph::WithStartNode,
    hir::def_id::DefId,
    middle::{mir, ty, ty::subst::SubstsRef},
    span::Span,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    common::{
        check_mode::CheckMode,
        expression::{BinaryOperationHelpers, ExpressionIterator, UnaryOperationHelpers},
        position::Positioned,
    },
    high::{
        self as vir_high,
        builders::procedure::{
            BasicBlockBuilder, ProcedureBuilder, StatementSequenceBuilder, SuccessorBuilder,
            SuccessorExitKind,
        },
        operations::{lifetimes::WithLifetimes, ty::Typed},
    },
};

mod builtin_function_encoder;
mod check_mode_converters;
mod elaborate_drops;
mod ghost;
mod initialisation;
mod lifetimes;
mod loops;
mod scc;
pub mod specification_blocks;
mod termination;
mod specifications;
mod utils;
mod specification_regions;
mod user_named_lifetimes;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum ProcedureEncodingKind {
    Regular,
    PostconditionFrameCheck,
}

pub(super) fn encode_procedure<'v, 'tcx: 'v>(
    encoder: &mut Encoder<'v, 'tcx>,
    def_id: DefId,
    check_mode: CheckMode,
    encoding_kind: ProcedureEncodingKind,
) -> SpannedEncodingResult<vir_high::ProcedureDecl> {
    let procedure = Procedure::new(encoder.env(), def_id);
    let tcx = encoder.env().tcx();
    let (mir, lifetimes) =
        self::elaborate_drops::get_and_elaborate_mir(encoder, def_id, &procedure)?;
    let mir = &mir; // Mark body as immutable.
    let is_unsafe_function = encoder.env().query.is_unsafe_function(def_id);
    let no_panic: bool = encoder.no_panic(def_id, None);
    let no_panic_ensures_postcondition = encoder.no_panic_ensures_postcondition(def_id, None);
    let (env, un_derefer) =
        self::initialisation::create_move_data_param_env_and_un_derefer(tcx, mir);
    // TODO: the clone is required so that we can remove dead unwinds
    let mut no_dead_unwinds = mir.clone();
    let init_data = InitializationData::new(tcx, &mut no_dead_unwinds, &env, &un_derefer);
    let locals_without_explicit_allocation: BTreeSet<_> = mir.vars_and_temps_iter().collect();
    let specification_blocks =
        SpecificationBlocks::build(encoder.env().query, mir, Some(&procedure), true);
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
    let is_drop_impl = {
        let is_drop_impl = encoder.env().query.is_drop_method_impl(def_id);
        let function_name = encoder.env().name.get_absolute_item_name(def_id);
        // FIXME: Remove this hack based assert after convinced that the query
        // works reliably.
        assert_eq!(
            function_name.ends_with(" as std::ops::Drop>::drop"),
            is_drop_impl
        );
        is_drop_impl
    };
    let mut procedure_encoder = ProcedureEncoder {
        encoder,
        def_id,
        check_mode,
        is_unsafe_function,
        procedure: &procedure,
        mir,
        init_data,
        initialization,
        allocation,
        lifetimes,
        reachable_blocks: Default::default(),
        specification_blocks,
        specification_block_encoding: Default::default(),
        specification_region_encoding_statements: Default::default(),
        specification_region_exit_target_block: Default::default(),
        specification_on_drop_unwind: Default::default(),
        add_specification_before_terminator: Default::default(),
        add_function_panic_specification_before_terminator: Default::default(),
        locals_used_only_in_specification_regions: Default::default(),
        loop_invariant_encoding: Default::default(),
        check_panics: config::check_panics() && check_mode.check_specifications(),
        locals_without_explicit_allocation,
        locals_live_in_block: Default::default(),
        missing_live_locals: Default::default(),
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
        termination_variable: None,
        encoding_kind,
        opened_reference_place_permissions: Default::default(),
        opened_reference_witnesses: Default::default(),
        user_named_lifetimes: Default::default(),
        manually_managed_places: Default::default(),
        stashed_ranges: Default::default(),
        specification_expressions: Default::default(),
        is_drop_impl,
        opened_reference_parameter_lifetimes: Default::default(),
        pointer_deref_lifetime: None,
        no_panic,
        no_panic_ensures_postcondition,
    };
    procedure_encoder.encode()
}

struct ProcedureEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p mut Encoder<'v, 'tcx>,
    def_id: DefId,
    check_mode: CheckMode,
    encoding_kind: ProcedureEncodingKind,
    is_unsafe_function: bool,
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
    /// Specification regions to be removed from the given point.
    /// FIXME: We currently assume no branching in the specification region.
    specification_region_encoding_statements: BTreeMap<mir::BasicBlock, Vec<vir_high::Statement>>,
    /// The block immediatelly after the specification region to which the
    /// execution should be resumed after the specification region is removed.
    specification_region_exit_target_block: BTreeMap<mir::BasicBlock, mir::BasicBlock>,
    /// The specification region that should executed when the specified
    /// expression is dropped.
    specification_on_drop_unwind: FxHashMap<vir_high::Expression, mir::BasicBlock>,
    /// The specification statements to be added before the terminator of the
    /// specified block.
    add_specification_before_terminator: BTreeMap<mir::BasicBlock, Vec<vir_high::Statement>>,
    /// The specification statements to be added before the terminator of the
    /// panic edge of the function call.
    add_function_panic_specification_before_terminator:
        BTreeMap<(mir::BasicBlock, mir::BasicBlock), Vec<vir_high::Statement>>,
    /// The locals that are used only in the specification regions and,
    /// therefore, `StorageLive`/`StorageDead` are not generated for them.
    locals_used_only_in_specification_regions: BTreeSet<mir::Local>,
    /// The loop invariant to be inserted at the end of the given basic block.
    loop_invariant_encoding: BTreeMap<mir::BasicBlock, vir_high::Statement>,
    check_panics: bool,
    /// Locals that are not explicitly allocated or deallocated with
    /// `StorageLive`/`StorageDead`. Such locals are assumed to be alive through
    /// the entire body of the function.
    locals_without_explicit_allocation: BTreeSet<mir::Local>,
    /// The Rust compiler does not guarantee that each `StorageDead` is
    /// dominated by a `StorageLive`:
    ///
    /// * https://github.com/rust-lang/rust/issues/99160
    /// * https://github.com/rust-lang/rust/issues/98896
    ///
    /// Therefore, we track which locals are alive in each block and emit a fake
    /// `StorageLive` in blocks that are merged with blocks in which the local
    /// is alive.
    locals_live_in_block: BTreeMap<mir::BasicBlock, BTreeSet<mir::Local>>,
    /// `StorageDead` statements which apply to locals that are not guaranteed
    /// to be alive.
    missing_live_locals: Vec<(mir::BasicBlock, mir::Local)>,
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
    termination_variable: Option<vir_high::VariableDecl>,
    /// A map from opened reference place to the corresponding permission
    /// variable.
    opened_reference_place_permissions:
        BTreeMap<vir_high::Expression, Option<vir_high::VariableDecl>>,
    /// A map from opened reference witnesses to the corresponding places and lifetimes.
    opened_reference_witnesses:
        BTreeMap<String, (vir_high::Expression, vir_high::ty::LifetimeConst)>,
    /// The lifetimes extracted by the user by using `take_lifetime!` macro.
    user_named_lifetimes: BTreeMap<String, vir_high::ty::LifetimeConst>,
    /// Places that are manually managed by the user and for which we should not
    /// automatically generate open/close/fold/unfold statements.
    /// FIXME: Not used, remove.
    manually_managed_places: BTreeSet<vir_high::Expression>,
    /// Information about stashed ranges with a given name: `(pointer,
    /// start_index, end_index)`.
    stashed_ranges: BTreeMap<
        String,
        (
            vir_high::Expression,
            vir_high::Expression,
            vir_high::Expression,
        ),
    >,
    /// The encoded Prusti specification expressions used in specification
    /// blocks.
    ///
    /// Specification ID → expresssion.
    specification_expressions: BTreeMap<String, vir_high::Expression>,
    is_drop_impl: bool,
    /// The lifetime of the `self` argument in a `Drop` implementation.
    opened_reference_parameter_lifetimes: Vec<vir_high::ty::LifetimeConst>,
    /// A lifetime to use when reborrowing a place behind a raw pointer dereference.
    pointer_deref_lifetime: Option<ty::Region<'tcx>>,
    /// This function is guaranteed not to panic even when its precondition is
    /// violated.
    no_panic: bool,
    /// If this function did not panic, then its postcondition is guaranteed to
    /// hold.
    no_panic_ensures_postcondition: bool,
}

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    fn encode(&mut self) -> SpannedEncodingResult<vir_high::ProcedureDecl> {
        self.pure_sanity_checks()?;
        let name = format!(
            "{}${}${:?}",
            self.encoder.encode_item_name(self.def_id),
            self.check_mode,
            self.encoding_kind,
        );
        let broken_invariants = self.encode_broken_invariants()?;
        let (allocate_parameters, deallocate_parameters) =
            self.encode_parameters(broken_invariants)?;
        let (allocate_returns, deallocate_returns) = self.encode_returns()?;
        self.lifetime_token_permission =
            Some(self.fresh_ghost_variable("lifetime_token_perm_amount", vir_high::Type::MPerm));
        let (assume_preconditions, assert_postconditions) =
            self.encode_functional_specifications()?;
        let dead_references = self.encode_dead_references_for_parameters()?;
        // match self.check_mode {
        //     CheckMode::CoreProof => {
        //         // Unsafe functions will come with CheckMode::Both because they
        //         // are allowed to have preconditions.
        //         (Vec::new(), Vec::new())
        //     }
        //     CheckMode::Both | CheckMode::Specifications => {
        //         self.encode_functional_specifications()?
        //     }
        // };
        let (assume_lifetime_preconditions, assert_lifetime_postconditions) =
            self.encode_lifetime_specifications()?;
        let termination_initialization = self.encode_termination_initialization()?;
        let mut pre_statements = assume_lifetime_preconditions;
        pre_statements.extend(allocate_parameters);
        pre_statements.extend(assume_preconditions);
        let old_label = self.encoder.set_statement_error_ctxt(
            vir_high::Statement::old_label_no_pos(PRECONDITION_LABEL.to_string()),
            self.mir.span,
            ErrorCtxt::UnexpectedAssumeMethodPrecondition,
            self.def_id,
        )?;
        pre_statements.push(old_label);
        pre_statements.extend(termination_initialization);
        pre_statements.extend(allocate_returns);
        let mut post_success_statements = dead_references;
        post_success_statements.extend(assert_postconditions);
        post_success_statements.extend(deallocate_parameters);
        post_success_statements.extend(deallocate_returns);
        let post_statements = assert_lifetime_postconditions;
        let mut resume_panic_statements = vec![vir_high::Statement::leak_all()];
        if self.no_panic {
            resume_panic_statements.push(self.encoder.set_statement_error_ctxt(
                vir_high::Statement::assert_no_pos(false.into()),
                self.mir.span,
                ErrorCtxt::NoPanicPanics,
                self.def_id,
            )?);
        }
        let procedure_position =
            self.encoder
                .register_error(self.mir.span, ErrorCtxt::Unexpected, self.def_id);
        let mut procedure_builder = ProcedureBuilder::new(
            name,
            self.check_mode,
            procedure_position,
            pre_statements,
            post_success_statements,
            post_statements,
            resume_panic_statements,
        );
        for local_index in 0..self.mir.local_decls.len() {
            // We do not use `encode_local` to avoid marking the variable as
            // used.
            let variable = self
                .encoder
                .encode_local_high(self.mir, local_index.into())?;
            procedure_builder.add_non_aliased_place(variable.into());
        }
        match self.encoding_kind {
            ProcedureEncodingKind::Regular => self.encode_body(&mut procedure_builder)?,
            ProcedureEncodingKind::PostconditionFrameCheck => {
                assert!(
                    !self.is_drop_impl,
                    "Drop impl does not have a postcondition and, therefore, should not be checked"
                );
                self.encode_postcondition_frame_check(&mut procedure_builder)?;
            }
        }
        self.encode_implicit_allocations(&mut procedure_builder)?;
        let mut procedure = procedure_builder.build();
        self.add_missing_live_locals(&mut procedure)?;
        Ok(procedure)
    }

    fn add_missing_live_locals(
        &mut self,
        procedure: &mut vir_high::ProcedureDecl,
    ) -> SpannedEncodingResult<()> {
        if !config::create_missing_storage_live() {
            return Ok(());
        }
        let predecessors = self.mir.basic_blocks.predecessors();
        for (block, missing_local) in std::mem::take(&mut self.missing_live_locals) {
            for predecessor in &predecessors[block] {
                if let Some(locals_live_in_block) = self.locals_live_in_block.get(predecessor) {
                    if !locals_live_in_block.contains(&missing_local) {
                        let statements = self.encode_statement_storage_live(
                            missing_local,
                            mir::Location {
                                block: *predecessor,
                                statement_index: 0,
                            },
                        )?;
                        let label = self.encode_basic_block_label(*predecessor);
                        procedure
                            .basic_blocks
                            .get_mut(&label)
                            .unwrap()
                            .statements
                            .splice(0..0, statements);
                    }
                }
            }
        }
        Ok(())
    }

    fn pure_sanity_checks(&self) -> SpannedEncodingResult<()> {
        if self.encoder.is_pure(self.def_id, None) && !self.encoder.terminates(self.def_id, None) {
            let mut err = SpannedEncodingError::incorrect(
                "Pure functions need to terminate",
                self.encoder.get_mir_body_span(self.mir),
            );
            err.set_help("Consider adding the `#[terminates]` attribute.");
            Err(err)
        } else {
            Ok(())
        }
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
        broken_invariants: Vec<bool>,
    ) -> SpannedEncodingResult<(Vec<vir_high::Statement>, Vec<vir_high::Statement>)> {
        let mut allocation = vec![vir_high::Statement::comment(
            "Allocate the parameters.".to_string(),
        )];
        let mut deallocation = vec![vir_high::Statement::comment(
            "Deallocate the parameters.".to_string(),
        )];
        if self.is_drop_impl {
            self.encode_drop_impl_parameters(&mut allocation, &mut deallocation)?;
            return Ok((allocation, deallocation));
        }
        assert_eq!(broken_invariants.len(), self.mir.args_iter().count());
        for (mir_arg, is_invariant_broken) in
            self.mir.args_iter().zip(broken_invariants.into_iter())
        {
            let parameter = self.encode_local(mir_arg)?;
            if is_invariant_broken {
                self.encode_broken_invariant_parameter(
                    parameter,
                    &mut allocation,
                    &mut deallocation,
                )?;
            } else {
                self.encode_normal_parameter(
                    mir_arg,
                    parameter,
                    &mut allocation,
                    &mut deallocation,
                )?;
            }
        }
        Ok((allocation, deallocation))
    }

    fn encode_normal_parameter(
        &mut self,
        mir_arg: mir::Local,
        parameter: vir_high::Local,
        allocation: &mut Vec<vir_high::Statement>,
        deallocation: &mut Vec<vir_high::Statement>,
    ) -> SpannedEncodingResult<()> {
        let alloc_statement = vir_high::Statement::inhale_predicate_no_pos(
            vir_high::Predicate::owned_non_aliased_no_pos(parameter.clone().into()),
        );
        allocation.push(self.encoder.set_surrounding_error_context_for_statement(
            alloc_statement,
            parameter.position,
            ErrorCtxt::UnexpectedStorageLive,
        )?);
        let mir_type = self.encoder.get_local_type(self.mir, mir_arg)?;
        let size = self.encoder.encode_type_size_expression(mir_type)?;
        let dealloc_statement = vir_high::Statement::exhale_predicate_no_pos(
            vir_high::Predicate::memory_block_stack_no_pos(parameter.clone().into(), size),
        );
        deallocation.push(self.encoder.set_surrounding_error_context_for_statement(
            dealloc_statement,
            parameter.position,
            ErrorCtxt::UnexpectedStorageDead,
        )?);
        Ok(())
    }

    fn encode_broken_invariant_parameter(
        &mut self,
        parameter: vir_high::Local,
        allocation: &mut Vec<vir_high::Statement>,
        deallocation: &mut Vec<vir_high::Statement>,
    ) -> SpannedEncodingResult<()> {
        assert!(self.is_unsafe_function, "TODO: a proper error message that broken invarianats are allowed only on unsafe functions.");
        let vir_high::Type::Reference(reference) = parameter.get_type() else {
            unimplemented!("TODO: A proper error message that broken invariants are allowed only on references.");
        };
        self.opened_reference_parameter_lifetimes
            .push(reference.lifetime.clone());
        let address_memory_block =
            self.encode_reference_address_memory_block(parameter.clone().into())?;
        let alloc_statement =
            vir_high::Statement::inhale_predicate_no_pos(address_memory_block.clone());
        allocation.push(self.encoder.set_surrounding_error_context_for_statement(
            alloc_statement,
            parameter.position,
            ErrorCtxt::UnexpectedStorageLive,
        )?);
        let dealloc_statement = vir_high::Statement::exhale_predicate_no_pos(address_memory_block);
        deallocation.push(self.encoder.set_surrounding_error_context_for_statement(
            dealloc_statement,
            parameter.position,
            ErrorCtxt::UnexpectedStorageDead,
        )?);
        let deref_place = vir_high::Expression::deref_no_pos(
            parameter.clone().into(),
            (*reference.target_type).clone(),
        );
        let type_decl = self
            .encoder
            .encode_type_def_high(deref_place.get_type(), true)?;
        match type_decl {
            vir_high::TypeDecl::Struct(struct_decl) => {
                for field in struct_decl.fields {
                    let field_place = vir_high::Expression::field(deref_place.clone(), field, parameter.position);
                    let predicate = vir_high::Predicate::owned_non_aliased_no_pos(field_place);
                    allocation.push(self.encoder.set_surrounding_error_context_for_statement(
                        vir_high::Statement::inhale_predicate_no_pos(predicate.clone()),
                        parameter.position,
                        ErrorCtxt::UnexpectedStorageDead,
                    )?);
                    deallocation.push(self.encoder.set_surrounding_error_context_for_statement(
                        vir_high::Statement::exhale_predicate_no_pos(predicate),
                        parameter.position,
                        ErrorCtxt::UnexpectedStorageDead,
                    )?);
                }
            }
            _ => unimplemented!("TODO: A proper error message that broken invariants are allowed only on structs. Got: {}", type_decl),
        }
        Ok(())
    }

    fn encode_reference_address_memory_block(
        &mut self,
        place: vir_high::Expression,
    ) -> SpannedEncodingResult<vir_high::Predicate> {
        let position = place.position();
        let vir_high::Type::Reference(reference) = place.get_type() else {
            unreachable!();
        };
        let pointer_type = vir_high::Type::pointer((*reference.target_type).clone());
        let address_field = vir_high::FieldDecl::reference_address(reference.clone());
        let address_place = vir_high::Expression::field(place, address_field, position);
        let size = self
            .encoder
            .encode_type_size_expression_high(pointer_type)?;
        Ok(vir_high::Predicate::memory_block_stack_no_pos(
            address_place,
            size,
        ))
    }

    fn encode_drop_impl_parameters(
        &mut self,
        allocation: &mut Vec<vir_high::Statement>,
        deallocation: &mut Vec<vir_high::Statement>,
    ) -> SpannedEncodingResult<()> {
        let self_mir_arg = {
            let mut args_iter = self.mir.args_iter();
            let self_arg = args_iter.next().unwrap();
            assert!(args_iter.next().is_none());
            self_arg
        };
        let self_parameter = self.encode_local(self_mir_arg).unwrap();
        let vir_high::Type::Reference(self_reference) = self_parameter.get_type() else {
            unreachable!();
        };
        self.opened_reference_parameter_lifetimes
            .push(self_reference.lifetime.clone());
        // let address_place = vir_high::Expression::field(
        //     self_parameter.clone().into(),
        //     vir_high::FieldDecl::reference_address(self_reference.clone()),
        //     // vir_high::FieldDecl::new(
        //     //     ADDRESS_FIELD_NAME,
        //     //     0usize,
        //     //     vir_high::Type::Int(vir_high::ty::Int::Usize),
        //     // ),
        //     self_parameter.position,
        // );
        // let pointer_type = vir_high::Type::pointer((*self_reference.target_type).clone());
        // let size = self
        //     .encoder
        //     .encode_type_size_expression_high(pointer_type)?;
        let address_memory_block =
            self.encode_reference_address_memory_block(self_parameter.clone().into())?;
        let alloc_statement = vir_high::Statement::inhale_predicate_no_pos(
            address_memory_block.clone(), // vir_high::Predicate::memory_block_stack_no_pos(address_place.clone(), size.clone()),
        );
        allocation.push(self.encoder.set_surrounding_error_context_for_statement(
            alloc_statement,
            self_parameter.position,
            ErrorCtxt::UnexpectedStorageLive,
        )?);
        let deref_place = vir_high::Expression::deref_no_pos(
            self_parameter.clone().into(),
            (*self_reference.target_type).clone(),
        );
        let alloc_statement = vir_high::Statement::inhale_predicate_no_pos(
            vir_high::Predicate::owned_non_aliased_no_pos(deref_place.clone()),
        );
        allocation.push(self.encoder.set_surrounding_error_context_for_statement(
            alloc_statement,
            self_parameter.position,
            ErrorCtxt::UnexpectedStorageLive,
        )?);
        let dealloc_statement = vir_high::Statement::exhale_predicate_no_pos(
            address_memory_block, // vir_high::Predicate::memory_block_stack_no_pos(address_place.clone(), size),
        );
        deallocation.push(self.encoder.set_surrounding_error_context_for_statement(
            dealloc_statement,
            self_parameter.position,
            ErrorCtxt::UnexpectedStorageDead,
        )?);
        self.add_drop_impl_deallocation_statements(
            deallocation,
            self_parameter.position,
            deref_place,
        )?;
        Ok(())
    }

    fn add_drop_impl_deallocation_statements(
        &mut self,
        deallocation: &mut Vec<vir_high::Statement>,
        position: vir_high::Position,
        place: vir_high::Expression,
    ) -> SpannedEncodingResult<()> {
        let type_decl = self.encoder.encode_type_def_high(place.get_type(), true)?;
        match type_decl {
            vir_high::TypeDecl::Bool
            | vir_high::TypeDecl::Int(_)
            | vir_high::TypeDecl::Float(_)
            | vir_high::TypeDecl::TypeVar(_)
            | vir_high::TypeDecl::Pointer(_) => {
                unreachable!("Drop on a primitive type.");
            }
            vir_high::TypeDecl::Tuple(_) => todo!(),
            vir_high::TypeDecl::Struct(struct_decl) => {
                for field in struct_decl.fields {
                    let field_place = vir_high::Expression::field(place.clone(), field, position);
                    let dealloc_statement = vir_high::Statement::exhale_predicate_no_pos(
                        vir_high::Predicate::owned_non_aliased_no_pos(field_place),
                    );
                    deallocation.push(self.encoder.set_surrounding_error_context_for_statement(
                        dealloc_statement,
                        position,
                        ErrorCtxt::UnexpectedStorageDead,
                    )?);
                }
            }
            vir_high::TypeDecl::Sequence(_) => todo!(),
            vir_high::TypeDecl::Map(_) => todo!(),
            vir_high::TypeDecl::Enum(_) => todo!(),
            vir_high::TypeDecl::Union(_) => todo!(),
            vir_high::TypeDecl::Array(_) => todo!(),
            vir_high::TypeDecl::Slice(_) => todo!(),
            vir_high::TypeDecl::Reference(_) => todo!(),
            vir_high::TypeDecl::Never => todo!(),
            vir_high::TypeDecl::Closure(_) => todo!(),
            vir_high::TypeDecl::Unsupported(_) => todo!(),
            vir_high::TypeDecl::Trusted(_) => {
                unimplemented!("A proper error message that drops can be implemented only on non-trusted types");
            }
        }
        Ok(())
    }

    fn encode_returns(
        &mut self,
    ) -> SpannedEncodingResult<(Vec<vir_high::Statement>, Vec<vir_high::Statement>)> {
        let return_local = self.encode_local(mir::RETURN_PLACE)?;
        let mir_type = self.encoder.get_local_type(self.mir, mir::RETURN_PLACE)?;
        let size = self.encoder.encode_type_size_expression(mir_type)?;
        let alloc_statement = self.encoder.set_surrounding_error_context_for_statement(
            vir_high::Statement::inhale_predicate_no_pos(
                vir_high::Predicate::memory_block_stack_no_pos(return_local.clone().into(), size),
            ),
            return_local.position,
            ErrorCtxt::UnexpectedStorageLive,
        )?;
        let dealloc_statement = self.encoder.set_surrounding_error_context_for_statement(
            vir_high::Statement::exhale_predicate_no_pos(
                vir_high::Predicate::owned_non_aliased_no_pos(return_local.clone().into()),
            ),
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

    fn check_refinement<T: std::fmt::Debug>(
        &self,
        specification: &SpecificationItem<T>,
    ) -> SpannedEncodingResult<()> {
        if let SpecificationItem::Refined(_, _) = specification {
            if self.encoder.env().query.is_drop_method_impl(self.def_id) {
                // Contract refinement is allowed only of Drop::drop of private
                // structs.
                let self_arg = self.mir.args_iter().next().unwrap();
                let self_type = self.encoder.get_local_type(self.mir, self_arg)?;
                match self_type.kind() {
                    ty::TyKind::Ref(_, target_type, _) => match target_type.kind() {
                        ty::TyKind::Adt(adt_def, _) => {
                            let vis = self.encoder.env().tcx().visibility(adt_def.did());
                            let module = self
                                .encoder
                                .env()
                                .tcx()
                                .parent_module_from_def_id(adt_def.did().as_local().unwrap())
                                .to_def_id();
                            match vis {
                                ty::Visibility::Restricted(struct_visibility_module)
                                    if struct_visibility_module == module =>
                                {
                                    // The struct is private.
                                }
                                _ => {
                                    unimplemented!(
                                        "TODO: A proper error message that the struct {:?} must be private",
                                        adt_def.did(),
                                    );
                                }
                            }
                        }
                        _ => unimplemented!(),
                    },
                    _ => unimplemented!(),
                }
            } else {
                unimplemented!("contract refinement not supported: {specification:?}");
            }
        }
        Ok(())
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
                assertion,
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
        let broken_invariants =
            self.encode_contract_broken_invariants(procedure_contract, call_substs)?;
        let broken_invariant_mask =
            self.encode_broken_invariant_argument_mask(procedure_contract, call_substs)?;
        assert_eq!(arguments.len(), broken_invariant_mask.len());
        let mut postconditions = Vec::new();
        let arguments_in_old: Vec<_> = arguments
            .into_iter()
            .zip(broken_invariant_mask.into_iter())
            .map(|(argument, is_broken_invariant)| {
                if is_broken_invariant {
                    argument
                } else {
                    let position = argument.position();
                    vir_high::Expression::labelled_old(
                        precondition_label.to_string(),
                        argument,
                        position,
                    )
                }
            })
            .collect();
        for (assertion, assertion_substs) in
            procedure_contract.functional_postcondition(self.encoder.env(), call_substs)
        {
            let expression = self.encoder.encode_assertion_high(
                assertion,
                Some(precondition_label),
                &arguments_in_old,
                Some(result),
                self.def_id,
                assertion_substs,
            )?;
            let expression = self.desugar_pledges_in_postcondition(
                precondition_label,
                result,
                expression,
                &broken_invariants,
            )?;
            postconditions.push(expression);
        }
        let pledges = procedure_contract.pledges();
        for Pledge {
            reference,
            lhs: body_lhs,
            rhs: body_rhs,
        } in pledges
        {
            trace!(
                "pledge reference={:?} lhs={:?} rhs={:?}",
                reference,
                body_lhs,
                body_rhs
            );
            assert!(
                reference.is_none(),
                "The reference should be none in postcondition."
            );
            assert!(body_lhs.is_none(), "assert on expiry is not supported yet.");
            let assertion_rhs = self.encoder.encode_assertion_high(
                *body_rhs,
                Some(precondition_label),
                &arguments_in_old,
                Some(result),
                self.def_id,
                call_substs,
            )?;
            let position = assertion_rhs.position();
            let expression = vir_high::Expression::builtin_func_app(
                vir_high::BuiltinFunc::AfterExpiry,
                Vec::new(),
                vec![assertion_rhs],
                vir_high::Type::Bool,
                position,
            );
            let expression = self.desugar_pledges_in_postcondition(
                precondition_label,
                result,
                expression,
                &broken_invariants,
            )?;
            postconditions.push(expression);
        }
        Ok(postconditions)
    }

    fn encode_functional_specifications(
        &mut self,
    ) -> SpannedEncodingResult<(Vec<vir_high::Statement>, Vec<vir_high::Statement>)> {
        let mir_span = self.mir.span;
        let substs = self.encoder.env().query.identity_substs(self.def_id);
        // Retrieve the contract
        let procedure_contract = self
            .encoder
            .get_mir_procedure_contract_for_def(self.def_id, substs)
            .with_span(mir_span)?;
        let mut preconditions = vec![vir_high::Statement::comment(
            "Assume functional preconditions.".to_string(),
        )];
        let mut precondition_conjuncts = Vec::new();
        let mut arguments: Vec<vir_high::Expression> = Vec::new();
        let mut framing_variables = Vec::new();
        for local in self.mir.args_iter() {
            let parameter = self.encode_local(local)?;
            framing_variables.push(parameter.variable.clone());
            arguments.push(parameter.into());
        }
        self.check_refinement(&procedure_contract.specification.pres)?;
        for expression in
            self.encode_precondition_expressions(&procedure_contract, substs, &arguments)?
        {
            if let Some(expression) = self.convert_expression_to_check_mode(
                expression,
                !self.is_unsafe_function,
                false,
                &framing_variables,
            )? {
                let expression_with_pos = self.encoder.set_expression_error_ctxt(
                    expression,
                    mir_span,
                    ErrorCtxt::UnexpectedAssumeMethodPrecondition,
                    self.def_id,
                );
                // let inhale_statement = self.encoder.set_statement_error_ctxt(
                //     vir_high::Statement::inhale_expression_no_pos(expression),
                //     mir_span,
                //     ErrorCtxt::UnexpectedAssumeMethodPrecondition,
                //     self.def_id,
                // )?;
                precondition_conjuncts.push(expression_with_pos);
            }
        }
        let inhale_statement = self.encoder.set_statement_error_ctxt(
            vir_high::Statement::inhale_expression_no_pos(
                precondition_conjuncts.into_iter().conjoin(),
                Some(PRECONDITION_LABEL.to_string()),
            ),
            mir_span,
            ErrorCtxt::UnexpectedAssumeMethodPrecondition,
            self.def_id,
        )?;
        preconditions.push(inhale_statement);

        let mut postconditions = vec![vir_high::Statement::comment(
            "Assert functional postconditions.".to_string(),
        )];
        let mut postcondition_conjuncts = Vec::new();
        let result_variable = self.encode_local(mir::RETURN_PLACE)?;
        framing_variables.push(result_variable.variable.clone());
        let result: vir_high::Expression = result_variable.into();
        let mut all_pure = true;
        self.check_refinement(&procedure_contract.specification.posts)?;
        let postcondition_context =
            if self.no_panic_ensures_postcondition && self.check_mode == CheckMode::MemorySafety {
                ErrorCtxt::AssertMethodPostconditionNoPanic
            } else {
                ErrorCtxt::AssertMethodPostcondition
            };
        for expression in self.encode_postcondition_expressions(
            &procedure_contract,
            substs,
            arguments,
            &result,
            PRECONDITION_LABEL,
        )? {
            if let Some(expression) = self.convert_expression_to_check_mode(
                expression,
                !self.is_unsafe_function,
                self.no_panic_ensures_postcondition,
                &framing_variables,
            )? {
                // We use different encoding based on purity because:
                // * Silicon reports a failing exhale statement. Therefore,
                //   having multiple statements allows having more precise error
                //   messages.
                // * However, if we have permissions in the postcondition, we
                //   have to exhale it as a single statement to ensure that the
                //   permission frames what is following it.
                all_pure = all_pure && expression.is_pure();
                if all_pure {
                    let exhale_statement = self.encoder.set_statement_error_ctxt(
                        vir_high::Statement::exhale_expression_no_pos(expression, None),
                        mir_span,
                        postcondition_context.clone(),
                        self.def_id,
                    )?;
                    postconditions.push(exhale_statement);
                } else {
                    // let expression_with_pos = self.encoder.set_expression_error_ctxt(
                    //     expression,
                    //     mir_span,
                    //     ErrorCtxt::AssertMethodPostcondition,
                    //     self.def_id,
                    // );
                    // postcondition_conjuncts.push(expression_with_pos);
                    postcondition_conjuncts.push(expression);
                }
            }
        }
        let exhale_statement = self.encoder.set_statement_error_ctxt(
            vir_high::Statement::exhale_expression_no_pos(
                postcondition_conjuncts.into_iter().conjoin(),
                None,
            ),
            mir_span,
            postcondition_context,
            self.def_id,
        )?;
        postconditions.push(exhale_statement);
        Ok((preconditions, postconditions))
    }

    /// Returns a list of reference-typed parameters for which the invariant is
    /// potentially broken.
    fn encode_broken_invariants(&mut self) -> SpannedEncodingResult<Vec<bool>> {
        let mir_span = self.mir.span;
        let substs = self.encoder.env().query.identity_substs(self.def_id);
        // Retrieve the contract
        let procedure_contract = self
            .encoder
            .get_mir_procedure_contract_for_def(self.def_id, substs)
            .with_span(mir_span)?;
        // let mut arguments: Vec<vir_high::Expression> = Vec::new();
        // for local in self.mir.args_iter() {
        //     let parameter = self.encode_local(local)?;
        //     arguments.push(parameter.into());
        // }
        // let mut preconditions = Vec::new();
        // for (assertion, assertion_substs) in
        //     procedure_contract.broken_precondition_invariants(self.encoder.env(), substs)
        // {
        //     let expression = self.encoder.encode_assertion_high(
        //         assertion,
        //         None,
        //         &arguments,
        //         None,
        //         self.def_id,
        //         assertion_substs,
        //     )?;
        //     match expression {
        //         vir_high::Expression::FuncApp(mut app) => {
        //             assert_eq!(
        //                 app.function_name,
        //                 "m_prusti_contracts$$prusti_broken_invariant"
        //             );
        //             assert_eq!(app.arguments.len(), 1);
        //             match app.arguments.pop() {
        //                 Some(vir_high::Expression::Local(local)) => {
        //                     preconditions.push(local.variable);
        //                 }
        //                 _ => unreachable!(),
        //             }
        //         }
        //         _ => {
        //             unreachable!();
        //         }
        //     }
        // }
        // Ok(preconditions)
        self.encode_broken_invariant_argument_mask(&procedure_contract, substs)
    }

    /// Returns a list of reference-typed parameters for which the invariant is
    /// potentially broken.
    fn encode_broken_invariant_argument_mask(
        &mut self,
        procedure_contract: &ProcedureContractMirDef<'tcx>,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<Vec<bool>> {
        let mut is_invariant_broken = vec![false; procedure_contract.args.len()];
        let broken_invariants =
            self.encode_contract_broken_invariants(procedure_contract, substs)?;
        let mut arguments: Vec<vir_high::Expression> = Vec::new();
        for local in &procedure_contract.args {
            let parameter = self.encode_local(*local)?;
            arguments.push(parameter.into());
        }
        let mut found_count = 0;
        for (i, arg) in arguments.iter().enumerate() {
            if broken_invariants.contains(arg) {
                is_invariant_broken[i] = true;
                found_count += 1;
            }
        }
        assert_eq!(found_count, broken_invariants.len());
        // let mut arguments: Vec<vir_high::Expression> = Vec::new();
        // for local in &procedure_contract.args {
        //     let parameter = self.encode_local(*local)?;
        //     arguments.push(parameter.into());
        // }
        // let mut is_invariant_broken = vec![false; procedure_contract.args.len()];
        // for (assertion, assertion_substs) in
        //     procedure_contract.broken_precondition_invariants(self.encoder.env(), substs)
        // {
        //     let expression = self.encoder.encode_assertion_high(
        //         assertion,
        //         None,
        //         &arguments,
        //         None,
        //         self.def_id,
        //         assertion_substs,
        //     )?;
        //     match expression {
        //         vir_high::Expression::FuncApp(mut app) => {
        //             assert_eq!(
        //                 app.function_name,
        //                 "m_prusti_contracts$$prusti_broken_invariant"
        //             );
        //             assert_eq!(app.arguments.len(), 1);
        //             match app.arguments.pop() {
        //                 Some(local) => {
        //                     let mut found = false;
        //                     for (i, arg) in arguments.iter().enumerate() {
        //                         if arg == &local {
        //                             is_invariant_broken[i] = true;
        //                             found = true;
        //                             break;
        //                         }
        //                     }
        //                     assert!(found);
        //                 }
        //                 _ => unreachable!(),
        //             }
        //         }
        //         _ => {
        //             unreachable!();
        //         }
        //     }
        // }
        Ok(is_invariant_broken)
    }

    fn encode_contract_broken_invariants(
        &mut self,
        procedure_contract: &ProcedureContractMirDef<'tcx>,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<Vec<vir_high::Expression>> {
        let mut arguments: Vec<vir_high::Expression> = Vec::new();
        for local in &procedure_contract.args {
            let parameter = self.encode_local(*local)?;
            arguments.push(parameter.into());
        }
        let mut broken_invariants = Vec::new();
        for (assertion, assertion_substs) in
            procedure_contract.broken_precondition_invariants(self.encoder.env(), substs)
        {
            let expression = self.encoder.encode_assertion_high(
                assertion,
                None,
                &arguments,
                None,
                self.def_id,
                assertion_substs,
            )?;
            match expression {
                vir_high::Expression::FuncApp(mut app) => {
                    assert_eq!(
                        app.function_name,
                        "m_prusti_contracts$$prusti_broken_invariant"
                    );
                    assert_eq!(app.arguments.len(), 1);
                    match app.arguments.pop() {
                        Some(local) => {
                            broken_invariants.push(local);
                        }
                        _ => unreachable!(),
                    }
                }
                _ => {
                    unreachable!();
                }
            }
        }
        Ok(broken_invariants)
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
                        vir_high::Statement::inhale_predicate_no_pos(predicate.clone()),
                        encoded_local.position,
                        ErrorCtxt::UnexpectedStorageLive,
                    )?,
                );
                procedure_builder.add_dealloc_statement(
                    self.encoder.set_surrounding_error_context_for_statement(
                        vir_high::Statement::exhale_predicate_no_pos(predicate.clone()),
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
        if self.mir.basic_blocks.is_empty() {
            block_builder.set_successor_exit(SuccessorExitKind::Return);
        } else {
            block_builder.set_successor_jump(vir_high::Successor::Goto(
                self.encode_basic_block_label(self.mir.basic_blocks.start_node()),
            ));
        }
        block_builder.build();
        procedure_builder.set_entry(entry_label);
        self.encode_specification_blocks(procedure_builder.name())?;
        self.reachable_blocks
            .insert(self.mir.basic_blocks.start_node());
        let predecessors = self.mir.basic_blocks.predecessors();
        for (bb, data) in
            prusti_rustc_interface::middle::mir::traversal::reverse_postorder(self.mir)
        {
            if !self.specification_blocks.is_specification_block(bb)
                && self.reachable_blocks.contains(&bb)
            {
                self.create_locals_live_entry(bb, predecessors.get(bb).unwrap())?;
                self.encode_basic_block(procedure_builder, bb, data)?;
            }
        }
        assert!(
            self.loop_invariant_encoding.is_empty(),
            "not consumed loop invariant: {:?}",
            self.loop_invariant_encoding.keys()
        );
        assert!(
            self.specification_region_encoding_statements.is_empty(),
            "not consumed specification region: {:?}",
            self.specification_region_encoding_statements.keys()
        );
        assert!(
            self.specification_on_drop_unwind.is_empty(),
            "not consumed specification on drop unwind: {:?}",
            self.specification_on_drop_unwind.keys()
        );
        assert!(
            self.add_specification_before_terminator.is_empty(),
            "not consumed specification before terminator: {:?}",
            self.add_specification_before_terminator.keys()
        );
        Ok(())
    }

    fn encode_postcondition_frame_check(
        &mut self,
        procedure_builder: &mut ProcedureBuilder,
    ) -> SpannedEncodingResult<()> {
        // FIXME: code duplication with encode_function_call.
        let entry_label = vir_high::BasicBlockId::new("label_entry".to_string());
        let mut block_builder = procedure_builder.create_basic_block_builder(entry_label.clone());
        block_builder.set_successor_exit(SuccessorExitKind::Return);
        let location = mir::Location {
            block: 0usize.into(),
            statement_index: 0,
        };
        let span = self.mir.span;
        let called_def_id = self.def_id;
        let call_substs = self.encoder.env().query.identity_substs(called_def_id);
        let args: Vec<_> = self
            .mir
            .args_iter()
            .map(|arg| mir::Operand::Move(arg.into()))
            .collect();
        let target_place_local = mir::RETURN_PLACE;
        let destination: mir::Place = target_place_local.into();
        // let target = Some(1usize.into());
        // let cleanup = Some(1usize.into());

        let is_unsafe = self.encoder.env().query.is_unsafe_function(called_def_id);
        let is_checked = false;

        // self.encode_function_call(&mut block_builder, location, span, called_def_id, call_substs, &args, destination, &target, &cleanup)?;

        let old_label = self.fresh_old_label();
        block_builder.add_statement(self.encoder.set_statement_error_ctxt(
            vir_high::Statement::old_label_no_pos(old_label.clone()),
            span,
            ErrorCtxt::ProcedureCall,
            self.def_id,
        )?);

        let procedure_contract = self
            .encoder
            .get_mir_procedure_contract_for_call(self.def_id, called_def_id, call_substs)
            .with_span(span)?;
        let broken_invariants =
            self.encode_broken_invariant_argument_mask(&procedure_contract, call_substs)?;

        let mut arguments = Vec::new();
        let mut consume_arguments = Vec::new();
        let mut broken_invariant_places = Vec::new();
        let mut broken_invariant_address_memory_blocks = Vec::new();
        for (arg, is_invariant_broken) in args.iter().zip(broken_invariants.iter()) {
            // FIXME: Code repetition with encode_function_call.
            arguments.push(
                self.encoder
                    .encode_operand_high(self.mir, arg, span)
                    .with_span(span)?,
            );
            if *is_invariant_broken {
                match arg {
                    mir::Operand::Copy(_) => unimplemented!(
                        "TODO: A proper error message that only moved references are supported"
                    ),
                    mir::Operand::Move(place) => {
                        let encoded_place = self.encode_place(*place, None)?;
                        let address_memory_block =
                            self.encode_reference_address_memory_block(encoded_place)?;
                        broken_invariant_address_memory_blocks.push(address_memory_block.clone());
                        let dealloc_address_statement =
                            vir_high::Statement::exhale_predicate_no_pos(address_memory_block);
                        consume_arguments.add_statement(self.encoder.set_statement_error_ctxt(
                            dealloc_address_statement,
                            span,
                            ErrorCtxt::ProcedureCall,
                            self.def_id,
                        )?);
                        let deref_place = self.encoder.env().tcx().mk_place_deref(*place);
                        for field_place in analysis::mir_utils::expand_struct_place(
                            deref_place,
                            self.mir,
                            self.encoder.env().tcx(),
                            None,
                        ) {
                            let encoded_arg = self.encode_place(field_place, None)?;
                            broken_invariant_places.push(encoded_arg.clone());
                            let statement = vir_high::Statement::exhale_predicate_no_pos(
                                vir_high::Predicate::owned_non_aliased_no_pos(encoded_arg),
                            );
                            consume_arguments.add_statement(
                                self.encoder.set_statement_error_ctxt(
                                    statement,
                                    span,
                                    ErrorCtxt::ProcedureCall,
                                    self.def_id,
                                )?,
                            );
                        }
                    }
                    mir::Operand::Constant(_) => unimplemented!(
                        "TODO: A proper error message that only moved references are supported"
                    ),
                }
            } else {
                let encoded_arg =
                    self.encode_statement_operand_no_refs(&mut consume_arguments, location, arg)?;
                let statement = vir_high::Statement::consume_no_pos(encoded_arg);
                consume_arguments.add_statement(self.encoder.set_statement_error_ctxt(
                    statement,
                    span,
                    ErrorCtxt::ProcedureCall,
                    self.def_id,
                )?);
            }
        }
        assert_eq!(arguments.len(), broken_invariants.len());

        self.check_refinement(&procedure_contract.specification.pres)?;
        let precondition_expressions =
            self.encode_precondition_expressions(&procedure_contract, call_substs, &arguments)?;
        let mut precondition_conjuncts = Vec::new();
        for expression in precondition_expressions {
            if let Some(expression) = self.convert_expression_to_check_mode_call_site(
                expression, is_unsafe, is_checked, &arguments,
            )? {
                // let exhale_statement = self.encoder.set_statement_error_ctxt(
                //     vir_high::Statement::exhale_expression_no_pos(expression),
                //     span,
                //     ErrorCtxt::ExhaleMethodPrecondition,
                //     self.def_id,
                // )?;
                // block_builder.add_statement(exhale_statement);
                let conjunct = self.encoder.set_expression_error_ctxt(
                    expression,
                    span,
                    ErrorCtxt::ExhaleMethodPrecondition,
                    self.def_id,
                );
                precondition_conjuncts.push(conjunct);
            }
        }
        let exhale_statement = self.encoder.set_statement_error_ctxt(
            vir_high::Statement::exhale_expression_no_pos(
                precondition_conjuncts.into_iter().conjoin(),
                Some(old_label.clone()),
            ),
            span,
            ErrorCtxt::ExhaleMethodPrecondition,
            self.def_id,
        )?;
        block_builder.add_statement(exhale_statement);
        block_builder.add_statements(consume_arguments);

        let position = self.register_error(location, ErrorCtxt::ProcedureCall);
        let encoded_target_place = self
            .encode_place(destination, None)?
            .set_default_position(position);
        self.check_refinement(&procedure_contract.specification.posts)?;
        let postcondition_expressions = self.encode_postcondition_expressions(
            &procedure_contract,
            call_substs,
            arguments.clone(),
            &encoded_target_place,
            &old_label,
        )?;
        let size = self.encoder.encode_type_size_expression(
            self.encoder.get_local_type(self.mir, target_place_local)?,
        )?;
        let target_memory_block =
            vir_high::Predicate::memory_block_stack_no_pos(encoded_target_place.clone(), size);
        block_builder.add_statement(self.encoder.set_statement_error_ctxt(
            vir_high::Statement::exhale_predicate_no_pos(target_memory_block),
            span,
            ErrorCtxt::ProcedureCall,
            self.def_id,
        )?);
        let statement = vir_high::Statement::inhale_predicate_no_pos(
            vir_high::Predicate::owned_non_aliased_no_pos(encoded_target_place.clone()),
        );
        block_builder.add_statement(self.encoder.set_statement_error_ctxt(
            statement,
            span,
            ErrorCtxt::ProcedureCall,
            self.def_id,
        )?);
        for memory_block in broken_invariant_address_memory_blocks {
            let statement = vir_high::Statement::inhale_predicate_no_pos(memory_block);
            block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                statement,
                span,
                ErrorCtxt::ProcedureCall,
                self.def_id,
            )?);
        }
        for encoded_place in broken_invariant_places {
            let statement = vir_high::Statement::inhale_predicate_no_pos(
                vir_high::Predicate::owned_non_aliased_no_pos(encoded_place),
            );
            block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                statement,
                span,
                ErrorCtxt::ProcedureCall,
                self.def_id,
            )?);
        }
        let result_place = vec![encoded_target_place.clone()];
        let mut postcondition_conjuncts = Vec::new();
        for expression in postcondition_expressions {
            if let Some(expression) = self.convert_expression_to_check_mode_call_site(
                expression,
                is_unsafe,
                is_checked,
                &result_place,
            )? {
                // let inhale_statement = self.encoder.set_statement_error_ctxt(
                //     vir_high::Statement::inhale_expression_no_pos(expression),
                //     span,
                //     ErrorCtxt::MethodPostconditionFraming,
                //     self.def_id,
                // )?;
                // block_builder.add_statement(inhale_statement);
                let conjunct = self.encoder.set_expression_error_ctxt(
                    expression,
                    span,
                    ErrorCtxt::MethodPostconditionFraming,
                    self.def_id,
                );
                postcondition_conjuncts.push(conjunct);
            }
        }
        let inhale_statement = self.encoder.set_statement_error_ctxt(
            vir_high::Statement::inhale_expression_no_pos(
                postcondition_conjuncts.into_iter().conjoin(),
                None,
            ),
            span,
            ErrorCtxt::MethodPostconditionFraming,
            self.def_id,
        )?;
        block_builder.add_statement(inhale_statement);

        let assume_statement = self.encoder.set_statement_error_ctxt(
            vir_high::Statement::assume_no_pos(false.into()),
            span,
            ErrorCtxt::UnexpectedAssumeEndMethodPostconditionFraming,
            self.def_id,
        )?;
        block_builder.add_statement(assume_statement);

        block_builder.build();
        procedure_builder.set_entry(entry_label);
        Ok(())
    }

    fn create_locals_live_entry(
        &mut self,
        bb: mir::BasicBlock,
        predecessors: &[mir::BasicBlock],
    ) -> SpannedEncodingResult<()> {
        let mut predecessors_iter = predecessors.iter().filter(|predecessor| {
            !self
                .specification_blocks
                .is_specification_block(**predecessor)
                && self.reachable_blocks.contains(predecessor)
        });
        let locals_live_in_block = if let Some(first_predecessor) = predecessors_iter.next() {
            let mut locals_live_in_block = self.locals_live_in_block[first_predecessor].clone();
            for predecessor in predecessors_iter {
                if let Some(predecessor_locals) = &self.locals_live_in_block.get(predecessor) {
                    locals_live_in_block.retain(|local| predecessor_locals.contains(local));
                }
            }
            locals_live_in_block
        } else {
            BTreeSet::new()
        };
        assert!(self
            .locals_live_in_block
            .insert(bb, locals_live_in_block)
            .is_none());
        Ok(())
    }

    fn encode_basic_block(
        &mut self,
        procedure_builder: &mut ProcedureBuilder,
        bb: mir::BasicBlock,
        data: &mir::BasicBlockData<'tcx>,
    ) -> SpannedEncodingResult<()> {
        self.derived_lifetimes_yet_to_kill.clear();
        let to_remove = self
            .reborrow_lifetimes_to_remove_for_block
            .entry(bb)
            .or_insert_with(BTreeSet::new);
        to_remove.extend(self.lifetimes.get_all_ignored_loans());
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
        if let Some(statements) = self.add_specification_before_terminator.remove(&bb) {
            block_builder.add_statements(statements);
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
            if self.needs_termination(bb)
                && statement.clone().unwrap_loop_invariant().variant.is_none()
            {
                block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                    vir_high::Statement::assert_no_pos(false.into()),
                    data.terminator().source_info.span,
                    ErrorCtxt::UnexpectedReachableLoop,
                    self.def_id,
                )?);
            }
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
        block_builder.add_comment(format!("{location:?} {statement:?}"));
        match &statement.kind {
            mir::StatementKind::StorageLive(local)
                if self
                    .locals_used_only_in_specification_regions
                    .contains(local) =>
            {
                block_builder.add_comment(format!("StorageLive for local {:?} is ignored because it is only used in specification regions", local));
            }
            mir::StatementKind::StorageDead(local)
                if self
                    .locals_used_only_in_specification_regions
                    .contains(local) =>
            {
                block_builder.add_comment(format!("StorageDead for local {:?} is ignored because it is only used in specification regions", local));
            }
            mir::StatementKind::StorageLive(local) => {
                self.locals_without_explicit_allocation.remove(local);
                let block_locals = self.locals_live_in_block.get_mut(&location.block).unwrap();
                assert!(block_locals.insert(*local));
                let statements = self.encode_statement_storage_live(*local, location)?;
                block_builder.add_statements(statements);
            }
            mir::StatementKind::StorageDead(local) => {
                self.locals_without_explicit_allocation.remove(local);
                let block_locals = self.locals_live_in_block.get_mut(&location.block).unwrap();
                if !block_locals.remove(local) {
                    self.missing_live_locals.push((location.block, *local));
                }
                let memory_block = self
                    .encoder
                    .encode_memory_block_for_local(self.mir, *local)?;
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::UnexpectedStorageDead,
                    vir_high::Statement::exhale_predicate_no_pos(memory_block),
                )?);
                let memory_block_drop = self
                    .encoder
                    .encode_memory_block_drop_for_local(self.mir, *local)?;
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::UnexpectedStorageDead,
                    vir_high::Statement::exhale_predicate_no_pos(memory_block_drop),
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

    fn encode_statement_storage_live(
        &mut self,
        local: mir::Local,
        location: mir::Location,
    ) -> SpannedEncodingResult<Vec<vir_high::Statement>> {
        let mut statements = Vec::new();
        let memory_block = self
            .encoder
            .encode_memory_block_for_local(self.mir, local)?;
        statements.push(self.set_statement_error(
            location,
            ErrorCtxt::UnexpectedStorageLive,
            vir_high::Statement::inhale_predicate_no_pos(memory_block),
        )?);
        let memory_block_drop = self
            .encoder
            .encode_memory_block_drop_for_local(self.mir, local)?;
        statements.push(self.set_statement_error(
            location,
            ErrorCtxt::UnexpectedStorageLive,
            vir_high::Statement::inhale_predicate_no_pos(memory_block_drop),
        )?);
        Ok(statements)
    }

    fn encode_statement_assign(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        encoded_target: vir_crate::high::Expression,
        source: &mir::Rvalue<'tcx>,
    ) -> SpannedEncodingResult<()> {
        let span = self.encoder.get_mir_location_span(self.mir, location);
        match source {
            mir::Rvalue::Use(operand) => {
                self.encode_assign_operand(block_builder, location, encoded_target, operand)?;
            }
            mir::Rvalue::Repeat(operand, count) => {
                let encoded_operand =
                    self.encode_statement_operand_no_refs(block_builder, location, operand)?;
                let encoded_count = self.encoder.compute_array_len(*count).with_span(span)?;
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
                // let is_reborrow = place
                //     .iter_projections()
                //     .filter(|(place, projection)| {
                //         projection == &mir::ProjectionElem::Deref
                //             && place.ty(self.mir, self.encoder.env().tcx()).ty.is_ref()
                //     })
                //     .last();
                let is_reborrow = self.check_if_reborrow(*place);
                let uniquness = match borrow_kind {
                    mir::BorrowKind::Mut { .. } => vir_high::ty::Uniqueness::Unique,
                    _ => vir_high::ty::Uniqueness::Shared,
                };
                let encoded_place = self.encode_place(*place, None)?;
                let region_name = region.to_text();
                let new_borrow_lifetime = vir_high::ty::LifetimeConst { name: region_name };

                let encoded_rvalue = if let Some((_, region)) = is_reborrow {
                    // let reference_type = place.ty(self.mir, self.encoder.env().tcx());
                    // let deref_lifetime = match reference_type.ty.kind() {
                    //     ty::TyKind::Ref(region, _, _) => vir_high::ty::LifetimeConst {
                    //         name: region.to_text(),
                    //     },
                    //     _ => unreachable!(),
                    // };
                    let deref_lifetime = vir_high::ty::LifetimeConst::new(region.to_text());
                    if let vir_high::Expression::Local(local) = &encoded_target {
                        self.points_to_reborrow.insert(local.clone());
                    }
                    vir_high::Rvalue::reborrow(
                        new_borrow_lifetime,
                        deref_lifetime,
                        encoded_place,
                        uniquness,
                        self.lifetime_token_fractional_permission(self.lifetime_count),
                    )
                } else {
                    vir_high::Rvalue::ref_(
                        new_borrow_lifetime,
                        encoded_place,
                        uniquness,
                        self.lifetime_token_fractional_permission(self.lifetime_count),
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
            mir::Rvalue::Cast(_kind, operand, ty) => {
                let encoded_operand =
                    self.encode_statement_operand_no_refs(block_builder, location, operand)?;
                let ty = self.encoder.encode_type_high(*ty)?;
                let encoded_rvalue = vir_high::Rvalue::cast(encoded_operand, ty);
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::Assign,
                    vir_high::Statement::assign_no_pos(encoded_target, encoded_rvalue),
                )?);
                // self.encode_assign_cast(block_builder, location, encoded_target, *kind, operand, *ty)?;
                // TODO: For raw pointers do nothing because we care only about
                // the type of the target.
                // unimplemented!("kind={kind:?} operand={operand:?} ty={ty:?}");
            }
            mir::Rvalue::BinaryOp(op, box (left, right)) => {
                let (encoded_left, left_post_statements) =
                    self.encode_statement_operand(block_builder, location, left)?;
                let (encoded_right, right_post_statements) =
                    self.encode_statement_operand(block_builder, location, right)?;
                let kind = self.encode_binary_op_kind(*op, encoded_target.get_type())?;
                let encoded_rvalue = vir_high::Rvalue::binary_op(kind, encoded_left, encoded_right);
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::Assign,
                    vir_high::Statement::assign_no_pos(encoded_target, encoded_rvalue),
                )?);
                block_builder.add_statements(left_post_statements);
                block_builder.add_statements(right_post_statements);
            }
            mir::Rvalue::CheckedBinaryOp(op, box (left, right)) => {
                let (encoded_left, left_post_statements) =
                    self.encode_statement_operand(block_builder, location, left)?;
                let (encoded_right, right_post_statements) =
                    self.encode_statement_operand(block_builder, location, right)?;
                let kind = self.encode_binary_op_kind(*op, encoded_target.get_type())?;
                let encoded_rvalue =
                    vir_high::Rvalue::checked_binary_op(kind, encoded_left, encoded_right);
                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::Assign,
                    vir_high::Statement::assign_no_pos(encoded_target, encoded_rvalue),
                )?);
                block_builder.add_statements(left_post_statements);
                block_builder.add_statements(right_post_statements);
            }
            // mir::Rvalue::NullaryOp(NullOp, Ty<'tcx>),
            mir::Rvalue::UnaryOp(op, operand) => {
                let (encoded_operand, post_statements) =
                    self.encode_statement_operand(block_builder, location, operand)?;
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
                block_builder.add_statements(post_statements);
            }
            mir::Rvalue::Discriminant(place) => {
                let encoded_place = self.encode_place(*place, None)?;

                // let deref_base = encoded_place.get_dereference_base().cloned();
                let source_permission = self.encode_automatic_open_reference(
                    block_builder,
                    location,
                    // &deref_base,
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

                self.encode_automatic_close_reference(
                    block_builder,
                    location,
                    // &deref_base,
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
                    let field_name = variant_def.fields[(*active_field_index).into()]
                        .ident(tcx)
                        .to_string();
                    ty = ty.variant(field_name.into());
                }
                ty
            }
            mir::AggregateKind::Closure(_, _) => unimplemented!(),
            mir::AggregateKind::Generator(_, _, _) => unimplemented!(),
        };
        let base_lifetimes = ty.get_lifetimes();
        let lifetime_replacement_map = self
            .lifetimes
            .construct_replacement_map(location, base_lifetimes);

        let mut encoded_operands = Vec::new();
        for operand in operands {
            let mut encoded_operand =
                self.encode_statement_operand_no_refs(block_builder, location, operand)?;
            let new_expression = encoded_operand
                .expression
                .clone()
                .replace_lifetimes(&lifetime_replacement_map);
            if encoded_operand.kind == vir_high::OperandKind::Move {
                if let vir_high::Type::Reference(ty) = encoded_operand.expression.get_type() {
                    // FIXME: Figure out whether we need to do this also for Copy.
                    block_builder.add_statement(self.set_statement_error(
                        location,
                        ErrorCtxt::LifetimeEncoding,
                        vir_high::Statement::bor_shorten_no_pos(
                            lifetime_replacement_map[&ty.lifetime].clone(),
                            ty.lifetime.clone(),
                            encoded_operand.expression.clone(),
                            self.lifetime_token_fractional_permission(self.lifetime_count),
                        ),
                    )?);
                }
            }
            encoded_operand.expression = new_expression;
            encoded_operands.push(encoded_operand);
        }
        let encoded_rvalue = vir_high::Rvalue::aggregate(ty, encoded_operands);
        block_builder.add_statement(vir_high::Statement::assign(
            encoded_target,
            encoded_rvalue,
            self.register_error(location, ErrorCtxt::Assign),
        ));
        Ok(())
    }

    // FIXME: Dead code, remove.
    fn is_manually_managed(&self, place: &vir_high::Expression) -> bool {
        for manual_place in &self.manually_managed_places {
            if place.has_prefix(manual_place) {
                return true;
            }
        }
        false
    }

    fn encode_close_reference(
        &mut self,
        location: mir::Location,
        deref_base: &Option<vir_high::Expression>,
        place: vir_high::Expression,
        permission: Option<vir_high::VariableDecl>,
        is_user_written: bool,
    ) -> SpannedEncodingResult<Option<vir_high::Statement>> {
        let mut statement = None;
        if let Some(base) = deref_base {
            match base.get_type() {
                vir_high::ty::Type::Reference(vir_high::ty::Reference {
                    lifetime,
                    uniqueness,
                    ..
                }) => {
                    if *uniqueness == vir_high::ty::Uniqueness::Unique {
                        statement = Some(self.set_statement_error(
                            location,
                            ErrorCtxt::CloseMutRef,
                            vir_high::Statement::close_mut_ref_no_pos(
                                lifetime.clone(),
                                self.lifetime_token_fractional_permission(self.lifetime_count),
                                place,
                                is_user_written,
                            ),
                        )?);
                    } else {
                        statement = Some(self.set_statement_error(
                            location,
                            ErrorCtxt::CloseFracRef,
                            vir_high::Statement::close_frac_ref_no_pos(
                                lifetime.clone(),
                                self.lifetime_token_fractional_permission(self.lifetime_count),
                                place,
                                permission.unwrap(),
                                is_user_written,
                            ),
                        )?);
                    }
                }
                vir_high::ty::Type::Pointer(_) => {}
                _ => unreachable!(),
            }
        }
        Ok(statement)
    }

    fn encode_automatic_close_reference(
        &mut self,
        block_builder: &mut impl StatementSequenceBuilder,
        location: mir::Location,
        place: vir_high::Expression,
        permission: Option<vir_high::VariableDecl>,
    ) -> SpannedEncodingResult<()> {
        if self.is_manually_managed(&place) {
            return Ok(());
        }
        let deref_base = place.get_dereference_base().cloned();
        let statement =
            self.encode_close_reference(location, &deref_base, place, permission, false)?;
        if let Some(statement) = statement {
            block_builder.add_statement(statement);
        }
        Ok(())
    }

    fn encode_open_reference(
        &mut self,
        location: mir::Location,
        deref_base: &Option<vir_high::Expression>,
        place: vir_high::Expression,
        is_user_written: bool,
    ) -> SpannedEncodingResult<(Option<vir_high::VariableDecl>, Option<vir_high::Statement>)> {
        let mut variable = None;
        let mut statement = None;
        if let Some(base) = deref_base {
            match base.get_type() {
                vir_high::ty::Type::Reference(vir_high::ty::Reference {
                    lifetime,
                    uniqueness,
                    ..
                }) => {
                    if *uniqueness == vir_high::ty::Uniqueness::Unique {
                        statement = Some(self.set_statement_error(
                            location,
                            ErrorCtxt::OpenMutRef,
                            vir_high::Statement::open_mut_ref_no_pos(
                                lifetime.clone(),
                                self.lifetime_token_fractional_permission(self.lifetime_count),
                                place,
                                is_user_written,
                            ),
                        )?);
                    } else {
                        let permission =
                            self.fresh_ghost_variable("tmp_frac_ref_perm", vir_high::Type::MPerm);
                        variable = Some(permission.clone());
                        statement = Some(self.set_statement_error(
                            location,
                            ErrorCtxt::OpenFracRef,
                            vir_high::Statement::open_frac_ref_no_pos(
                                lifetime.clone(),
                                permission,
                                self.lifetime_token_fractional_permission(self.lifetime_count),
                                place,
                                is_user_written,
                            ),
                        )?);
                    }
                }
                vir_high::ty::Type::Pointer(_) => {
                    // Note: if the dereferenced place is behind a raw pointer
                    // and reference, we require the user to manually open the
                    // reference.
                }
                _ => unreachable!("place: {} deref_base: {:?}", place, base),
            }
        };
        Ok((variable, statement))
    }

    fn encode_automatic_open_reference(
        &mut self,
        block_builder: &mut impl StatementSequenceBuilder,
        location: mir::Location,
        // deref_base: &Option<vir_high::Expression>,
        place: vir_high::Expression,
    ) -> SpannedEncodingResult<Option<vir_high::VariableDecl>> {
        // return Ok(None);
        if self.is_manually_managed(&place) {
            return Ok(None);
        }
        let deref_place = place.get_dereference_base().cloned();
        let (variable, statement) =
            self.encode_open_reference(location, &deref_place, place.clone(), false)?;
        if let Some(statement) = statement {
            block_builder.add_statement(statement);
        }
        if variable.is_some() {
            Ok(variable)
        } else {
            Ok(self.lookup_opened_reference_place_permission(&place))
            // // Check whether the place was manually opened. FIXME: The
            // // permission amount is cotrol-flow dependent and, therefore, should
            // // be inserted by the fold-unfold algorithm.
            // for (opened_place, variable) in &self.opened_reference_place_permissions {
            //     if place.has_prefix(opened_place) {
            //         return Ok(variable.clone());
            //     }
            // }
            // Ok(None)
        }
    }

    /// Check whether the place was manually opened. FIXME: The
    /// permission amount is cotrol-flow dependent and, therefore, should
    /// be inserted by the fold-unfold algorithm.
    fn lookup_opened_reference_place_permission(
        &self,
        place: &vir_high::Expression,
    ) -> Option<vir_high::VariableDecl> {
        for (opened_place, variable) in &self.opened_reference_place_permissions {
            if place.has_prefix(opened_place) {
                return variable.clone();
            }
        }
        None
    }

    fn encode_assign_operand(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        encoded_target: vir_crate::high::Expression,
        operand: &mir::Operand<'tcx>,
    ) -> SpannedEncodingResult<()> {
        let span = self.encoder.get_span_of_location(self.mir, location);

        // let deref_base = encoded_target.get_dereference_base().cloned();
        let target_permission = self.encode_automatic_open_reference(
            block_builder,
            location,
            // &deref_base,
            encoded_target.clone(),
        )?;
        match operand {
            mir::Operand::Move(source @ mir::Place { local, .. })
            | mir::Operand::Copy(source @ mir::Place { local, .. })
                if source.as_local().is_some()
                    && self
                        .locals_used_only_in_specification_regions
                        .contains(local)
                    && source.ty(self.mir, self.encoder.env().tcx()).ty.is_unit() =>
            {
                block_builder.add_comment(format!(
                    "Assignment is ignored because {:?} is used only in specifications",
                    local
                ));
            }
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
                    "{encoded_source} is not place (encoded from: {source:?}"
                );

                // let deref_base = encoded_source.get_dereference_base().cloned();
                let source_permission = self.encode_automatic_open_reference(
                    block_builder,
                    location,
                    // &deref_base,
                    encoded_source.clone(),
                )?;

                block_builder.add_statement(self.set_statement_error(
                    location,
                    ErrorCtxt::CopyPlace,
                    vir_high::Statement::copy_place_no_pos(
                        encoded_target.clone(),
                        encoded_source.clone(),
                        // source_permission.clone(),
                    ),
                )?);

                self.encode_automatic_close_reference(
                    block_builder,
                    location,
                    // &deref_base,
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

        self.encode_automatic_close_reference(
            block_builder,
            location,
            // &deref_base,
            encoded_target,
            target_permission,
        )?;

        Ok(())
    }

    // fn encode_assign_cast(
    //     &mut self,
    //     block_builder: &mut BasicBlockBuilder,
    //     location: mir::Location,
    //     encoded_target: vir_crate::high::Expression,
    //     kind: mir::CastKind,
    //     operand: &mir::Operand<'tcx>,
    //     ty: ty::Ty<'tcx>,
    // ) -> SpannedEncodingResult<()> {
    //     let span = self.encoder.get_span_of_location(self.mir, location);
    //     match ty {}
    // }

    fn encode_statement_operand(
        &mut self,
        block_builder: &mut impl StatementSequenceBuilder,
        location: mir::Location,
        operand: &mir::Operand<'tcx>,
    ) -> SpannedEncodingResult<(vir_high::Operand, Vec<vir_high::Statement>)> {
        let mut post_statements = Vec::new();
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
                let source_permission = self.encode_automatic_open_reference(
                    block_builder,
                    location,
                    encoded_source.clone(),
                )?;
                self.encode_automatic_close_reference(
                    &mut post_statements,
                    location,
                    encoded_source.clone(),
                    source_permission,
                )?;
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
        Ok((encoded_operand, post_statements))
    }

    fn encode_statement_operand_no_refs(
        &mut self,
        block_builder: &mut impl StatementSequenceBuilder,
        location: mir::Location,
        operand: &mir::Operand<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Operand> {
        let (operand, post_statements) =
            self.encode_statement_operand(block_builder, location, operand)?;
        assert!(post_statements.is_empty(), "unimplemented");
        Ok(operand)
    }

    fn encode_binary_op_kind(
        &self,
        op: mir::BinOp,
        result_type: &vir_high::Type,
    ) -> SpannedEncodingResult<vir_high::BinaryOpKind> {
        let kind = match op {
            mir::BinOp::Add => vir_high::BinaryOpKind::Add,
            mir::BinOp::Sub => vir_high::BinaryOpKind::Sub,
            mir::BinOp::Mul => vir_high::BinaryOpKind::Mul,
            mir::BinOp::Div => vir_high::BinaryOpKind::Div,
            mir::BinOp::Rem => vir_high::BinaryOpKind::Mod,
            // mir::BinOp::BitXor => vir_high::BinaryOpKind::BitXor,
            mir::BinOp::BitAnd if result_type == &vir_high::Type::Bool => {
                vir_high::BinaryOpKind::And
            }
            // mir::BinOp::BitAnd => vir_high::BinaryOpKind::BitAnd,
            mir::BinOp::BitOr if result_type == &vir_high::Type::Bool => vir_high::BinaryOpKind::Or,
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
        block_builder.add_comment(format!("{location:?} {terminator:?}"));
        let span = self.encoder.get_span_of_location(self.mir, location);
        use prusti_rustc_interface::middle::mir::TerminatorKind;
        let successor = match &terminator {
            TerminatorKind::Goto { target } => {
                self.encode_lft_for_block(*target, location, block_builder)?;
                SuccessorBuilder::jump(vir_high::Successor::Goto(
                    self.encode_basic_block_label(*target),
                ))
            }
            TerminatorKind::SwitchInt { targets, discr } => {
                let switch_ty = discr.ty(self.mir, self.encoder.env().tcx());
                self.encode_terminator_switch_int(
                    block_builder,
                    location,
                    span,
                    targets,
                    discr,
                    switch_ty,
                )?
            }
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
            } => {
                self.encode_terminator_drop(block_builder, location, span, *place, *target, unwind)?
            }
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
                location,
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

    #[tracing::instrument(level = "debug", skip_all)]
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
            // Special handling of specifications:
            // 1. Specificaiton blocks.
            // 2. Specification regions.
            let all_targets = targets.all_targets();
            if all_targets.len() == 2 {
                if let Some(spec) = all_targets
                    .iter()
                    .position(|target| self.specification_blocks.is_specification_block(*target))
                {
                    let mut real_target = all_targets[(spec + 1) % 2];
                    let spec_target = all_targets[spec];
                    block_builder.add_comment(format!("Specification from block: {spec_target:?}"));
                    if let Some(statements) = self.specification_block_encoding.remove(&spec_target)
                    {
                        // We have the specification block, add it here.
                        block_builder.add_statements(statements);
                    } else if let Some(exit_target_block) = self
                        .specification_region_exit_target_block
                        .get(&spec_target)
                    {
                        // We have the specification region, use it as a real target.
                        real_target = *exit_target_block;
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
            // self.encode_lifetimes_dead_on_edge(
            //     block_builder,
            //     RichLocation::Mid(location),
            //     RichLocation::Start(mir::Location {
            //         block: target,
            //         statement_index: 0,
            //     }),
            // )?;
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
                false,
                encoded_target,
                location,
                block_builder,
            )?;
            successors.push((encoded_condition, encoded_target));
        }
        // self.encode_lifetimes_dead_on_edge(
        //     block_builder,
        //     RichLocation::Mid(location),
        //     RichLocation::Start(mir::Location {
        //         block: targets.otherwise(),
        //         statement_index: 0,
        //     }),
        // )?;
        let otherwise = self.encode_basic_block_label(targets.otherwise());
        let otherwise = self.encode_lft_for_block_with_edge(
            targets.otherwise(),
            false,
            otherwise,
            location,
            block_builder,
        )?;
        successors.push((true.into(), otherwise));
        Ok(SuccessorBuilder::jump(vir_high::Successor::GotoSwitch(
            successors,
        )))
    }

    fn encode_drop_contracts(
        &mut self,
        place: mir::Place<'tcx>,
        precondition_label: &str,
    ) -> SpannedEncodingResult<Option<(Vec<vir_high::Expression>, Vec<vir_high::Expression>)>> {
        let place_ty = place.ty(self.mir, self.encoder.env().tcx()).ty;
        if let Some(drop_method_def_id) = self.encoder.env().query.get_drop_method_id(place_ty) {
            let substs = self.encoder.env().query.identity_substs(drop_method_def_id);
            let procedure_contract = self
                .encoder
                .get_mir_procedure_contract_for_def(drop_method_def_id, substs)
                .with_span(self.mir.span)?;
            let self_place = self.encode_place(place, None)?;
            let reference_type = vir_high::Type::reference(
                vir_high::ty::LifetimeConst::erased(),
                vir_high::ty::Uniqueness::Unique,
                self_place.get_type().clone(),
            );
            let arguments = vec![vir_high::Expression::addr_of_no_pos(
                self_place,
                reference_type,
            )];
            let preconditions =
                self.encode_precondition_expressions(&procedure_contract, substs, &arguments)?;
            let result = vir_high::VariableDecl::new(
                "non-existant-result",
                vir_high::Type::tuple(Vec::new(), Vec::new()),
            )
            .into();
            let postconditions = self.encode_postcondition_expressions(
                &procedure_contract,
                substs,
                arguments,
                &result,
                precondition_label,
            )?;
            Ok(Some((preconditions, postconditions)))
        } else {
            Ok(None)
        }
    }
    fn encode_terminator_drop(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        span: Span,
        place: mir::Place<'tcx>,
        target: mir::BasicBlock,
        unwind: &Option<mir::BasicBlock>,
    ) -> SpannedEncodingResult<SuccessorBuilder> {
        let target_block_label = self.encode_basic_block_label(target);
        let target_block_label = self.encode_lft_for_block_with_edge(
            target,
            false,
            target_block_label,
            location,
            block_builder,
        )?;

        if config::check_no_drops() {
            let statement = self.encoder.set_statement_error_ctxt(
                vir_high::Statement::assert_no_pos(false.into()),
                span,
                ErrorCtxt::DropCall,
                self.def_id,
            )?;
            block_builder.add_statement(statement);
        }

        let old_label = self.fresh_old_label();
        let mut contracts = self.encode_drop_contracts(place, &old_label)?;

        let place = self.encode_place(place, None)?;
        let unwind_specification_statements =
            if let Some(region) = self.specification_on_drop_unwind.remove(&place) {
                Some(
                    self.specification_region_encoding_statements
                        .remove(&region)
                        .unwrap(),
                )
            } else {
                None
            };
        // FIXME: Assert that the lifetimes used in type of the place are alive
        // at this point (by exhaling them and inhaling). Do not forget to take
        // into account
        // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.GenericParamDef.html#structfield.pure_wrt_drop

        let target_permission =
            self.encode_automatic_open_reference(block_builder, location, place.clone())?;
        let mut close_ref_statements = Vec::new();
        self.encode_automatic_close_reference(
            &mut close_ref_statements,
            location,
            place.clone(),
            target_permission,
        )?;
        self.add_specification_before_terminator
            .insert(target, close_ref_statements.clone());

        let argument = vir_high::Operand::new(vir_high::OperandKind::Move, place);
        let statement = self.encoder.set_statement_error_ctxt(
            vir_high::Statement::consume_no_pos(argument),
            span,
            ErrorCtxt::DropCall,
            self.def_id,
        )?;
        statement.check_no_default_position();
        block_builder.add_statement(statement);
        if let Some((preconditions, _)) = &mut contracts {
            block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                vir_high::Statement::old_label_no_pos(old_label.clone()),
                span,
                ErrorCtxt::ProcedureCall,
                self.def_id,
            )?);
            let mut precondition_conjuncts = Vec::new();
            for expression in std::mem::take(preconditions) {
                let conjunct = self.encoder.set_expression_error_ctxt(
                    expression,
                    span,
                    ErrorCtxt::ExhaleMethodPrecondition,
                    self.def_id,
                );
                precondition_conjuncts.push(conjunct);
            }
            let exhale_statement = self.encoder.set_statement_error_ctxt(
                vir_high::Statement::exhale_expression_no_pos(
                    precondition_conjuncts.into_iter().conjoin(),
                    Some(old_label.clone()),
                ),
                span,
                ErrorCtxt::ExhaleMethodPrecondition,
                self.def_id,
            )?;
            block_builder.add_statement(exhale_statement);
        }
        if unwind.is_some() && contracts.is_none() {
            // If we have a contract, then we assume that the drop will not panic.
            let Some(unwind_block) = unwind else {
                unreachable!()
            };
            let encoded_unwind_block_label = self.encode_basic_block_label(*unwind_block);
            let encoded_unwind_block_label = self.encode_lft_for_block_with_edge(
                *unwind_block,
                true,
                encoded_unwind_block_label,
                location,
                block_builder,
            )?;
            if let Some(statements) = unwind_specification_statements {
                // We put the specification statements before the terminator
                // because `DropAndReplace` desugaring adds an assignment and we
                // need to put our specification after it.
                assert!(close_ref_statements.is_empty(), "unimplemented: which statements should go first? Closing the reference or user's specification?");
                self.add_specification_before_terminator
                    .insert(*unwind_block, statements);
            } else {
                self.add_specification_before_terminator
                    .insert(*unwind_block, close_ref_statements);
            }
            Ok(SuccessorBuilder::jump(vir_high::Successor::NonDetChoice(
                target_block_label,
                encoded_unwind_block_label,
            )))
        } else {
            assert!(unwind_specification_statements.is_none(), "TODO: A proper error message that `on_drop_unwind!` can be used only with places that can be unwound.");
            if let Some((_, postconditions)) = &mut contracts {
                let mut postcondition_conjuncts = Vec::new();
                for expression in std::mem::take(postconditions) {
                    let conjunct = self.encoder.set_expression_error_ctxt(
                        expression,
                        span,
                        ErrorCtxt::UnexpectedAssumeMethodPostcondition,
                        self.def_id,
                    );
                    postcondition_conjuncts.push(conjunct);
                }
                let inhale_statement = self.encoder.set_statement_error_ctxt(
                    vir_high::Statement::inhale_expression_no_pos(
                        postcondition_conjuncts.into_iter().conjoin(),
                        None,
                    ),
                    span,
                    ErrorCtxt::UnexpectedAssumeMethodPostcondition,
                    self.def_id,
                )?;
                block_builder.add_statement(inhale_statement);
            }
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
        let query = self.encoder.env().query;
        let (called_def_id, call_substs) =
            query.resolve_method_call(self.def_id, called_def_id, call_substs);
        let is_unsafe = query.is_unsafe_function(called_def_id);
        let no_panic_ensures_postcondition = self
            .encoder
            .no_panic_ensures_postcondition(called_def_id, Some(call_substs));
        let no_panic = self.encoder.no_panic(called_def_id, Some(call_substs));
        let is_checked = self.specification_blocks.is_checked(location.block);

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

        // find lifetimes for function args
        let has_erased_regions = call_substs.regions().any(|r| r.is_erased());
        let mut subst_regions = call_substs.regions().peekable();
        if !has_erased_regions && subst_regions.peek().is_some() {
            // use generic argument lifetimes
            lifetimes_to_exhale_inhale.extend(subst_regions.map(|r| r.to_text()));
        } else {
            // if we find any erased regions, cancel everything and fall back on resolving lifetimes from args directly
            // this happens e.g. when working with the result of trait method resolution, which erases lifetimes
            for arg in args {
                if let &mir::Operand::Move(place) = arg {
                    let encoded_place = self.encode_place(place, None)?;
                    let place_lifetimes = encoded_place.get_lifetimes();
                    for lifetime in place_lifetimes {
                        lifetimes_to_exhale_inhale.push(lifetime.name.clone());
                    }
                }
            }
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

        let procedure_contract = self
            .encoder
            .get_mir_procedure_contract_for_call(self.def_id, called_def_id, call_substs)
            .with_span(span)?;
        let broken_invariants =
            self.encode_broken_invariant_argument_mask(&procedure_contract, call_substs)?;

        let mut arguments = Vec::new();
        let mut consume_arguments = Vec::new();
        let mut broken_invariant_places = Vec::new();
        let mut broken_invariant_address_memory_blocks = Vec::new();
        for (arg, is_invariant_broken) in args.iter().zip(broken_invariants.iter()) {
            // FIXME: Code repetition with encode_postcondition_frame_check
            arguments.push(
                self.encoder
                    .encode_operand_high(self.mir, arg, span)
                    .with_span(span)?,
            );
            if *is_invariant_broken {
                match arg {
                    mir::Operand::Copy(_) => unimplemented!(
                        "TODO: A proper error message that only moved references are supported"
                    ),
                    mir::Operand::Move(place) => {
                        let encoded_place = self.encode_place(*place, None)?;
                        let address_memory_block =
                            self.encode_reference_address_memory_block(encoded_place)?;
                        broken_invariant_address_memory_blocks.push(address_memory_block.clone());
                        let dealloc_address_statement =
                            vir_high::Statement::exhale_predicate_no_pos(address_memory_block);
                        consume_arguments.add_statement(self.encoder.set_statement_error_ctxt(
                            dealloc_address_statement,
                            span,
                            ErrorCtxt::ProcedureCall,
                            self.def_id,
                        )?);
                        let deref_place = self.encoder.env().tcx().mk_place_deref(*place);
                        for field_place in analysis::mir_utils::expand_struct_place(
                            deref_place,
                            self.mir,
                            self.encoder.env().tcx(),
                            None,
                        ) {
                            let encoded_arg = self.encode_place(field_place, None)?;
                            broken_invariant_places.push(encoded_arg.clone());
                            let statement = vir_high::Statement::exhale_predicate_no_pos(
                                vir_high::Predicate::owned_non_aliased_no_pos(encoded_arg),
                            );
                            consume_arguments.add_statement(
                                self.encoder.set_statement_error_ctxt(
                                    statement,
                                    span,
                                    ErrorCtxt::ProcedureCall,
                                    self.def_id,
                                )?,
                            );
                        }
                    }
                    mir::Operand::Constant(_) => unimplemented!(
                        "TODO: A proper error message that only moved references are supported"
                    ),
                }
            } else {
                let encoded_arg =
                    self.encode_statement_operand_no_refs(&mut consume_arguments, location, arg)?;
                let statement = vir_high::Statement::consume_no_pos(encoded_arg);
                consume_arguments.add_statement(self.encoder.set_statement_error_ctxt(
                    statement,
                    span,
                    ErrorCtxt::ProcedureCall,
                    self.def_id,
                )?);
            }
            // let encoded_arg =
            //     self.encode_statement_operand_no_refs(&mut consume_arguments, location, arg)?;
            // let statement = vir_high::Statement::consume_no_pos(encoded_arg);
            // consume_arguments.add_statement(self.encoder.set_statement_error_ctxt(
            //     statement,
            //     span,
            //     ErrorCtxt::ProcedureCall,
            //     self.def_id,
            // )?);
        }
        self.encode_exhale_lifetime_tokens(
            block_builder,
            &lifetimes_to_exhale_inhale,
            derived_from.len() + 1,
        )?;

        if self.encoder.terminates(self.def_id, None) {
            self.encode_termination_measure_call_assertion(
                block_builder,
                span,
                &procedure_contract,
                call_substs,
                &arguments,
            )?;
        }

        let precondition_expressions =
            self.encode_precondition_expressions(&procedure_contract, call_substs, &arguments)?;
        // let has_no_precondition = precondition_expressions.is_empty();
        let is_precondition_checked =
            self.check_mode.check_specifications() || is_unsafe || is_checked; // || has_no_precondition;
        let mut precondition_conjuncts = Vec::new();
        for expression in precondition_expressions {
            if let Some(expression) = self.convert_expression_to_check_mode_call_site(
                expression, is_unsafe, is_checked, &arguments,
            )? {
                // let exhale_statement = self.encoder.set_statement_error_ctxt(
                //     vir_high::Statement::exhale_expression_no_pos(expression),
                //     span,
                //     ErrorCtxt::ExhaleMethodPrecondition,
                //     self.def_id,
                // )?;
                // block_builder.add_statement(exhale_statement);
                let conjunct = self.encoder.set_expression_error_ctxt(
                    expression,
                    span,
                    ErrorCtxt::ExhaleMethodPrecondition,
                    self.def_id,
                );
                precondition_conjuncts.push(conjunct);
            }
        }
        let exhale_statement = self.encoder.set_statement_error_ctxt(
            vir_high::Statement::exhale_expression_no_pos(
                precondition_conjuncts.into_iter().conjoin(),
                Some(old_label.clone()),
            ),
            span,
            ErrorCtxt::ExhaleMethodPrecondition,
            self.def_id,
        )?;
        block_builder.add_statement(exhale_statement);
        block_builder.add_statements(consume_arguments);

        let is_pure = self.encoder.is_pure(called_def_id, Some(call_substs));
        if !is_pure && self.check_mode.is_purification_group() {
            let heap_havoc_statement = self.encoder.set_statement_error_ctxt(
                vir_high::Statement::heap_havoc_no_pos(),
                span,
                ErrorCtxt::ExhaleMethodPrecondition,
                self.def_id,
            )?;
            block_builder.add_statement(heap_havoc_statement);
        }

        if self.encoder.env().query.is_closure(called_def_id) {
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
                    vir_high::Statement::exhale_predicate_no_pos(target_memory_block.clone()),
                    span,
                    ErrorCtxt::ProcedureCall,
                    self.def_id,
                )?);
                let target_label = self.encode_basic_block_label(*target_block);

                let fresh_destination_label = self.fresh_basic_block_label();
                let mut post_call_block_builder =
                    block_builder.create_basic_block_builder(fresh_destination_label.clone());
                post_call_block_builder.set_successor_jump(vir_high::Successor::Goto(target_label));
                for memory_block in broken_invariant_address_memory_blocks {
                    let statement = vir_high::Statement::inhale_predicate_no_pos(memory_block);
                    post_call_block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                        statement,
                        span,
                        ErrorCtxt::ProcedureCall,
                        self.def_id,
                    )?);
                }
                for encoded_place in broken_invariant_places {
                    let statement = vir_high::Statement::inhale_predicate_no_pos(
                        vir_high::Predicate::owned_non_aliased_no_pos(encoded_place),
                    );
                    post_call_block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                        statement,
                        span,
                        ErrorCtxt::ProcedureCall,
                        self.def_id,
                    )?);
                }
                let statement = vir_high::Statement::inhale_predicate_no_pos(
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
                    derived_from.len() + 1,
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

                let result_place = vec![encoded_target_place.clone()];
                let mut postcondition_conjuncts = Vec::new();
                for expression in postcondition_expressions {
                    if let Some(expression) = self.convert_expression_to_check_mode_call_site(
                        expression,
                        is_unsafe,
                        no_panic_ensures_postcondition || is_checked,
                        // // If we have no precondition, then we can soundly
                        // // allways include the function postcondition.
                        // has_no_precondition,
                        &result_place,
                    )? {
                        // let inhale_statement = self.encoder.set_statement_error_ctxt(
                        //     vir_high::Statement::inhale_expression_no_pos(expression),
                        //     span,
                        //     ErrorCtxt::UnexpectedAssumeMethodPostcondition,
                        //     self.def_id,
                        // )?;
                        // post_call_block_builder.add_statement(inhale_statement);
                        let conjunct = self.encoder.set_expression_error_ctxt(
                            expression,
                            span,
                            ErrorCtxt::UnexpectedAssumeMethodPostcondition,
                            self.def_id,
                        );
                        postcondition_conjuncts.push(conjunct);
                    }
                }
                let inhale_statement = self.encoder.set_statement_error_ctxt(
                    vir_high::Statement::inhale_expression_no_pos(
                        postcondition_conjuncts.into_iter().conjoin(),
                        None,
                    ),
                    span,
                    ErrorCtxt::UnexpectedAssumeMethodPostcondition,
                    self.def_id,
                )?;
                post_call_block_builder.add_statement(inhale_statement);
                if is_pure
                    && !self.encoder.env().callee_reaches_caller(
                        self.def_id,
                        called_def_id,
                        call_substs,
                    )
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
                    if self.check_mode.check_specifications()
                        || is_checked
                        || no_panic_ensures_postcondition
                    // // If we have no precondition, then we can soundly
                    // // allways include the function postcondition.
                    // has_no_precondition
                    {
                        post_call_block_builder.add_statement(assume_statement);
                    }
                } else {
                    // // FIXME: We do this because extern specs do not support primitive
                    // // types.
                    // let func_name = self.encoder.env().name.get_unique_item_name(called_def_id);
                    // if func_name.starts_with("std::ptr::mut_ptr::<impl *mut T>::is_null")
                    // || func_name.starts_with("core::std::ptr::mut_ptr::<impl *mut T>::is_null") {
                    //     let type_arguments = self
                    //     .encoder
                    //     .encode_generic_arguments_high(called_def_id, call_substs)
                    //     .with_span(span)?;
                    //     let expression = vir_high::Expression::equals(
                    //         encoded_target_place,
                    //         vir_high::Expression::builtin_func_app_no_pos(
                    //             vir_high::BuiltinFunc::IsNull,
                    //             type_arguments,
                    //             arguments,
                    //             vir_high::Type::Bool,
                    //         ),
                    //     );
                    //     let assume_statement = self.encoder.set_statement_error_ctxt(
                    //         vir_high::Statement::assume_no_pos(expression),
                    //         span,
                    //         ErrorCtxt::UnexpectedAssumeMethodPostcondition,
                    //         self.def_id,
                    //     )?;
                    //     if self.check_mode != CheckMode::CoreProof {
                    //         post_call_block_builder.add_statement(assume_statement);
                    //     }
                    // }
                }
                post_call_block_builder.build();

                if let Some(cleanup_block) = cleanup {
                    let fresh_cleanup_label = self.encode_function_call_cleanup_block(
                        *cleanup_block,
                        block_builder,
                        location,
                        span,
                        is_precondition_checked,
                        no_panic,
                        Some(target_memory_block),
                        &lifetimes_to_exhale_inhale,
                        &derived_from,
                        function_call_lifetime,
                    )?;
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
        } else if let Some(cleanup_block) = cleanup {
            let fresh_cleanup_label = self.encode_function_call_cleanup_block(
                *cleanup_block,
                block_builder,
                location,
                span,
                is_precondition_checked,
                no_panic,
                None,
                &lifetimes_to_exhale_inhale,
                &derived_from,
                function_call_lifetime,
            )?;
            block_builder.set_successor_jump(vir_high::Successor::Goto(fresh_cleanup_label));
        } else {
            // TODO: Can we always soundly assume false here?
            unimplemented!();
        }

        Ok(())
    }

    fn encode_function_call_cleanup_block(
        &mut self,
        cleanup_block: mir::BasicBlock,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        span: Span,
        is_precondition_checked: bool,
        no_panic: bool,
        target_memory_block: Option<vir_high::Predicate>,
        lifetimes_to_exhale_inhale: &[String],
        derived_from: &[vir_high::VariableDecl],
        function_call_lifetime: vir_high::VariableDecl,
    ) -> SpannedEncodingResult<vir_high::BasicBlockId> {
        let encoded_cleanup_block = self.encode_basic_block_label(cleanup_block);
        let fresh_cleanup_label = self.fresh_basic_block_label();
        let mut cleanup_block_builder =
            block_builder.create_basic_block_builder(fresh_cleanup_label.clone());
        cleanup_block_builder.set_successor_jump(vir_high::Successor::Goto(encoded_cleanup_block));

        if is_precondition_checked || no_panic {
            // If the precondition is checked or the function is
            // guaranteed to not panic, then the cleanup block is
            // unreachable.
            let statement = vir_high::Statement::assume_no_pos(false.into());
            cleanup_block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                statement,
                span,
                ErrorCtxt::ProcedureCall,
                self.def_id,
            )?);
        }

        if let Some(target_memory_block) = target_memory_block {
            let statement = vir_high::Statement::inhale_predicate_no_pos(target_memory_block);
            cleanup_block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                statement,
                span,
                ErrorCtxt::ProcedureCall,
                self.def_id,
            )?);
        }

        self.encode_inhale_lifetime_tokens(
            &mut cleanup_block_builder,
            lifetimes_to_exhale_inhale,
            derived_from.len() + 1,
        )?;
        let function_lifetime_return = self.encoder.set_statement_error_ctxt(
            vir_high::Statement::lifetime_return_no_pos(
                function_call_lifetime,
                derived_from.to_vec(),
                self.lifetime_token_fractional_permission(self.lifetime_count * derived_from.len()),
            ),
            self.mir.span,
            ErrorCtxt::LifetimeInhale,
            self.def_id,
        )?;
        cleanup_block_builder.add_statement(function_lifetime_return);

        if let Some(statements) = self
            .add_function_panic_specification_before_terminator
            .get(&(location.block, cleanup_block))
        {
            // We need to add the statements before the expiration
            // of the lifetime. Otherwise, the fold-unfold crashes.
            cleanup_block_builder.add_statements(statements.clone());
        }

        self.encode_lft_for_block(cleanup_block, location, &mut cleanup_block_builder)?;

        cleanup_block_builder.build();
        Ok(fresh_cleanup_label)
    }

    #[allow(clippy::too_many_arguments)]
    fn encode_terminator_assert(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
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
        block_builder.add_comment(format!("Rust assertion: {assert_msg}"));
        if self.check_panics {
            block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                vir_high::Statement::assert_no_pos(guard.clone()),
                span,
                error_ctxt,
                self.def_id,
            )?);
        }
        let successor = if let Some(cleanup) = cleanup {
            let target_label = self.encode_lft_for_block_with_edge(
                target,
                false,
                target_label,
                location,
                block_builder,
            )?;
            let cleanup_label = self.encode_basic_block_label(cleanup);
            let cleanup_label = self.encode_lft_for_block_with_edge(
                cleanup,
                true,
                cleanup_label,
                location,
                block_builder,
            )?;
            let successors = vec![(guard, target_label), (true.into(), cleanup_label)];
            SuccessorBuilder::jump(vir_high::Successor::GotoSwitch(successors))
        } else {
            self.encode_lft_for_block(target, location, block_builder)?;
            SuccessorBuilder::jump(vir_high::Successor::Goto(target_label))
        };
        Ok(successor)
    }

    /// Also marks it as reachable.
    fn encode_basic_block_label(&mut self, bb: mir::BasicBlock) -> vir_high::BasicBlockId {
        self.reachable_blocks.insert(bb);
        vir_high::BasicBlockId::new(format!("label_{bb:?}"))
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

    fn encode_specification_blocks(&mut self, procedure_name: &str) -> SpannedEncodingResult<()> {
        // Collect the entry points into the specification blocks.
        let mut entry_points: BTreeMap<_, _> = self
            .specification_blocks
            .entry_points()
            .map(|bb| (bb, Vec::new()))
            .collect();

        if config::dump_debug_info() {
            let graph = specification_blocks_to_graph(self.mir, &self.specification_blocks);
            prusti_common::report::log::report_with_writer(
                "graphviz_mir_dump_specification_blocks",
                format!("{}.dot", procedure_name),
                |writer| graph.write(writer).unwrap(),
            );
        }

        // Encode the specification blocks.

        // First, encode all specification expressions because they are sometimes used before they are declared.
        let mut encoded_blocks = FxHashSet::default();
        for bb in entry_points.keys() {
            let block = &self.mir[*bb];
            if self.try_encode_specification_expression(*bb, block)? {
                encoded_blocks.insert(*bb);
            }
        }

        // Encode the remaining specification blocks.
        for (bb, statements) in &mut entry_points {
            if !encoded_blocks.contains(bb) {
                self.encode_specification_block(*bb, statements, None)?;
            }
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
                self.encode_loop_specs(*loop_head, invariant_location, specification_blocks)?;
            self.loop_invariant_encoding
                .insert(invariant_location, statement);
        }

        self.encode_specification_regions()?;

        for region in self.specification_blocks.try_finally_regions() {
            let on_panic_specification_region_entry_block = self
                .specification_blocks
                .spec_id_to_entry_block(&region.on_panic_specification_region_id);
            let on_panic_statements = self
                .specification_region_encoding_statements
                .remove(&on_panic_specification_region_entry_block)
                .unwrap();
            let finally_specification_region_entry_block = self
                .specification_blocks
                .spec_id_to_entry_block(&region.finally_specification_region_id);
            let finally_statements = self
                .specification_region_encoding_statements
                .remove(&finally_specification_region_entry_block)
                .unwrap();
            for edge in &region.function_panic_exit_edges {
                let mut unwind_statements = on_panic_statements.clone();
                unwind_statements.extend(finally_statements.clone());
                assert!(self
                    .add_function_panic_specification_before_terminator
                    .insert(*edge, unwind_statements)
                    .is_none());
            }
            for (_source, target) in &region.panic_exit_edges {
                let mut unwind_statements = on_panic_statements.clone();
                unwind_statements.extend(finally_statements.clone());
                // FIXME: Not using source is probably wrong.
                assert!(self
                    .add_specification_before_terminator
                    .insert(*target, unwind_statements)
                    .is_none());
            }
            assert!(self
                .add_specification_before_terminator
                .insert(region.regular_exit_target_block, finally_statements)
                .is_none());
        }

        self.encode_ghost_blocks()?;

        Ok(())
    }

    #[allow(clippy::nonminimal_bool)]
    fn encode_specification_block(
        &mut self,
        bb: mir::BasicBlock,
        encoded_statements: &mut Vec<vir_high::Statement>,
        region_entry_block: Option<mir::BasicBlock>,
    ) -> SpannedEncodingResult<()> {
        let block = &self.mir[bb];
        if false
            // || self.try_encode_specification_expression(bb, block)?
            || self.try_encode_assert(bb, block, encoded_statements)?
            || self.try_encode_assume(bb, block, encoded_statements)?
            || self.try_encode_ghost_markers(bb, block, encoded_statements)?
            || self.try_encode_specification_markers(bb, block, encoded_statements)?
            || self.try_encode_specification_function_call(bb, block, encoded_statements, region_entry_block)?
        {
            Ok(())
        } else {
            unreachable!()
        }
    }

    /// Check whether this basic block defines a Prusti specification
    /// expression. If it does, encoding it and save it under the given
    /// specification id.
    fn try_encode_specification_expression(
        &mut self,
        bb: mir::BasicBlock,
        block: &mir::BasicBlockData<'tcx>,
    ) -> SpannedEncodingResult<bool> {
        for stmt in &block.statements {
            if let mir::StatementKind::Assign(box (
                _,
                mir::Rvalue::Aggregate(box mir::AggregateKind::Closure(cl_def_id, cl_substs), _),
            )) = stmt.kind
            {
                let def_id = cl_def_id;
                let expression = match self.encoder.get_prusti_specification_expression(def_id) {
                    Some(spec) => spec,
                    None => return Ok(false),
                };

                let span = self
                    .encoder
                    .get_definition_span(expression.expression.to_def_id());

                // We do not know the error context here, so we use a dummy one.
                let error_ctxt = ErrorCtxt::UnexpectedSpecificationExpression;

                let expression = self.encoder.set_expression_error_ctxt(
                    self.encoder.encode_loop_spec_high(
                        self.mir,
                        bb,
                        self.def_id,
                        cl_substs,
                        true,
                    )?,
                    span,
                    error_ctxt,
                    self.def_id,
                );

                let attrs = self.encoder.env().query.get_attributes(def_id);
                let Some(raw_spec_id) = prusti_interface::utils::read_prusti_attr("spec_id", attrs) else {
                    unreachable!();
                };

                self.specification_expressions
                    .insert(raw_spec_id, expression);

                return Ok(true);
            }
        }
        Ok(false)
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
                    self.encoder.encode_loop_spec_high(
                        self.mir,
                        bb,
                        self.def_id,
                        cl_substs,
                        false,
                    )?,
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

                if assertion.is_structural || self.check_mode.check_specifications() {
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
                    self.encoder.encode_loop_spec_high(
                        self.mir,
                        bb,
                        self.def_id,
                        cl_substs,
                        false,
                    )?,
                    span,
                    error_ctxt.clone(),
                    self.def_id,
                );

                let stmt = vir_high::Statement::assume_no_pos(expr);
                let stmt =
                    self.encoder
                        .set_statement_error_ctxt(stmt, span, error_ctxt, self.def_id)?;

                if assumption.is_structural || self.check_mode.check_specifications() {
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

    fn try_encode_specification_markers(
        &mut self,
        _bb: mir::BasicBlock,
        block: &mir::BasicBlockData<'tcx>,
        _encoded_statements: &mut [vir_high::Statement],
    ) -> SpannedEncodingResult<bool> {
        let is_marker = is_specification_begin_marker(self.encoder.env().query, block).is_some()
            || is_specification_end_marker(self.encoder.env().query, block)
            || is_try_finally_begin_marker(self.encoder.env().query, block).is_some()
            || is_try_finally_end_marker(self.encoder.env().query, block)
            || is_checked_block_begin_marker(self.encoder.env().query, block)
            || is_checked_block_end_marker(self.encoder.env().query, block);
        // for stmt in &block.statements {
        //     if let mir::StatementKind::Assign(box (
        //         _,
        //         mir::Rvalue::Aggregate(box mir::AggregateKind::Closure(cl_def_id, _), _),
        //     )) = stmt.kind
        //     {
        //         let is_begin = self
        //             .encoder
        //             .get_specification_region_begin(cl_def_id)
        //             .is_some();
        //         let is_end = self
        //             .encoder
        //             .get_specification_region_end(cl_def_id)
        //             .is_some();
        //         return Ok(is_begin || is_end);
        //     }
        // }
        Ok(is_marker)
    }

    // TODO: Move this function to a separate file and extract nested functions.
    fn try_encode_specification_function_call(
        &mut self,
        bb: mir::BasicBlock,
        block: &mir::BasicBlockData<'tcx>,
        encoded_statements: &mut Vec<vir_high::Statement>,
        region_entry_block: Option<mir::BasicBlock>,
    ) -> SpannedEncodingResult<bool> {
        let span = self.encoder.get_mir_terminator_span(block.terminator());
        let location = mir::Location {
            block: bb,
            statement_index: block.statements.len(),
        };
        let terminator_kind = &block.terminator().kind;
        match terminator_kind {
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
                    let full_called_function_name =
                        self.encoder.env().name.get_absolute_item_name(*def_id);
                    enum ArgKind {
                        Place(vir_high::Expression),
                        String(String),
                    }
                    fn extract_args<'p, 'v: 'p, 'tcx: 'v>(
                        mir: &mir::Body<'tcx>,
                        args: &[mir::Operand<'tcx>],
                        block: &mir::BasicBlockData<'tcx>,
                        encoder: &mut ProcedureEncoder<'p, 'v, 'tcx>,
                    ) -> SpannedEncodingResult<Vec<ArgKind>> {
                        // assert_eq!(args.len(), 1);
                        let mut encoded_args = Vec::new();
                        for arg in args {
                            match arg {
                                mir::Operand::Move(_) => {}
                                mir::Operand::Constant(constant) => {
                                    // FIXME: There should be a proper way of doing this.
                                    let value = format!("{constant:?}");
                                    let value =
                                        value.trim_start_matches("const \"").trim_end_matches('\"');
                                    encoded_args.push(ArgKind::String(value.to_string()));
                                    continue; // FIXME: Do proper control flow.
                                }
                                _ => {
                                    unreachable!()
                                }
                            }
                            let argument_place = if let mir::Operand::Move(place) = arg {
                                place
                            } else {
                                unreachable!()
                            };
                            // Find the place whose address was stored in the argument by
                            // iterating backwards through statements.
                            let mut statement_index = block.statements.len() - 1;
                            let place = loop {
                                if let Some(statement) = block.statements.get(statement_index) {
                                    if let mir::StatementKind::Assign(box (target_place, rvalue)) =
                                        &statement.kind
                                    {
                                        if target_place == argument_place {
                                            match rvalue {
                                                mir::Rvalue::AddressOf(_, place) => {
                                                    break encoder.encode_place(*place, None)?;
                                                }
                                                mir::Rvalue::Use(operand) => {
                                                    break encoder
                                                        .encoder
                                                        .encode_operand_high(
                                                            mir,
                                                            operand,
                                                            statement.source_info.span,
                                                        )
                                                        .with_span(statement.source_info.span)?;
                                                }
                                                _ => {
                                                    unimplemented!("rvalue: {:?}", rvalue);
                                                }
                                            }
                                        }
                                    }
                                    statement_index -= 1;
                                } else {
                                    unreachable!();
                                }
                            };
                            encoded_args.push(ArgKind::Place(place));
                        }
                        Ok(encoded_args)
                    }
                    fn extract_places<'p, 'v: 'p, 'tcx: 'v>(
                        mir: &mir::Body<'tcx>,
                        args: &[mir::Operand<'tcx>],
                        block: &mir::BasicBlockData<'tcx>,
                        encoder: &mut ProcedureEncoder<'p, 'v, 'tcx>,
                    ) -> SpannedEncodingResult<Vec<vir_high::Expression>> {
                        let places = extract_args(mir, args, block, encoder)?
                            .into_iter()
                            .map(|arg| match arg {
                                ArgKind::Place(place) => place,
                                ArgKind::String(_) => unreachable!(),
                            })
                            .collect();
                        Ok(places)
                    }
                    fn extract_place<'p, 'v: 'p, 'tcx: 'v>(
                        mir: &mir::Body<'tcx>,
                        args: &[mir::Operand<'tcx>],
                        block: &mir::BasicBlockData<'tcx>,
                        encoder: &mut ProcedureEncoder<'p, 'v, 'tcx>,
                    ) -> SpannedEncodingResult<vir_high::Expression> {
                        assert_eq!(args.len(), 1);
                        Ok(extract_places(mir, args, block, encoder)?.pop().unwrap())
                    }
                    match full_called_function_name.as_ref() {
                        "prusti_contracts::prusti_set_union_active_field" => {
                            assert_eq!(args.len(), 1);
                            // assert_eq!(args.len(), 1);
                            // let argument_place = if let mir::Operand::Move(place) = args[0] {
                            //     place
                            // } else {
                            //     unreachable!()
                            // };
                            // // Find the place whose address was stored in the argument by
                            // // iterating backwards through statements.
                            // let mut statement_index = block.statements.len() - 1;
                            // let union_variant_place = loop {
                            //     if let Some(statement) = block.statements.get(statement_index) {
                            //         if let mir::StatementKind::Assign(box (
                            //             target_place,
                            //             mir::Rvalue::AddressOf(_, union_variant_place),
                            //         )) = &statement.kind
                            //         {
                            //             if *target_place == argument_place {
                            //                 break union_variant_place;
                            //             }
                            //         }
                            //         statement_index -= 1;
                            //     } else {
                            //         unreachable!();
                            //     }
                            // };
                            // let encoded_variant_place =
                            //     self.encode_place(*union_variant_place, None)?;
                            let encoded_variant_place = extract_place(self.mir, args, block, self)?;
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
                        "prusti_contracts::prusti_manually_manage" => {
                            let encoded_place = extract_place(self.mir, args, block, self)?;
                            assert!(self.manually_managed_places.insert(encoded_place));
                            Ok(true)
                        }
                        "prusti_contracts::prusti_pack_place" => {
                            let encoded_place = extract_place(self.mir, args, block, self)?;
                            // let permission_amount =
                            //     self.lookup_opened_reference_place_permission(&encoded_place);
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::pack_no_pos(
                                    encoded_place,
                                    vir_high::PredicateKind::Owned,
                                    // permission_amount,
                                ),
                                span,
                                ErrorCtxt::Pack,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_unpack_place" => {
                            let encoded_place = extract_place(self.mir, args, block, self)?;
                            // let permission_amount =
                            //     self.lookup_opened_reference_place_permission(&encoded_place);
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::unpack_no_pos(
                                    encoded_place,
                                    vir_high::PredicateKind::Owned,
                                    // permission_amount,
                                ),
                                span,
                                ErrorCtxt::Unpack,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_obtain_place" => {
                            let encoded_place = extract_place(self.mir, args, block, self)?;
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::obtain_no_pos(
                                    encoded_place,
                                    vir_high::PredicateKind::Owned,
                                ),
                                span,
                                ErrorCtxt::Unpack,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_pack_ref_place" => {
                            assert_eq!(args.len(), 2);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::Place(place) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::String(lifetime_name) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            assert!(encoded_args.is_empty());
                            let lifetime = self
                                .user_named_lifetimes
                                .get(&lifetime_name)
                                .unwrap()
                                .clone();
                            // let permission_amount =
                            //     self.lookup_opened_reference_place_permission(&place);
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::pack_no_pos(
                                    place,
                                    vir_high::PredicateKind::frac_ref(lifetime),
                                    // permission_amount,
                                ),
                                span,
                                ErrorCtxt::Pack,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_unpack_ref_place" => {
                            assert_eq!(args.len(), 2);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::Place(place) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::String(lifetime_name) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            assert!(encoded_args.is_empty());
                            let lifetime = self
                                .user_named_lifetimes
                                .get(&lifetime_name)
                                .unwrap()
                                .clone();
                            // let encoded_place = extract_place(self.mir, args, block, self)?;
                            // let permission_amount =
                            //     self.lookup_opened_reference_place_permission(&place);
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::unpack_no_pos(
                                    place,
                                    vir_high::PredicateKind::frac_ref(lifetime),
                                    // permission_amount,
                                ),
                                span,
                                ErrorCtxt::Unpack,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_pack_mut_ref_place" => {
                            assert_eq!(args.len(), 2);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::Place(place) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::String(lifetime_name) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            assert!(encoded_args.is_empty());
                            let lifetime = self
                                .user_named_lifetimes
                                .get(&lifetime_name)
                                .unwrap()
                                .clone();
                            // let encoded_place = extract_place(self.mir, args, block, self)?;
                            // let permission_amount =
                            //     self.lookup_opened_reference_place_permission(&place);
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::pack_no_pos(
                                    place,
                                    vir_high::PredicateKind::unique_ref(lifetime),
                                    // permission_amount,
                                ),
                                span,
                                ErrorCtxt::Pack,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_unpack_mut_ref_place" => {
                            assert_eq!(args.len(), 2);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::Place(place) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::String(lifetime_name) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            assert!(encoded_args.is_empty());
                            let lifetime = self
                                .user_named_lifetimes
                                .get(&lifetime_name)
                                .unwrap()
                                .clone();
                            // let permission_amount =
                            //     self.lookup_opened_reference_place_permission(&place);
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::unpack_no_pos(
                                    place,
                                    vir_high::PredicateKind::unique_ref(lifetime),
                                    // permission_amount,
                                ),
                                span,
                                ErrorCtxt::Unpack,
                                self.def_id,
                            )?;
                            // let encoded_place = extract_place(self.mir, args, block, self)?;
                            // let statement = self.encoder.set_statement_error_ctxt(
                            //     vir_high::Statement::unpack_no_pos(
                            //         encoded_place,
                            //         vir_high::PredicateKind::UniqueRef,
                            //     ),
                            //     span,
                            //     ErrorCtxt::Unpack,
                            //     self.def_id,
                            // )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_take_lifetime" => {
                            assert_eq!(args.len(), 2);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::String(lifetime_name) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(place) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            assert!(encoded_args.is_empty());
                            let vir_high::ty::Type::Reference(ref_type) = place.get_type() else {
                                unimplemented!("FIXME: A proper error message.");
                            };
                            let lifetime = ref_type.lifetime.clone();
                            assert!(self
                                .user_named_lifetimes
                                .insert(lifetime_name, lifetime)
                                .is_none());
                            Ok(true)
                        }
                        "prusti_contracts::prusti_set_lifetime_for_raw_pointer_reference_casts" => {
                            assert_eq!(args.len(), 1);
                            // FIXME: Code is very similar to
                            // prusti-viper/src/encoder/mir/procedures/encoder/elaborate_drops/pointer_reborrow.rs.
                            let arg = &args[0];
                            let mut statement_index = block.statements.len() - 1;
                            let argument_place = if let mir::Operand::Move(place) = arg {
                                place
                            } else {
                                unreachable!()
                            };
                            let place = loop {
                                if let Some(statement) = block.statements.get(statement_index) {
                                    if let mir::StatementKind::Assign(box (target_place, rvalue)) =
                                        &statement.kind
                                    {
                                        if target_place == argument_place {
                                            match rvalue {
                                                mir::Rvalue::AddressOf(_, place) => {
                                                    break place;
                                                }
                                                _ => {
                                                    unimplemented!("rvalue: {:?}", rvalue);
                                                }
                                            }
                                        }
                                    }
                                    statement_index -= 1;
                                } else {
                                    unreachable!();
                                }
                            };
                            let ty::TyKind::Ref(reference_region, _, _) = place.ty(self.mir, self.encoder.env().tcx()).ty.kind() else {
                                unreachable!("place {place:?} must be a reference");
                            };
                            self.pointer_deref_lifetime = Some(*reference_region);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_join_place" => {
                            let encoded_place = extract_place(self.mir, args, block, self)?;
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::join_no_pos(encoded_place),
                                span,
                                ErrorCtxt::Pack,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_join_range" => {
                            assert_eq!(args.len(), 3);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::Place(end_index) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(start_index) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(pointer) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::join_range_no_pos(
                                    pointer,
                                    start_index,
                                    end_index,
                                ),
                                span,
                                ErrorCtxt::JoinRange,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_split_place" => {
                            let encoded_place = extract_place(self.mir, args, block, self)?;
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::split_no_pos(encoded_place),
                                span,
                                ErrorCtxt::Unpack,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_split_range" => {
                            assert_eq!(args.len(), 3);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::Place(end_index) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(start_index) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(pointer) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::split_range_no_pos(
                                    pointer,
                                    start_index,
                                    end_index,
                                ),
                                span,
                                ErrorCtxt::SplitRange,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_stash_range" => {
                            assert_eq!(args.len(), 4);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::String(stash_name) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(end_index) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(start_index) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(pointer) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            encoded_statements.push(vir_high::Statement::old_label(
                                stash_name.clone(),
                                self.encoder.register_error(
                                    span,
                                    ErrorCtxt::StashRange,
                                    self.def_id,
                                ),
                            ));
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::stash_range_no_pos(
                                    pointer.clone(),
                                    start_index.clone(),
                                    end_index.clone(),
                                    stash_name.clone(),
                                ),
                                span,
                                ErrorCtxt::StashRange,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            encoded_statements.push(vir_high::Statement::old_label(
                                format!("{stash_name}$post"),
                                self.encoder.register_error(
                                    span,
                                    ErrorCtxt::StashRange,
                                    self.def_id,
                                ),
                            ));
                            let position = pointer.position();
                            let pointer = vir_high::Expression::labelled_old(
                                stash_name.clone(),
                                pointer,
                                position,
                            );
                            assert!(self
                                .stashed_ranges
                                .insert(stash_name, (pointer, start_index, end_index))
                                .is_none());
                            Ok(true)
                        }
                        "prusti_contracts::prusti_restore_stash_range" => {
                            assert_eq!(args.len(), 3);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::String(stash_name) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(new_start_index) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(new_pointer) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let (old_pointer, old_start_index, old_end_index) =
                                self.stashed_ranges.get(&stash_name).unwrap().clone();
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::stash_range_restore_no_pos(
                                    old_pointer,
                                    old_start_index,
                                    old_end_index,
                                    stash_name,
                                    new_pointer,
                                    new_start_index,
                                ),
                                span,
                                ErrorCtxt::RestoreStashRange,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_close_ref_place" => {
                            assert_eq!(args.len(), 2);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::String(witness) = encoded_args.pop().unwrap() else {
                                unreachable!()
                            };
                            let ArgKind::String(place_spec_id) = encoded_args.pop().unwrap() else {
                                unreachable!()
                            };
                            let user_place = self
                                .specification_expressions
                                .get(&place_spec_id)
                                .expect("FIXME: A proper error message")
                                .clone();
                            let vir_high::Expression::AddrOf(vir_high::AddrOf { base: box user_place, .. }) =
                            user_place else {
                                    unreachable!("place: {user_place}");
                                };
                            assert!(encoded_args.is_empty());
                            // FIXME: These should actually remove the
                            // witnesses. However, since specification blocks
                            // are processed before all other blocks, the state
                            // cannot be easily transfered. A proper solution
                            // would be to check whether the state that uses the
                            // opened permission is dominated by the statement
                            // that opens the reference. Alternatively, we could
                            // have annotations that specify which permission
                            // amount to use for copy statements. Another
                            // alternative (probably the easiest) would be to
                            // make a static analysis that inserts the right
                            // permission amount into the copy statement.
                            //
                            // A proper solution probably would be to integrate
                            // this into fold-unfold algorithm.
                            let (place, lifetime) = self
                                .opened_reference_witnesses
                                .get(&witness)
                                .expect("FIXME: a proper error message");
                            assert_eq!(place, &user_place, "FIXME: a proper error message");
                            let variable = self
                                .opened_reference_place_permissions
                                .get(place)
                                .expect("FIXME: A proper error message");
                            // let deref_base = place.get_last_dereferenced_reference().cloned();
                            // let statement = self.encode_close_reference(
                            //     location,
                            //     &deref_base,
                            //     place.clone(),
                            //     variable.clone(),
                            // )?;
                            let statement = self.set_statement_error(
                                location,
                                ErrorCtxt::CloseFracRef,
                                vir_high::Statement::close_frac_ref_no_pos(
                                    lifetime.clone(),
                                    self.lifetime_token_fractional_permission(self.lifetime_count),
                                    place.clone(),
                                    variable.clone().unwrap(),
                                    true,
                                ),
                            )?;
                            encoded_statements.push(statement);
                            // encoded_statements.push(statement.expect(
                            //     "FIXME: A proper error message for closing not a reference",
                            // ));
                            Ok(true)
                        }
                        "prusti_contracts::prusti_open_ref_place" => {
                            assert_eq!(args.len(), 3);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::String(witness) = encoded_args.pop().unwrap() else {
                                unreachable!()
                            };
                            let ArgKind::String(place_spec_id) = encoded_args.pop().unwrap() else {
                                unreachable!()
                            };
                            let place = self
                                .specification_expressions
                                .get(&place_spec_id)
                                .unwrap()
                                .clone();
                            let vir_high::Expression::AddrOf(vir_high::AddrOf { base: box place, .. }) =
                                place else {
                                    unreachable!("place: {place}");
                                };
                            let ArgKind::String(lifetime_name) = encoded_args.pop().unwrap() else {
                                unreachable!()
                            };
                            place.check_no_erased_lifetime();
                            assert!(encoded_args.is_empty());
                            let Some(lifetime) = self
                                .user_named_lifetimes
                                .get(&lifetime_name)
                                .cloned() else {
                                    return Err(SpannedEncodingError::incorrect(
                                        format!("Lifetime name `{lifetime_name}` not defined"), span));
                                };
                            let permission = self
                                .fresh_ghost_variable("tmp_frac_ref_perm", vir_high::Type::MPerm);
                            let variable = Some(permission.clone());
                            let statement = self.set_statement_error(
                                location,
                                ErrorCtxt::OpenFracRef,
                                vir_high::Statement::open_frac_ref_no_pos(
                                    lifetime.clone(),
                                    permission,
                                    self.lifetime_token_fractional_permission(self.lifetime_count),
                                    place.clone(),
                                    true,
                                ),
                            )?;

                            // let deref_place = place.get_last_dereferenced_reference().cloned();
                            // let (variable, statement) =
                            //     self.encode_open_reference(location, &deref_place, place.clone())?;
                            encoded_statements.push(statement);
                            assert!(self
                                .opened_reference_place_permissions
                                .insert(place.clone(), variable)
                                .is_none());
                            assert!(self
                                .opened_reference_witnesses
                                .insert(witness, (place, lifetime))
                                .is_none());
                            Ok(true)
                        }
                        "prusti_contracts::prusti_close_mut_ref_place" => {
                            assert_eq!(args.len(), 2);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::String(witness) = encoded_args.pop().unwrap() else {
                                unreachable!()
                            };
                            let ArgKind::String(place_spec_id) = encoded_args.pop().unwrap() else {
                                unreachable!()
                            };
                            let user_place = self
                                .specification_expressions
                                .get(&place_spec_id)
                                .expect("FIXME: A proper error message")
                                .clone();
                            let vir_high::Expression::AddrOf(vir_high::AddrOf { base: box user_place, .. }) =
                            user_place else {
                                    unreachable!("place: {user_place}");
                                };
                            assert!(encoded_args.is_empty());
                            // FIXME: These should actually remove the
                            // witnesses. However, since specification blocks
                            // are processed before all other blocks, the state
                            // cannot be easily transfered. A proper solution
                            // would be to check whether the state that uses the
                            // opened permission is dominated by the statement
                            // that opens the reference. Alternatively, we could
                            // have annotations that specify which permission
                            // amount to use for copy statements. Another
                            // alternative (probably the easiest) would be to
                            // make a static analysis that inserts the right
                            // permission amount into the copy statement.
                            //
                            // A proper solution probably would be to integrate
                            // this into fold-unfold algorithm.
                            let (place, lifetime) = self
                                .opened_reference_witnesses
                                .get(&witness)
                                .expect("FIXME: a proper error message");
                            assert_eq!(place, &user_place, "FIXME: a proper error message");
                            // let variable = self
                            //     .opened_reference_place_permissions
                            //     .get(&place)
                            //     .expect("FIXME: A proper error message");
                            // let deref_base = place.get_last_dereferenced_reference().cloned();
                            let statement = self.set_statement_error(
                                location,
                                ErrorCtxt::CloseMutRef,
                                vir_high::Statement::close_mut_ref_no_pos(
                                    lifetime.clone(),
                                    self.lifetime_token_fractional_permission(self.lifetime_count),
                                    place.clone(),
                                    true,
                                ),
                            )?;
                            // let statement = self.encode_close_reference(
                            //     location,
                            //     &deref_base,
                            //     place.clone(),
                            //     variable.clone(),
                            // )?;
                            // encoded_statements.push(statement.expect(
                            //     "FIXME: A proper error message for closing not a reference",
                            // ));
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_open_mut_ref_place" => {
                            assert_eq!(args.len(), 3);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::String(witness) = encoded_args.pop().unwrap() else {
                                unreachable!()
                            };
                            let ArgKind::String(place_spec_id) = encoded_args.pop().unwrap() else {
                                unreachable!()
                            };
                            let place = self
                                .specification_expressions
                                .get(&place_spec_id)
                                .unwrap()
                                .clone();
                            let vir_high::Expression::AddrOf(vir_high::AddrOf { base: box place, .. }) =
                                place else {
                                    unreachable!("place: {place}");
                                };
                            let ArgKind::String(lifetime_name) = encoded_args.pop().unwrap() else {
                                unreachable!()
                            };
                            place.check_no_erased_lifetime();
                            assert!(encoded_args.is_empty());
                            // let lifetime = self
                            //     .user_named_lifetimes
                            //     .get(&lifetime_name)
                            //     .unwrap()
                            //     .clone();
                            let Some(lifetime) = self
                                .user_named_lifetimes
                                .get(&lifetime_name)
                                .cloned() else {
                                    return Err(SpannedEncodingError::incorrect(
                                        format!("Lifetime name `{lifetime_name}` not defined"), span));
                                };
                            let statement = self.set_statement_error(
                                location,
                                ErrorCtxt::OpenMutRef,
                                vir_high::Statement::open_mut_ref_no_pos(
                                    lifetime.clone(),
                                    self.lifetime_token_fractional_permission(self.lifetime_count),
                                    place.clone(),
                                    true,
                                ),
                            )?;
                            encoded_statements.push(statement);
                            assert!(self
                                .opened_reference_place_permissions
                                .insert(place.clone(), None)
                                .is_none());
                            assert!(self
                                .opened_reference_witnesses
                                .insert(witness, (place, lifetime))
                                .is_none());
                            Ok(true)
                        }
                        "prusti_contracts::prusti_resolve" => {
                            assert_eq!(args.len(), 1);
                            let encoded_place = extract_place(self.mir, args, block, self)?;
                            let statement = self.set_statement_error(
                                location,
                                ErrorCtxt::Resolve,
                                vir_high::Statement::dead_reference_no_pos(encoded_place, None),
                            )?;
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_resolve_range" => {
                            assert_eq!(args.len(), 6);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::Place(end_index) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(start_index) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(predicate_range_end_index) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(predicate_range_start_index) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(pointer) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::String(lifetime_name) = encoded_args.pop().unwrap() else {
                                unreachable!()
                            };
                            let Some(lifetime) = self
                                .user_named_lifetimes
                                .get(&lifetime_name)
                                .cloned() else {
                                    return Err(SpannedEncodingError::incorrect(
                                        format!("Lifetime name `{lifetime_name}` not defined"), span));
                                };
                            let statement = self.set_statement_error(
                                location,
                                ErrorCtxt::Resolve,
                                vir_high::Statement::dead_reference_range_no_pos(
                                    lifetime,
                                    vir_high::ty::Uniqueness::Unique,
                                    pointer,
                                    predicate_range_start_index,
                                    predicate_range_end_index,
                                    start_index,
                                    end_index,
                                ),
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_forget_initialization" => {
                            let encoded_place = extract_place(self.mir, args, block, self)?;
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::forget_initialization_no_pos(encoded_place),
                                span,
                                ErrorCtxt::ForgetInitialization,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_forget_initialization_range" => {
                            assert_eq!(args.len(), 3);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::Place(end_index) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(start_index) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let ArgKind::Place(pointer) = encoded_args.pop().unwrap() else {
                                unreachable!("Wrong function parameters?");
                            };
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::forget_initialization_range_no_pos(
                                    pointer,
                                    start_index,
                                    end_index,
                                ),
                                span,
                                ErrorCtxt::ForgetInitialization,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_on_drop_unwind" => {
                            let encoded_place = extract_place(self.mir, args, block, self)?;
                            let Some(region_entry_block) = region_entry_block else {
                                unreachable!()
                            };
                            assert!(self
                                .specification_on_drop_unwind
                                .insert(encoded_place, region_entry_block)
                                .is_none());
                            Ok(true)
                        }
                        "prusti_contracts::prusti_restore_place" => {
                            assert_eq!(args.len(), 2);
                            let mut encoded_places = extract_places(self.mir, args, block, self)?;
                            let restored_place = encoded_places.pop().unwrap();
                            let borrowing_place = encoded_places.pop().unwrap();
                            let statement = self.encoder.set_statement_error_ctxt(
                                vir_high::Statement::restore_raw_borrowed_no_pos(
                                    borrowing_place,
                                    restored_place,
                                ),
                                span,
                                ErrorCtxt::RestoreRawBorrowed,
                                self.def_id,
                            )?;
                            statement.check_no_default_position();
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        "prusti_contracts::prusti_materialize_predicate"
                        | "prusti_contracts::prusti_quantified_predicate" => {
                            assert_eq!(args.len(), 1);
                            let mut encoded_args = extract_args(self.mir, args, block, self)?;
                            let ArgKind::String(predicate_spec_id) = encoded_args.pop().unwrap() else {
                                unreachable!()
                            };
                            let predicate_expression = self
                                .specification_expressions
                                .get(&predicate_spec_id)
                                .expect("FIXME: A proper error message")
                                .clone();
                            let predicate_expression =
                                self.resolve_lifetimes(predicate_expression)?;
                            assert!(encoded_args.is_empty());
                            let vir_high::Expression::AccPredicate(acc_predicate) = predicate_expression else {
                                unimplemented!("FIXME: A proper error message")
                            };
                            let predicate = *acc_predicate.predicate;
                            let check_that_exists = match full_called_function_name.as_ref() {
                                "prusti_contracts::prusti_materialize_predicate" => true,
                                "prusti_contracts::prusti_quantified_predicate" => false,
                                _ => unreachable!(),
                            };
                            let statement = self.set_statement_error(
                                location,
                                ErrorCtxt::MaterializePredicate,
                                vir_high::Statement::materialize_predicate_no_pos(
                                    predicate,
                                    check_that_exists,
                                ),
                            )?;
                            encoded_statements.push(statement);
                            Ok(true)
                        }
                        function_name => unreachable!("function: {}", function_name),
                    }
                } else {
                    unreachable!();
                }
            }
            mir::TerminatorKind::SwitchInt { .. } | mir::TerminatorKind::Goto { .. }
                if region_entry_block.is_some() =>
            {
                // Ignored when encoding a specification region.
                Ok(true)
            }
            _ => unreachable!("terminator {:?} at {:?} ", terminator_kind, bb),
        }
    }

    // fn is_pure(&self, def_id: DefId, substs: Option<SubstsRef<'tcx>>) -> bool {
    //     self.encoder.is_pure(def_id, substs)
    //     //  || {
    //     //     // FIXME: We do this because extern specs do not support primitive
    //     //     // types.
    //     //     let func_name = self.encoder.env().name.get_unique_item_name(def_id);
    //     //     func_name.starts_with("std::ptr::mut_ptr::<impl *mut T>::is_null")
    //     //     || func_name.starts_with("core::std::ptr::mut_ptr::<impl *mut T>::is_null")
    //     // }
    // }
}
