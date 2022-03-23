use super::MirProcedureEncoderInterface;
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingError, SpannedEncodingResult, WithSpan},
    mir::{
        casts::CastsEncoderInterface, constants::ConstantsEncoderInterface, errors::ErrorInterface,
        panics::MirPanicsEncoderInterface, places::PlacesEncoderInterface,
        predicates::MirPredicateEncoderInterface, spans::SpanInterface,
        type_layouts::MirTypeLayoutsEncoderInterface, types::MirTypeEncoderInterface,
    },
    Encoder,
};
use log::debug;
use prusti_common::config;
use prusti_interface::environment::{mir_dump::lifetimes::Lifetimes, Procedure};
use rustc_data_structures::graph::WithStartNode;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty};
use rustc_span::Span;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, UnaryOperationHelpers},
    high::{
        self as vir_high,
        builders::procedure::{
            BasicBlockBuilder, ProcedureBuilder, SuccessorBuilder, SuccessorExitKind,
        },
    },
};

pub(super) fn encode_procedure<'v, 'tcx: 'v>(
    encoder: &mut Encoder<'v, 'tcx>,
    def_id: DefId,
) -> SpannedEncodingResult<vir_high::ProcedureDecl> {
    let procedure = Procedure::new(encoder.env(), def_id);
    let lifetimes = if let Some(facts) = encoder
        .env()
        .try_get_local_mir_borrowck_facts(def_id.expect_local())
    {
        Lifetimes::new(facts)
    } else {
        return Err(SpannedEncodingError::internal(
            format!("failed to obtain borrow information for {:?}", def_id),
            procedure.get_span(),
        ));
    };
    let mut procedure_encoder = ProcedureEncoder {
        encoder,
        def_id,
        _procedure: &procedure,
        mir: procedure.get_mir(),
        _lifetimes: lifetimes,
        check_panics: config::check_panics(),
    };
    procedure_encoder.encode()
}

struct ProcedureEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p mut Encoder<'v, 'tcx>,
    def_id: DefId,
    _procedure: &'p Procedure<'tcx>,
    mir: &'p mir::Body<'tcx>,
    _lifetimes: Lifetimes,
    check_panics: bool,
}

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    fn encode(&mut self) -> SpannedEncodingResult<vir_high::ProcedureDecl> {
        let name = self.encoder.encode_item_name(self.def_id);
        let (allocate_parameters, deallocate_parameters) = self.encode_parameters()?;
        let (allocate_returns, deallocate_returns) = self.encode_returns()?;
        let mut procedure_builder = ProcedureBuilder::new(
            name,
            allocate_parameters,
            allocate_returns,
            deallocate_parameters,
            deallocate_returns,
        );
        self.encode_body(&mut procedure_builder)?;
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
        Ok(vir_high::expression::Local::new_with_pos(
            variable, position,
        ))
    }

    fn encode_parameters(
        &mut self,
    ) -> SpannedEncodingResult<(Vec<vir_high::Statement>, Vec<vir_high::Statement>)> {
        let mut allocation = Vec::new();
        let mut deallocation = Vec::new();
        for mir_arg in self.mir.args_iter() {
            let parameter = self.encode_local(mir_arg)?;
            let alloc_statement = vir_high::Statement::inhale_no_pos(
                vir_high::Predicate::owned_non_aliased_no_pos(parameter.clone().into()),
            )
            .set_default_position(
                self.encoder
                    .change_error_context(parameter.position, ErrorCtxt::UnexpectedStorageLive),
            );
            allocation.push(alloc_statement);
            let mir_type = self.encoder.get_local_type(self.mir, mir_arg)?;
            let size = self.encoder.encode_type_size_expression(mir_type)?;
            let dealloc_statement = vir_high::Statement::exhale_no_pos(
                vir_high::Predicate::memory_block_stack_no_pos(parameter.clone().into(), size),
            )
            .set_default_position(
                self.encoder
                    .change_error_context(parameter.position, ErrorCtxt::UnexpectedStorageDead),
            );
            deallocation.push(dealloc_statement);
        }
        Ok((allocation, deallocation))
    }

    fn encode_returns(
        &mut self,
    ) -> SpannedEncodingResult<(Vec<vir_high::Statement>, Vec<vir_high::Statement>)> {
        let return_local = self.encode_local(mir::RETURN_PLACE)?;
        let mir_type = self.encoder.get_local_type(self.mir, mir::RETURN_PLACE)?;
        let size = self.encoder.encode_type_size_expression(mir_type)?;
        let alloc_statement = vir_high::Statement::inhale_no_pos(
            vir_high::Predicate::memory_block_stack_no_pos(return_local.clone().into(), size),
        )
        .set_default_position(
            self.encoder
                .change_error_context(return_local.position, ErrorCtxt::UnexpectedStorageLive),
        );
        let dealloc_statement = vir_high::Statement::exhale_no_pos(
            vir_high::Predicate::owned_non_aliased_no_pos(return_local.clone().into()),
        )
        .set_default_position(
            self.encoder
                .change_error_context(return_local.position, ErrorCtxt::UnexpectedStorageDead),
        );
        Ok((vec![alloc_statement], vec![dealloc_statement]))
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
                self.encode_basic_block_label(self.mir.start_node()),
            ));
        }
        block_builder.build();
        procedure_builder.set_entry(entry_label);
        for bb in self.mir.basic_blocks().indices() {
            self.encode_basic_block(procedure_builder, bb)?;
        }
        Ok(())
    }

    fn encode_basic_block(
        &mut self,
        procedure_builder: &mut ProcedureBuilder,
        bb: mir::BasicBlock,
    ) -> SpannedEncodingResult<()> {
        let label = self.encode_basic_block_label(bb);
        let mut block_builder = procedure_builder.create_basic_block_builder(label);
        let mir::BasicBlockData {
            statements,
            terminator,
            ..
        } = &self.mir[bb];
        let mut location = mir::Location {
            block: bb,
            statement_index: 0,
        };
        let terminator_index = statements.len();
        while location.statement_index < terminator_index {
            self.encode_statement(
                &mut block_builder,
                location,
                &statements[location.statement_index],
            )?;
            location.statement_index += 1;
        }
        if let Some(terminator) = terminator {
            self.encode_terminator(&mut block_builder, location, terminator)?;
        }
        block_builder.build();
        Ok(())
    }

    fn encode_statement(
        &self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        statement: &mir::Statement<'tcx>,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_comment(format!("{:?} {:?}", location, statement));
        match &statement.kind {
            mir::StatementKind::StorageLive(local) => {
                let memory_block = self
                    .encoder
                    .encode_memory_block_for_local(self.mir, *local)?;
                block_builder.add_statement(vir_high::Statement::inhale(
                    memory_block,
                    self.register_error(location, ErrorCtxt::UnexpectedStorageLive),
                ));
                let memory_block_drop = self
                    .encoder
                    .encode_memory_block_drop_for_local(self.mir, *local)?;
                block_builder.add_statement(vir_high::Statement::inhale(
                    memory_block_drop,
                    self.register_error(location, ErrorCtxt::UnexpectedStorageLive),
                ));
            }
            mir::StatementKind::StorageDead(local) => {
                let memory_block = self
                    .encoder
                    .encode_memory_block_for_local(self.mir, *local)?;
                block_builder.add_statement(vir_high::Statement::exhale(
                    memory_block,
                    self.register_error(location, ErrorCtxt::UnexpectedStorageDead),
                ));
                let memory_block_drop = self
                    .encoder
                    .encode_memory_block_drop_for_local(self.mir, *local)?;
                block_builder.add_statement(vir_high::Statement::exhale(
                    memory_block_drop,
                    self.register_error(location, ErrorCtxt::UnexpectedStorageDead),
                ));
            }
            mir::StatementKind::Assign(box (target, source)) => {
                let encoded_target = self.encoder.encode_place_high(self.mir, *target)?;
                self.encode_statement_assign(block_builder, location, encoded_target, source)?;
            }
            _ => {
                block_builder.add_comment("encode_statement: not encoded".to_string());
            }
        }
        Ok(())
    }

    fn encode_statement_assign(
        &self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        encoded_target: vir_crate::high::Expression,
        source: &mir::Rvalue<'tcx>,
    ) -> SpannedEncodingResult<()> {
        match source {
            mir::Rvalue::Use(operand) => {
                self.encode_assign_operand(block_builder, location, encoded_target, operand)?;
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
            mir::Rvalue::UnaryOp(op, operand) => {
                let encoded_operand = self.encode_statement_operand(location, operand)?;
                let kind = match op {
                    mir::UnOp::Not => vir_high::UnaryOpKind::Not,
                    mir::UnOp::Neg => vir_high::UnaryOpKind::Minus,
                };
                let encoded_rvalue = vir_high::Rvalue::unary_op(kind, encoded_operand);
                block_builder.add_statement(vir_high::Statement::assign(
                    encoded_target,
                    encoded_rvalue,
                    self.register_error(location, ErrorCtxt::Assign),
                ));
            }
            _ => {
                block_builder.add_comment("encode_statement_assign: not encoded".to_string());
                unimplemented!("{:?}", source);
            }
        }
        Ok(())
    }

    fn encode_statement_assign_aggregate(
        &self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        encoded_target: vir_crate::high::Expression,
        aggregate_kind: &mir::AggregateKind<'tcx>,
        operands: &[mir::Operand<'tcx>],
    ) -> SpannedEncodingResult<()> {
        let span = self.encoder.get_span_of_location(self.mir, location);
        match aggregate_kind {
            mir::AggregateKind::Adt(adt_did, variant_index, substs, _, active_field_index) => {
                let adt_def = self.encoder.env().tcx().adt_def(*adt_did);
                assert!(
                    active_field_index.is_none(),
                    "field index should be set only for unions"
                );
                assert_eq!(variant_index.index(), 0, "variant for structs should be 0");
                let encoded_adt_def = self.encoder.encode_adt_def(adt_def, substs, None)?;
                match encoded_adt_def {
                    vir_high::TypeDecl::Struct(decl) => {
                        assert_eq!(decl.fields.len(), operands.len());
                        for (field, operand) in decl.fields.into_iter().zip(operands.iter()) {
                            let encoded_target_with_field =
                                encoded_target.clone().field_no_pos(field);
                            self.encode_assign_operand(
                                block_builder,
                                location,
                                encoded_target_with_field,
                                operand,
                            )?;
                        }
                    }
                    vir_high::TypeDecl::Enum(_decl) => {
                        unimplemented!();
                    }
                    _ => {
                        return Err(SpannedEncodingError::internal(
                            format!("expected adt, got: {:?}", adt_def),
                            span,
                        ));
                    }
                }
            }
            _ => {
                block_builder
                    .add_comment("encode_statement_assign_aggregate: not encoded".to_string());
            }
        }
        Ok(())
    }

    fn encode_assign_operand(
        &self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        encoded_target: vir_crate::high::Expression,
        operand: &mir::Operand<'tcx>,
    ) -> SpannedEncodingResult<()> {
        let span = self.encoder.get_span_of_location(self.mir, location);
        match operand {
            mir::Operand::Move(source) => {
                let encoded_source = self.encoder.encode_place_high(self.mir, *source)?;
                block_builder.add_statement(vir_high::Statement::move_place(
                    encoded_target,
                    encoded_source,
                    self.register_error(location, ErrorCtxt::MovePlace),
                ));
            }
            mir::Operand::Copy(source) => {
                let encoded_source = self.encoder.encode_place_high(self.mir, *source)?;
                block_builder.add_statement(vir_high::Statement::copy_place(
                    encoded_target,
                    encoded_source,
                    self.register_error(location, ErrorCtxt::CopyPlace),
                ));
            }
            mir::Operand::Constant(constant) => {
                let encoded_constant = self
                    .encoder
                    .encode_constant_high(constant)
                    .with_span(span)?;
                block_builder.add_statement(vir_high::Statement::write_place(
                    encoded_target,
                    encoded_constant,
                    self.register_error(location, ErrorCtxt::WritePlace),
                ));
            }
        }
        Ok(())
    }

    fn encode_statement_operand(
        &self,
        location: mir::Location,
        operand: &mir::Operand<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Operand> {
        let span = self.encoder.get_span_of_location(self.mir, location);
        let encoded_operand = match operand {
            mir::Operand::Move(source) => {
                let encoded_source = self.encoder.encode_place_high(self.mir, *source)?;
                vir_high::Operand::new(vir_high::OperandKind::Move, encoded_source)
            }
            mir::Operand::Copy(source) => {
                let encoded_source = self.encoder.encode_place_high(self.mir, *source)?;
                vir_high::Operand::new(vir_high::OperandKind::Copy, encoded_source)
            }
            mir::Operand::Constant(constant) => {
                let encoded_constant = self
                    .encoder
                    .encode_constant_high(constant)
                    .with_span(span)?;
                vir_high::Operand::new(vir_high::OperandKind::Constant, encoded_constant)
            }
        };
        Ok(encoded_operand)
    }

    fn encode_terminator(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        terminator: &mir::Terminator<'tcx>,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_comment(format!("{:?} {:?}", location, terminator.kind));
        let span = self.encoder.get_span_of_location(self.mir, location);
        use rustc_middle::mir::TerminatorKind;
        let successor = match &terminator.kind {
            TerminatorKind::Goto { target } => SuccessorBuilder::jump(vir_high::Successor::Goto(
                self.encode_basic_block_label(*target),
            )),
            TerminatorKind::SwitchInt {
                targets,
                discr,
                switch_ty,
            } => self.encode_terminator_switch_int(span, targets, discr, *switch_ty)?,
            TerminatorKind::Resume => SuccessorBuilder::exit_resume_panic(),
            // TerminatorKind::Abort => {
            //     graph.add_exit_edge(bb, "abort");
            // }
            TerminatorKind::Return => SuccessorBuilder::exit_return(),
            // TerminatorKind::Unreachable => {
            //     graph.add_exit_edge(bb, "unreachable");
            // }
            // TerminatorKind::DropAndReplace { target, unwind, .. }
            // | TerminatorKind::Drop { target, unwind, .. } => {
            //     graph.add_regular_edge(bb, target);
            //     if let Some(target) = unwind {
            //         graph.add_unwind_edge(bb, target);
            //     }
            // }
            TerminatorKind::Call {
                func: mir::Operand::Constant(box mir::Constant { literal, .. }),
                args,
                destination,
                cleanup,
                fn_span,
                from_hir_call: _,
            } => self.encode_terminator_call(
                block_builder,
                span,
                literal.ty(),
                args,
                destination,
                cleanup,
                *fn_span,
            )?,
            // TerminatorKind::Assert {
            //     target, cleanup, ..
            // } => {
            //     graph.add_regular_edge(bb, target);
            //     if let Some(target) = cleanup {
            //         graph.add_unwind_edge(bb, target);
            //     }
            // }
            // TerminatorKind::Yield { .. } => {
            //     graph.add_exit_edge(bb, "yield");
            // }
            // TerminatorKind::GeneratorDrop => {
            //     graph.add_exit_edge(bb, "generator_drop");
            // }
            // TerminatorKind::FalseEdge {
            //     real_target,
            //     imaginary_target,
            // } => {
            //     graph.add_regular_edge(bb, real_target);
            //     graph.add_imaginary_edge(bb, imaginary_target);
            // }
            // TerminatorKind::FalseUnwind {
            //     real_target,
            //     unwind,
            // } => {
            //     graph.add_regular_edge(bb, real_target);
            //     if let Some(imaginary_target) = unwind {
            //         graph.add_imaginary_edge(bb, imaginary_target);
            //     }
            // }
            // TerminatorKind::InlineAsm { .. } => {
            //     graph.add_exit_edge(bb, "inline_asm");
            // }
            x => unimplemented!("terminator: {:?}", x),
        };
        block_builder.set_successor(successor);
        Ok(())
    }

    fn encode_terminator_switch_int(
        &self,
        span: Span,
        targets: &mir::SwitchTargets,
        discr: &mir::Operand<'tcx>,
        switch_ty: ty::Ty<'tcx>,
    ) -> SpannedEncodingResult<SuccessorBuilder> {
        let discriminant = self
            .encoder
            .encode_operand_high(self.mir, discr)
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
            successors.push((encoded_condition, encoded_target));
        }
        successors.push((
            true.into(),
            self.encode_basic_block_label(targets.otherwise()),
        ));
        Ok(SuccessorBuilder::jump(vir_high::Successor::GotoSwitch(
            successors,
        )))
    }

    #[allow(clippy::too_many_arguments)]
    fn encode_terminator_call(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        span: Span,
        ty: ty::Ty<'tcx>,
        args: &[mir::Operand<'tcx>],
        destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        cleanup: &Option<mir::BasicBlock>,
        _fn_span: Span,
    ) -> SpannedEncodingResult<SuccessorBuilder> {
        let successor = if let ty::TyKind::FnDef(def_id, _substs) = ty.kind() {
            let full_called_function_name = self.encoder.env().tcx().def_path_str(*def_id);
            if !self.try_encode_builtin_call(
                block_builder,
                span,
                &full_called_function_name,
                args,
                destination,
                cleanup,
            )? {
                unimplemented!("Regular call implementation")
            }
            if let Some(destination) = destination {
                unimplemented!("destination: {:?}", destination);
            }
            if let Some(cleanup) = cleanup {
                SuccessorBuilder::jump(vir_high::Successor::Goto(
                    self.encode_basic_block_label(*cleanup),
                ))
            } else {
                unimplemented!();
            }
        } else {
            unimplemented!();
        };
        Ok(successor)
    }

    fn try_encode_builtin_call(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        span: Span,
        called_function: &str,
        args: &[mir::Operand<'tcx>],
        _destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>, // FIXME: Encode panic paths.
        _cleanup: &Option<mir::BasicBlock>,                         // FIXME: Encode panic paths.
    ) -> SpannedEncodingResult<bool> {
        match called_function {
            "core::panicking::panic" => {
                let panic_message = format!("{:?}", args[0]);
                let panic_cause = self.encoder.encode_panic_cause(span)?;
                let position =
                    self.encoder
                        .register_error(span, ErrorCtxt::Panic(panic_cause), self.def_id);
                if self.check_panics {
                    block_builder.add_comment(format!("Rust panic - {}", panic_message));
                    block_builder
                        .add_statement(vir_high::Statement::assert(false.into(), position));
                } else {
                    debug!("Absence of panic will not be checked")
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn encode_basic_block_label(&self, bb: mir::BasicBlock) -> vir_high::BasicBlockId {
        vir_high::BasicBlockId::new(format!("label_{:?}", bb))
    }

    fn register_error(&self, location: mir::Location, error_ctxt: ErrorCtxt) -> vir_high::Position {
        let span = self.encoder.get_mir_location_span(self.mir, location);
        self.encoder
            .error_manager()
            .register_error(span, error_ctxt, self.def_id)
            .into()
    }
}
