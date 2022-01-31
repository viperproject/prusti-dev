use super::MirProcedureEncoderInterface;
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingError, SpannedEncodingResult, WithSpan},
    mir::{
        constants::ConstantsEncoderInterface, errors::ErrorInterface,
        places::PlacesEncoderInterface, predicates::MirPredicateEncoderInterface,
        spans::SpanInterface, types::MirTypeEncoderInterface,
    },
    Encoder,
};
use prusti_interface::environment::{mir_dump::lifetimes::Lifetimes, Procedure};
use rustc_data_structures::graph::WithStartNode;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use vir_crate::high::{
    self as vir_high,
    builders::procedure::{BasicBlockBuilder, ProcedureBuilder},
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
    };
    procedure_encoder.encode()
}

struct ProcedureEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p mut Encoder<'v, 'tcx>,
    def_id: DefId,
    _procedure: &'p Procedure<'tcx>,
    mir: &'p mir::Body<'tcx>,
    _lifetimes: Lifetimes,
}

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    fn encode(&mut self) -> SpannedEncodingResult<vir_high::ProcedureDecl> {
        let name = self.encoder.encode_item_name(self.def_id);
        let parameters = self.encode_parameters()?;
        let returns = self.encode_returns()?;
        let mut procedure_builder = ProcedureBuilder::new(name, parameters, returns);
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

    fn encode_parameters(&mut self) -> SpannedEncodingResult<Vec<vir_high::expression::Local>> {
        let mut parameters = Vec::new();
        for mir_arg in self.mir.args_iter() {
            parameters.push(self.encode_local(mir_arg)?);
        }
        Ok(parameters)
    }

    fn encode_returns(&mut self) -> SpannedEncodingResult<Vec<vir_high::expression::Local>> {
        let returns = vec![self.encode_local(mir::RETURN_PLACE)?];
        Ok(returns)
    }

    fn encode_body(
        &mut self,
        procedure_builder: &mut ProcedureBuilder,
    ) -> SpannedEncodingResult<()> {
        let entry_label = vir_high::BasicBlockId::new("label_entry".to_string());
        let mut block_builder = procedure_builder.create_basic_block_builder(entry_label.clone());
        if self.mir.basic_blocks().is_empty() {
            block_builder.set_successor(vir_high::Successor::Return);
        } else {
            block_builder.set_successor(vir_high::Successor::Goto(
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
            self.encode_terminator(&mut block_builder, bb, terminator)?;
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

    fn encode_terminator(
        &self,
        block_builder: &mut BasicBlockBuilder,
        _bb: mir::BasicBlock,
        terminator: &mir::Terminator<'tcx>,
    ) -> SpannedEncodingResult<()> {
        use rustc_middle::mir::TerminatorKind;
        let successor = match &terminator.kind {
            TerminatorKind::Goto { target } => {
                vir_high::Successor::Goto(self.encode_basic_block_label(*target))
            }
            TerminatorKind::SwitchInt { targets, .. } => {
                let successors = targets
                    .iter()
                    .map(|(_, target)| (true.into(), self.encode_basic_block_label(target)))
                    .collect();
                vir_high::Successor::GotoSwitch(successors)
            }
            // TerminatorKind::Resume => {
            //     graph.add_exit_edge(bb, "resume");
            // }
            // TerminatorKind::Abort => {
            //     graph.add_exit_edge(bb, "abort");
            // }
            TerminatorKind::Return => vir_high::Successor::Return,
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
            // TerminatorKind::Call {
            //     ref destination,
            //     cleanup,
            //     ..
            // } => {
            //     if let Some((_, target)) = destination {
            //         graph.add_regular_edge(bb, target);
            //     }
            //     if let Some(target) = cleanup {
            //         graph.add_unwind_edge(bb, target);
            //     }
            // }
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

    fn encode_basic_block_label(&self, bb: mir::BasicBlock) -> vir_high::BasicBlockId {
        vir_high::BasicBlockId::new(format!("label_{:?}", bb))
    }

    fn register_error(&self, location: mir::Location, error_ctxt: ErrorCtxt) -> vir_high::Position {
        let span = self.encoder.get_mir_location_span(self.mir, location);
        self.encoder
            .error_manager()
            .register(span, error_ctxt, self.def_id)
            .into()
    }
}
