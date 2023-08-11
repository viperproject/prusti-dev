use super::*;

pub(super) trait BuiltinFuncAppEncoder<'p, 'v, 'tcx> {
    #[allow(clippy::too_many_arguments)]
    fn try_encode_builtin_call(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        span: Span,
        called_def_id: DefId,
        call_substs: GenericArgsRef<'tcx>,
        args: &[mir::Operand<'tcx>],
        destination: mir::Place<'tcx>,
        target: &Option<mir::BasicBlock>,
        unwind: mir::UnwindAction,
    ) -> SpannedEncodingResult<bool>;
}

impl<'p, 'v, 'tcx> BuiltinFuncAppEncoder<'p, 'v, 'tcx> for super::ProcedureEncoder<'p, 'v, 'tcx> {
    #[tracing::instrument(level = "debug", skip_all, fields(called_def_id = ?called_def_id))]
    fn try_encode_builtin_call(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        span: Span,
        called_def_id: DefId,
        call_substs: GenericArgsRef<'tcx>,
        args: &[mir::Operand<'tcx>],
        destination: mir::Place<'tcx>,
        target: &Option<mir::BasicBlock>,
        unwind: mir::UnwindAction,
    ) -> SpannedEncodingResult<bool> {
        let full_called_function_name = self
            .encoder
            .env()
            .name
            .get_absolute_item_name(called_def_id);

        let make_manual_assign =
            |encoder: &mut Self,
             block_builder: &mut BasicBlockBuilder,
             rhs_gen: &mut dyn FnMut(_, Vec<vir_high::Expression>, _) -> vir_high::Expression|
             -> SpannedEncodingResult<()> {
                let (target_place, target_block) = (destination, target.unwrap());
                let position = encoder
                    .encoder
                    .error_manager()
                    .register_error(span, ErrorCtxt::WritePlace, encoder.def_id)
                    .into();
                let encoded_target_place = encoder
                    .encoder
                    .encode_place_high(encoder.mir, target_place, None)?
                    .set_default_position(position);
                let encoded_args = args
                    .iter()
                    .map(|arg| encoder.encode_statement_operand(location, arg))
                    .collect::<Result<Vec<_>, _>>()?;
                for encoded_arg in encoded_args.iter() {
                    let statement = vir_high::Statement::consume_no_pos(encoded_arg.clone());
                    block_builder.add_statement(encoder.encoder.set_statement_error_ctxt(
                        statement,
                        span,
                        ErrorCtxt::ProcedureCall,
                        encoder.def_id,
                    )?);
                }
                let target_place_local = if let Some(target_place_local) = target_place.as_local() {
                    target_place_local
                } else {
                    unimplemented!()
                };
                let size = encoder.encoder.encode_type_size_expression(
                    encoder
                        .encoder
                        .get_local_type(encoder.mir, target_place_local)?,
                )?;
                let target_memory_block = vir_high::Predicate::memory_block_stack_no_pos(
                    encoded_target_place.clone(),
                    size,
                );
                block_builder.add_statement(encoder.encoder.set_statement_error_ctxt(
                    vir_high::Statement::exhale_no_pos(target_memory_block),
                    span,
                    ErrorCtxt::ProcedureCall,
                    encoder.def_id,
                )?);
                let inhale_statement = vir_high::Statement::inhale_no_pos(
                    vir_high::Predicate::owned_non_aliased_no_pos(encoded_target_place.clone()),
                );
                block_builder.add_statement(encoder.encoder.set_statement_error_ctxt(
                    inhale_statement,
                    span,
                    ErrorCtxt::ProcedureCall,
                    encoder.def_id,
                )?);
                let type_arguments = encoder
                    .encoder
                    .encode_generic_arguments_high(called_def_id, call_substs)
                    .with_span(span)?;

                let encoded_arg_expressions =
                    encoded_args.into_iter().map(|arg| arg.expression).collect();

                let target_type = encoded_target_place.get_type().clone();

                let expression = vir_high::Expression::equals(
                    encoded_target_place,
                    rhs_gen(type_arguments, encoded_arg_expressions, target_type),
                );
                let assume_statement = encoder.encoder.set_statement_error_ctxt(
                    vir_high::Statement::assume_no_pos(expression),
                    span,
                    ErrorCtxt::UnexpectedAssumeMethodPostcondition,
                    encoder.def_id,
                )?;
                block_builder.add_statement(encoder.encoder.set_statement_error_ctxt(
                    assume_statement,
                    span,
                    ErrorCtxt::ProcedureCall,
                    encoder.def_id,
                )?);
                encoder.encode_lft_for_block(target_block, location, block_builder)?;
                let target_label = encoder.encode_basic_block_label(target_block);
                let successor = vir_high::Successor::Goto(target_label);
                block_builder.set_successor_jump(successor);
                Ok(())
            };

        let make_builtin_call = |encoder: &mut Self,
                                 block_builder: &mut BasicBlockBuilder,
                                 function|
         -> SpannedEncodingResult<()> {
            make_manual_assign(encoder, block_builder, &mut |ty_args, args, target_ty| {
                vir_high::Expression::builtin_func_app_no_pos(function, ty_args, args, target_ty)
            })?;
            Ok(())
        };

        let make_binop = |encoder: &mut Self,
                          block_builder: &mut BasicBlockBuilder,
                          op_kind|
         -> SpannedEncodingResult<()> {
            make_manual_assign(encoder, block_builder, &mut |_ty_args, args, _target_ty| {
                vir_high::Expression::binary_op_no_pos(op_kind, args[0].clone(), args[1].clone())
            })?;
            Ok(())
        };

        if let Some(op_name) = full_called_function_name
            .as_str()
            .strip_prefix("std::ops::")
            .or_else(|| {
                full_called_function_name
                    .as_str()
                    .strip_prefix("core::ops::")
            })
        {
            let lhs = self
                .encode_statement_operand(location, &args[0])?
                .expression;
            if lhs.get_type() == &vir_high::Type::Int(vir_high::ty::Int::Unbounded) {
                use vir_high::BinaryOpKind::*;
                let ops = [
                    ("Add::add", Add),
                    ("Sub::sub", Sub),
                    ("Mul::mul", Mul),
                    ("Div::div", Div),
                    ("Rem::rem", Mod),
                ];
                for op in ops {
                    if op_name == op.0 {
                        make_binop(self, block_builder, op.1)?;
                        return Ok(true);
                    }
                }
            }
        }

        match full_called_function_name.as_str() {
            "std::rt::begin_panic" | "core::panicking::panic" | "core::panicking::panic_fmt" => {
                let panic_message = format!("{:?}", args[0]);
                let panic_cause = self.encoder.encode_panic_cause(span)?;
                if self.check_panics {
                    block_builder.add_comment(format!("Rust panic - {panic_message}"));
                    block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                        vir_high::Statement::assert_no_pos(false.into()),
                        span,
                        ErrorCtxt::Panic(panic_cause),
                        self.def_id,
                    )?);
                } else {
                    debug!("Absence of panic will not be checked")
                }
                assert!(target.is_none());
                if let mir::UnwindAction::Cleanup(cleanup) = unwind {
                    let successor =
                        vir_high::Successor::Goto(self.encode_basic_block_label(cleanup));
                    block_builder.set_successor_jump(successor);
                } else {
                    unimplemented!();
                }
            }
            "prusti_contracts::Int::new" => {
                make_builtin_call(self, block_builder, vir_high::BuiltinFunc::NewInt)?
            }
            "prusti_contracts::Int::new_usize" => {
                make_builtin_call(self, block_builder, vir_high::BuiltinFunc::NewInt)?
            }
            "prusti_contracts::Map::<K, V>::empty" => {
                make_builtin_call(self, block_builder, vir_high::BuiltinFunc::EmptyMap)?
            }
            "prusti_contracts::Map::<K, V>::insert" => {
                make_builtin_call(self, block_builder, vir_high::BuiltinFunc::UpdateMap)?
            }
            "prusti_contracts::Map::<K, V>::delete" => {
                unimplemented!()
            }
            "prusti_contracts::Map::<K, V>::len" => {
                make_builtin_call(self, block_builder, vir_high::BuiltinFunc::MapLen)?
            }
            "prusti_contracts::Map::<K, V>::contains" => {
                make_builtin_call(self, block_builder, vir_high::BuiltinFunc::MapContains)?
            }
            "prusti_contracts::Map::<K, V>::lookup" => {
                make_builtin_call(self, block_builder, vir_high::BuiltinFunc::LookupMap)?
            }
            "prusti_contracts::Seq::<T>::empty" => {
                make_builtin_call(self, block_builder, vir_high::BuiltinFunc::EmptySeq)?
            }
            "prusti_contracts::Seq::<T>::single" => {
                make_builtin_call(self, block_builder, vir_high::BuiltinFunc::SingleSeq)?
            }
            "prusti_contracts::Seq::<T>::concat" => {
                make_builtin_call(self, block_builder, vir_high::BuiltinFunc::ConcatSeq)?
            }
            "prusti_contracts::Seq::<T>::lookup" => {
                make_builtin_call(self, block_builder, vir_high::BuiltinFunc::LookupSeq)?
            }
            "prusti_contracts::Ghost::<T>::new" => {
                make_manual_assign(self, block_builder, &mut |_, args, _| args[0].clone())?
            }
            "prusti_contracts::snapshot_equality" => {
                unreachable!();
            }
            "std::ops::Index::index" | "core::ops::Index::index" => {
                let lhs = self
                    .encode_statement_operand(location, &args[0])?
                    .expression;
                let typ = match lhs.get_type() {
                    vir_high::Type::Reference(vir_high::ty::Reference { target_type, .. }) => {
                        &**target_type
                    }
                    _ => unreachable!(),
                };
                match typ {
                    vir_high::Type::Sequence(..) => {
                        make_builtin_call(self, block_builder, vir_high::BuiltinFunc::LookupSeq)?
                    }
                    vir_high::Type::Map(..) => {
                        make_builtin_call(self, block_builder, vir_high::BuiltinFunc::LookupMap)?
                    }
                    _ => return Ok(false),
                }
            }
            "std::cmp::PartialEq::eq" => {
                let lhs = self
                    .encode_statement_operand(location, &args[0])?
                    .expression;
                if matches!(
                    lhs.get_type(),
                    vir_high::Type::Reference(vir_high::ty::Reference {
                        target_type:
                            box vir_high::Type::Int(vir_high::ty::Int::Unbounded)
                            | box vir_high::Type::Sequence(..)
                            | box vir_high::Type::Map(..),
                        ..
                    })
                ) {
                    make_binop(self, block_builder, vir_high::BinaryOpKind::EqCmp)?;
                    return Ok(true);
                } else {
                    return Ok(false);
                }
            }
            _ => return Ok(false),
        };
        Ok(true)
    }
}
