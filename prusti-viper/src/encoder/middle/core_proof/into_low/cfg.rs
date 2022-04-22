use super::IntoLow;
use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        block_markers::BlockMarkersInterface,
        builtin_methods::BuiltinMethodsInterface,
        lifetimes::LifetimesInterface,
        lowerer::{Lowerer, VariablesLowererInterface},
        places::PlacesInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        snapshots::{
            IntoProcedureBoolExpression, IntoProcedureSnapshot, SnapshotValidityInterface,
            SnapshotVariablesInterface,
        },
    },
};
use vir_crate::{
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

impl<S: IntoLow> IntoLow for Vec<S> {
    type Target = Vec<<S as IntoLow>::Target>;
    fn into_low<'p, 'v: 'p, 'tcx: 'v>(
        self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        self.into_iter()
            .map(|decl| decl.into_low(lowerer))
            .collect()
    }
}

impl IntoLow for vir_mid::Statement {
    type Target = Vec<vir_low::Statement>;
    fn into_low<'p, 'v: 'p, 'tcx: 'v>(
        self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        use vir_low::{macros::*, Statement};
        match self {
            Self::Comment(statement) => Ok(vec![Statement::comment(statement.comment)]),
            Self::OldLabel(label) => {
                lowerer.save_old_label(label.name)?;
                Ok(Vec::new())
            }
            Self::Inhale(statement) => {
                if let vir_mid::Predicate::OwnedNonAliased(owned) = &statement.predicate {
                    lowerer.mark_owned_non_aliased_as_unfolded(owned.place.get_type())?;
                }
                Ok(vec![Statement::inhale(
                    statement.predicate.into_low(lowerer)?,
                    statement.position,
                )])
            }
            Self::Exhale(statement) => {
                if let vir_mid::Predicate::OwnedNonAliased(owned) = &statement.predicate {
                    lowerer.mark_owned_non_aliased_as_unfolded(owned.place.get_type())?;
                }
                Ok(vec![Statement::exhale(
                    statement.predicate.into_low(lowerer)?,
                    statement.position,
                )])
            }
            Self::Consume(statement) => {
                let mut statements = Vec::new();
                lowerer.encode_consume_method_call(
                    &mut statements,
                    statement.operand,
                    statement.position,
                )?;
                Ok(statements)
            }
            Self::Assume(statement) => Ok(vec![Statement::assume(
                statement.expression.to_procedure_bool_expression(lowerer)?,
                statement.position,
            )]),
            Self::Assert(statement) => Ok(vec![Statement::assert(
                statement.expression.to_procedure_bool_expression(lowerer)?,
                statement.position,
            )]),
            Self::FoldOwned(statement) => {
                let ty = statement.place.get_type();
                lowerer.mark_owned_non_aliased_as_unfolded(ty)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let low_statement = if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    stmtp! {
                        statement.position =>
                        fold<low_condition> OwnedNonAliased<ty>([place], [address], [snapshot])
                    }
                } else {
                    stmtp! {
                        statement.position =>
                        fold OwnedNonAliased<ty>([place], [address], [snapshot])
                    }
                };
                Ok(vec![low_statement])
            }
            Self::UnfoldOwned(statement) => {
                let ty = statement.place.get_type();
                lowerer.mark_owned_non_aliased_as_unfolded(ty)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let low_statement = if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    stmtp! {
                        statement.position =>
                        unfold<low_condition> OwnedNonAliased<ty>([place], [address], [snapshot])
                    }
                } else {
                    stmtp! {
                        statement.position =>
                        unfold OwnedNonAliased<ty>([place], [address], [snapshot])
                    }
                };
                Ok(vec![low_statement])
            }
            Self::JoinBlock(statement) => {
                let ty = statement.place.get_type();
                lowerer.encode_memory_block_join_method(ty)?;
                let address = lowerer.encode_expression_as_place_address(&statement.place)?;
                let discriminant = if let Some(variant_index) = &statement.enum_variant {
                    // TODO: Remove code duplication with SplitBlock variant.
                    let type_decl = lowerer.encoder.get_type_decl_mid(ty)?;
                    match type_decl {
                        vir_mid::TypeDecl::Enum(decl) => {
                            Some(decl.get_discriminant(variant_index).unwrap().into())
                        }
                        vir_mid::TypeDecl::Union(decl) => {
                            Some(decl.get_discriminant(variant_index).unwrap().into())
                        }
                        _ => unreachable!("type: {}", type_decl),
                    }
                } else {
                    None
                };
                let low_statement = if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    if let Some(discriminant) = discriminant {
                        stmtp! {
                            statement.position =>
                            call<low_condition> memory_block_join<ty>([address], [discriminant])
                        }
                    } else {
                        stmtp! {
                            statement.position =>
                            call<low_condition> memory_block_join<ty>([address])
                        }
                    }
                } else if let Some(discriminant) = discriminant {
                    stmtp! {
                        statement.position =>
                        call memory_block_join<ty>([address], [discriminant])
                    }
                } else {
                    stmtp! {
                        statement.position =>
                        call memory_block_join<ty>([address])
                    }
                };
                Ok(vec![low_statement])
            }
            Self::SplitBlock(statement) => {
                let ty = statement.place.get_type();
                lowerer.encode_memory_block_split_method(ty)?;
                let address = lowerer.encode_expression_as_place_address(&statement.place)?;
                let discriminant = if let Some(variant_index) = &statement.enum_variant {
                    // TODO: Remove code duplication with JoinBlock variant.
                    let type_decl = lowerer.encoder.get_type_decl_mid(ty)?;
                    match type_decl {
                        vir_mid::TypeDecl::Enum(decl) => {
                            Some(decl.get_discriminant(variant_index).unwrap().into())
                        }
                        vir_mid::TypeDecl::Union(decl) => {
                            Some(decl.get_discriminant(variant_index).unwrap().into())
                        }
                        _ => unreachable!("type: {}", type_decl),
                    }
                } else {
                    None
                };
                let low_statement = if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    if let Some(discriminant) = discriminant {
                        stmtp! {
                            statement.position =>
                            call<low_condition> memory_block_split<ty>([address], [discriminant])
                        }
                    } else {
                        stmtp! {
                            statement.position =>
                            call<low_condition> memory_block_split<ty>([address])
                        }
                    }
                } else if let Some(discriminant) = discriminant {
                    stmtp! {
                        statement.position =>
                        call memory_block_split<ty>([address], [discriminant])
                    }
                } else {
                    stmtp! {
                        statement.position =>
                        call memory_block_split<ty>([address])
                    }
                };
                Ok(vec![low_statement])
            }
            Self::ConvertOwnedIntoMemoryBlock(statement) => {
                let ty = statement.place.get_type();
                lowerer.encode_into_memory_block_method(ty)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let lifetimes = lowerer.extract_lifetime_variables_as_expr(ty)?;
                let low_statement = if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    stmtp! {
                        statement.position =>
                        call<low_condition> into_memory_block<ty>([place], [address], [snapshot]; lifetimes)
                    }
                } else {
                    stmtp! {
                        statement.position =>
                        call into_memory_block<ty>([place], [address], [snapshot]; lifetimes)
                    }
                };
                Ok(vec![low_statement])
            }
            Self::RestoreMutBorrowed(statement) => {
                let ty = statement.place.get_type();
                lowerer.encode_into_memory_block_method(ty)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let lifetime = lowerer.encode_lifetime_const_into_variable(statement.lifetime)?;
                let validity = lowerer.encode_snapshot_valid_call_for_type(snapshot.clone(), ty)?;
                let low_statement = if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    stmtp! {
                        statement.position =>
                        apply<low_condition> (acc(DeadLifetimeToken(lifetime))) --* (
                            (acc(OwnedNonAliased<ty>([place], [address], [snapshot]))) &&
                            (acc(DeadLifetimeToken(lifetime)))
                        )
                    }
                } else {
                    stmtp! {
                        statement.position =>
                        apply (acc(DeadLifetimeToken(lifetime))) --* (
                            (acc(OwnedNonAliased<ty>([place], [address], [snapshot]))) &&
                            [validity] &&
                            (acc(DeadLifetimeToken(lifetime)))
                        )
                    }
                };
                Ok(vec![low_statement])
            }
            Self::MovePlace(statement) => {
                // TODO: Remove code duplication with Self::CopyPlace
                let target_ty = statement.target.get_type();
                let source_ty = statement.source.get_type();
                assert_eq!(target_ty, source_ty);
                lowerer.encode_move_place_method(target_ty)?;
                let target_place = lowerer.encode_expression_as_place(&statement.target)?;
                let target_address = lowerer.extract_root_address(&statement.target)?;
                let source_place = lowerer.encode_expression_as_place(&statement.source)?;
                let source_address = lowerer.extract_root_address(&statement.source)?;
                let value = statement.source.to_procedure_snapshot(lowerer)?;
                let mut statements = vec![stmtp! { statement.position =>
                    call move_place<target_ty>(
                        [target_place],
                        [target_address],
                        [source_place],
                        [source_address],
                        [value.clone()]
                    )
                }];
                lowerer.encode_snapshot_update(
                    &mut statements,
                    &statement.target,
                    value,
                    statement.position,
                )?;
                Ok(statements)
            }
            Self::CopyPlace(statement) => {
                // TODO: Remove code duplication with Self::MovePlace
                let target_ty = statement.target.get_type();
                let source_ty = statement.source.get_type();
                assert_eq!(target_ty, source_ty);
                lowerer.encode_copy_place_method(target_ty)?;
                let target_place = lowerer.encode_expression_as_place(&statement.target)?;
                let target_address = lowerer.extract_root_address(&statement.target)?;
                let source_place = lowerer.encode_expression_as_place(&statement.source)?;
                let source_address = lowerer.extract_root_address(&statement.source)?;
                let value = statement.source.to_procedure_snapshot(lowerer)?;
                let mut statements = vec![stmtp! { statement.position =>
                    call copy_place<target_ty>(
                        [target_place],
                        [target_address],
                        [source_place],
                        [source_address],
                        [value.clone()]
                    )
                }];
                lowerer.encode_snapshot_update(
                    &mut statements,
                    &statement.target,
                    value,
                    statement.position,
                )?;
                Ok(statements)
            }
            Self::WritePlace(statement) => {
                let target_ty = statement.target.get_type();
                let source_ty = statement.value.get_type();
                assert_eq!(target_ty, source_ty);
                lowerer.encode_write_place_method(target_ty)?;
                let target_place = lowerer.encode_expression_as_place(&statement.target)?;
                let target_address = lowerer.extract_root_address(&statement.target)?;
                let value = statement.value.to_procedure_snapshot(lowerer)?;
                let mut statements = vec![stmtp! { statement.position =>
                    call write_place<target_ty>(
                        [target_place],
                        [target_address],
                        [value.clone()]
                    )
                }];
                lowerer.encode_snapshot_update(
                    &mut statements,
                    &statement.target,
                    value,
                    statement.position,
                )?;
                Ok(statements)
            }
            Self::WriteAddress(statement) => {
                let target_ty = statement.target.get_type();
                let source_ty = statement.value.get_type();
                assert_eq!(target_ty, source_ty);
                lowerer.encode_write_address_method(target_ty)?;
                let target_address =
                    lowerer.encode_expression_as_place_address(&statement.target)?;
                let value = statement.value.to_procedure_snapshot(lowerer)?;
                let statements = vec![stmtp! { statement.position =>
                    call write_address<target_ty>(
                        [target_address],
                        [value]
                    )
                }];
                Ok(statements)
            }
            Self::Assign(statement) => {
                let mut statements = Vec::new();
                lowerer.encode_assign_method_call(
                    &mut statements,
                    statement.target,
                    statement.value,
                    statement.position,
                )?;
                Ok(statements)
            }
            Self::NewLft(statement) => {
                let targets = vec![vir_low::Expression::local_no_pos(
                    statement.target.to_procedure_snapshot(lowerer)?,
                )];
                lowerer.encode_newlft_method()?;
                Ok(vec![Statement::method_call(
                    String::from("newlft"),
                    vec![],
                    targets,
                    statement.position,
                )])
            }
            Self::EndLft(statement) => {
                let arguments = vec![vir_low::Expression::local_no_pos(
                    statement.lifetime.to_procedure_snapshot(lowerer)?,
                )];
                lowerer.encode_endlft_method()?;
                Ok(vec![Statement::method_call(
                    String::from("endlft"),
                    arguments,
                    vec![],
                    statement.position,
                )])
            }
            Self::GhostAssignment(statement) => {
                let statements = vec![Statement::assign(
                    statement.target.to_procedure_snapshot(lowerer)?,
                    statement.value.to_procedure_snapshot(lowerer)?,
                    statement.position,
                )];
                Ok(statements)
            }
            Self::LifetimeTake(_statement) => {
                unimplemented!();
            }
            Self::OpenMutRef(_statement) => {
                unimplemented!();
            }
            Self::CloseMutRef(_statement) => {
                unimplemented!();
            }
        }
    }
}

impl IntoLow for vir_mid::Predicate {
    type Target = vir_low::Expression;
    fn into_low<'p, 'v: 'p, 'tcx: 'v>(
        self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        use vir_low::macros::*;
        use vir_mid::Predicate;
        let result = match self {
            Predicate::MemoryBlockStack(predicate) => {
                lowerer.encode_memory_block_predicate()?;
                let place = lowerer.encode_expression_as_place_address(&predicate.place)?;
                let size = predicate.size.to_procedure_snapshot(lowerer)?;
                expr! { acc(MemoryBlock([place], [size]))}.set_default_position(predicate.position)
            }
            Predicate::MemoryBlockStackDrop(predicate) => {
                let place = lowerer.encode_expression_as_place_address(&predicate.place)?;
                let size = predicate.size.to_procedure_snapshot(lowerer)?;
                lowerer.encode_memory_block_stack_drop_acc(place, size, predicate.position)?
            }
            Predicate::MemoryBlockHeap(predicate) => {
                unimplemented!("predicate: {}", predicate);
            }
            Predicate::MemoryBlockHeapDrop(predicate) => {
                unimplemented!("predicate: {}", predicate);
            }
            Predicate::OwnedNonAliased(predicate) => {
                let place = lowerer.encode_expression_as_place(&predicate.place)?;
                let address = lowerer.extract_root_address(&predicate.place)?;
                let snapshot = predicate.place.to_procedure_snapshot(lowerer)?;
                let ty = predicate.place.get_type();
                let valid = lowerer.encode_snapshot_valid_call_for_type(snapshot.clone(), ty)?;
                exprp! {
                    predicate.position =>
                    (acc(OwnedNonAliased<ty>([place], [address], [snapshot]))) &&
                    [valid]
                }
            }
        };
        Ok(result)
    }
}

impl IntoLow for vir_mid::BasicBlockId {
    type Target = vir_low::Label;
    fn into_low<'p, 'v: 'p, 'tcx: 'v>(
        self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        Ok(vir_low::Label { name: self.name })
    }
}

impl IntoLow for vir_mid::Successor {
    type Target = vir_low::Successor;
    fn into_low<'p, 'v: 'p, 'tcx: 'v>(
        self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        match self {
            vir_mid::Successor::Exit => Ok(vir_low::Successor::Return),
            vir_mid::Successor::Goto(target) => {
                Ok(vir_low::Successor::Goto(target.into_low(lowerer)?))
            }
            vir_mid::Successor::GotoSwitch(targets) => {
                let mut new_targets = Vec::new();
                for (test, target) in targets {
                    let test_low = test.to_procedure_bool_expression(lowerer)?;
                    new_targets.push((test_low, target.into_low(lowerer)?))
                }
                Ok(vir_low::Successor::GotoSwitch(new_targets))
            }
            vir_mid::Successor::NonDetChoice(first, second) => {
                use vir_low::macros::*;
                let choice = lowerer.create_new_temporary_variable(vir_low::Type::Bool)?;
                Ok(vir_low::Successor::GotoSwitch(vec![
                    (expr! { choice }, first.into_low(lowerer)?),
                    (expr! { !choice }, second.into_low(lowerer)?),
                ]))
            }
        }
    }
}
