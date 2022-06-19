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
        references::ReferencesInterface,
        snapshots::{
            IntoProcedureBoolExpression, IntoProcedureFinalSnapshot, IntoProcedureSnapshot,
            SnapshotValidityInterface, SnapshotVariablesInterface,
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
            Self::Havoc(statement) => {
                let mut statements = Vec::new();
                lowerer.encode_havoc_method_call(
                    &mut statements,
                    statement.predicate,
                    statement.position,
                )?;
                Ok(statements)
            }
            Self::Assume(statement) => Ok(vec![Statement::assume(
                statement.expression.to_procedure_bool_expression(lowerer)?,
                statement.position,
            )]),
            Self::Assert(statement) => {
                let assert = Statement::assert(
                    statement.expression.to_procedure_bool_expression(lowerer)?,
                    statement.position,
                );
                let low_statement = if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    Statement::conditional(
                        low_condition,
                        vec![assert],
                        Vec::new(),
                        statement.position,
                    )
                } else {
                    assert
                };
                Ok(vec![low_statement])
            }
            // FIXME: Instead of having a statement per predicate kind, have two
            // statements `Fold` and `Unfold` that would take a predicate as an
            // argument.
            Self::FoldOwned(statement) => {
                // FIXME: Remove code duplication between fold and unfold.
                let ty = statement.place.get_type();
                lowerer.mark_owned_non_aliased_as_unfolded(ty)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let arguments = lowerer.extract_non_type_arguments_from_type(ty)?;
                let low_statement = if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    stmtp! {
                        statement.position =>
                        fold<low_condition> OwnedNonAliased<ty>(
                            [place], [address], [snapshot]; arguments
                        )
                    }
                } else {
                    stmtp! {
                        statement.position =>
                        fold OwnedNonAliased<ty>([place], [address], [snapshot]; arguments)
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
                let arguments = lowerer.extract_non_type_arguments_from_type(ty)?;
                let low_statement = if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    stmtp! {
                        statement.position =>
                        unfold<low_condition> OwnedNonAliased<ty>(
                            [place], [address], [snapshot]; arguments
                        )
                    }
                } else {
                    stmtp! {
                        statement.position =>
                        unfold OwnedNonAliased<ty>([place], [address], [snapshot]; arguments)
                    }
                };
                Ok(vec![low_statement])
            }
            Self::FoldRef(statement) => {
                let ty = statement.place.get_type();
                lowerer.mark_owned_non_aliased_as_unfolded(ty)?;
                let lifetime = lowerer.encode_lifetime_const_into_variable(statement.lifetime)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let current_snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let lifetimes = lowerer
                    .extract_lifetime_variables(ty)?
                    .into_iter()
                    .map(|lifetime| lifetime.into());
                let low_statement = if statement.uniqueness.is_shared() {
                    if let Some(condition) = statement.condition {
                        let low_condition = lowerer.lower_block_marker_condition(condition)?;
                        stmtp! {
                            statement.position =>
                            fold<low_condition> FracRef<ty>(
                                lifetime, [place], [address], [current_snapshot];
                                lifetimes
                            )
                        }
                    } else {
                        stmtp! {
                            statement.position =>
                            fold FracRef<ty>(
                                lifetime, [place], [address], [current_snapshot];
                                lifetimes
                            )
                        }
                    }
                } else {
                    let final_snapshot = statement.place.to_procedure_final_snapshot(lowerer)?;
                    if let Some(condition) = statement.condition {
                        let low_condition = lowerer.lower_block_marker_condition(condition)?;
                        stmtp! {
                            statement.position =>
                            fold<low_condition> UniqueRef<ty>(
                                lifetime, [place], [address], [current_snapshot], [final_snapshot];
                                lifetimes
                            )
                        }
                    } else {
                        stmtp! {
                            statement.position =>
                            fold UniqueRef<ty>(
                                lifetime, [place], [address], [current_snapshot], [final_snapshot];
                                lifetimes
                            )
                        }
                    }
                };
                Ok(vec![low_statement])
            }
            Self::UnfoldRef(statement) => {
                let ty = statement.place.get_type();
                lowerer.mark_owned_non_aliased_as_unfolded(ty)?;
                let lifetime = lowerer.encode_lifetime_const_into_variable(statement.lifetime)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let current_snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let lifetimes = lowerer
                    .extract_lifetime_variables(ty)?
                    .into_iter()
                    .map(|lifetime| lifetime.into());
                let low_statement = if statement.uniqueness.is_shared() {
                    if let Some(condition) = statement.condition {
                        let low_condition = lowerer.lower_block_marker_condition(condition)?;
                        stmtp! {
                            statement.position =>
                            unfold<low_condition> FracRef<ty>(
                                lifetime, [place], [address], [current_snapshot];
                                lifetimes
                            )
                        }
                    } else {
                        stmtp! {
                            statement.position =>
                            unfold FracRef<ty>(
                                lifetime, [place], [address], [current_snapshot];
                                lifetimes
                            )
                        }
                    }
                } else {
                    let final_snapshot = statement.place.to_procedure_final_snapshot(lowerer)?;
                    if let Some(condition) = statement.condition {
                        let low_condition = lowerer.lower_block_marker_condition(condition)?;
                        stmtp! {
                            statement.position =>
                            unfold<low_condition> UniqueRef<ty>(
                                lifetime, [place], [address], [current_snapshot], [final_snapshot];
                                lifetimes
                            )
                        }
                    } else {
                        stmtp! {
                            statement.position =>
                            unfold UniqueRef<ty>(
                                lifetime, [place], [address], [current_snapshot], [final_snapshot];
                                lifetimes
                            )
                        }
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
                            call<low_condition> memory_block_join<ty>(
                                [address], [vir_low::Expression::full_permission()], [discriminant]
                            )
                        }
                    } else {
                        stmtp! {
                            statement.position =>
                            call<low_condition> memory_block_join<ty>(
                                [address], [vir_low::Expression::full_permission()]
                            )
                        }
                    }
                } else if let Some(discriminant) = discriminant {
                    stmtp! {
                        statement.position =>
                        call memory_block_join<ty>(
                            [address], [vir_low::Expression::full_permission()], [discriminant]
                        )
                    }
                } else {
                    stmtp! {
                        statement.position =>
                        call memory_block_join<ty>(
                            [address], [vir_low::Expression::full_permission()]
                        )
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
                            call<low_condition> memory_block_split<ty>(
                                [address], [vir_low::Expression::full_permission()], [discriminant]
                            )
                        }
                    } else {
                        stmtp! {
                            statement.position =>
                            call<low_condition> memory_block_split<ty>(
                                [address], [vir_low::Expression::full_permission()]
                            )
                        }
                    }
                } else if let Some(discriminant) = discriminant {
                    stmtp! {
                        statement.position =>
                        call memory_block_split<ty>(
                            [address], [vir_low::Expression::full_permission()], [discriminant]
                        )
                    }
                } else {
                    stmtp! {
                        statement.position =>
                        call memory_block_split<ty>(
                            [address], [vir_low::Expression::full_permission()]
                        )
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
                let arguments = lowerer.extract_non_type_arguments_from_type(ty)?;
                let low_statement = if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    stmtp! {
                        statement.position =>
                        call<low_condition> into_memory_block<ty>([place], [address], [snapshot]; arguments)
                    }
                } else {
                    stmtp! {
                        statement.position =>
                        call into_memory_block<ty>([place], [address], [snapshot]; arguments)
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
                            [validity] &&
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
                let mut target_ty_without_lifetime = target_ty.clone();
                target_ty_without_lifetime.erase_lifetime();
                let mut source_ty_without_lifetime = source_ty.clone();
                source_ty_without_lifetime.erase_lifetime();
                assert_eq!(target_ty_without_lifetime, source_ty_without_lifetime);
                lowerer.encode_move_place_method(target_ty)?;
                let target_place = lowerer.encode_expression_as_place(&statement.target)?;
                let target_address = lowerer.extract_root_address(&statement.target)?;
                let source_place = lowerer.encode_expression_as_place(&statement.source)?;
                let source_address = lowerer.extract_root_address(&statement.source)?;
                let value = statement.source.to_procedure_snapshot(lowerer)?;
                let mut statements = if let vir_mid::Type::Reference(reference) = target_ty {
                    let lifetime =
                        lowerer.encode_lifetime_const_into_variable(reference.lifetime.clone())?;
                    vec![stmtp! { statement.position =>
                        call move_place<target_ty>(
                            [target_place],
                            [target_address],
                            [source_place],
                            [source_address],
                            [value.clone()],
                            [lifetime.into()]
                        )
                    }]
                } else {
                    vec![stmtp! { statement.position =>
                        call move_place<target_ty>(
                            [target_place],
                            [target_address],
                            [source_place],
                            [source_address],
                            [value.clone()]
                        )
                    }]
                };
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
                let source_permission = if let Some(source_permission) = statement.source_permission
                {
                    source_permission.to_procedure_snapshot(lowerer)?.into()
                } else {
                    vir_low::Expression::full_permission()
                };
                let value = statement.source.to_procedure_snapshot(lowerer)?;
                let mut statements = vec![stmtp! { statement.position =>
                    call copy_place<target_ty>(
                        [target_place],
                        [target_address],
                        [source_place],
                        [source_address],
                        [source_permission],
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
            Self::Dead(statement) => {
                let ty = statement.target.get_type();
                let mut statements = Vec::new();
                if let vir_mid::Type::Reference(vir_mid::ty::Reference {
                    uniqueness: vir_mid::ty::Uniqueness::Unique,
                    box target_type,
                    ..
                }) = ty
                {
                    let target_type = target_type.clone();
                    let lifetimes = lowerer.extract_lifetime_variables(ty)?;
                    for lifetime in lifetimes {
                        let low_statement = vir_low::Statement::assert(
                            expr! { (acc(DeadLifetimeToken(lifetime))) },
                            statement.position,
                        );
                        statements.push(low_statement);
                    }
                    let place = statement.target.deref(target_type, statement.position);
                    let current_snapshot = place.to_procedure_snapshot(lowerer)?;
                    let final_snapshot = place.to_procedure_final_snapshot(lowerer)?;
                    let low_statement = vir_low::Statement::assume(
                        expr! { [current_snapshot] == [final_snapshot] },
                        statement.position,
                    );
                    statements.push(low_statement);
                }
                Ok(statements)
            }
            Self::DeadInclusion(statement) => {
                lowerer.encode_dead_inclusion_method()?;
                Ok(vec![Statement::method_call(
                    String::from("dead_inclusion"),
                    vec![
                        statement.target.to_procedure_snapshot(lowerer)?.into(),
                        statement.value.to_procedure_snapshot(lowerer)?.into(),
                    ],
                    vec![],
                    statement.position,
                )])
            }
            Self::LifetimeTake(statement) => {
                if statement.value.len() == 1 {
                    let value = vir_low::Expression::local_no_pos(
                        statement
                            .value
                            .first()
                            .unwrap()
                            .to_procedure_snapshot(lowerer)?,
                    );
                    let statements = vec![Statement::assign(
                        lowerer
                            .new_snapshot_variable_version(&statement.target, statement.position)?,
                        value,
                        statement.position,
                    )];
                    Ok(statements)
                } else {
                    lowerer.encode_lft_tok_sep_take_method(statement.value.len())?;
                    let mut arguments: Vec<vir_low::Expression> = vec![];
                    for lifetime in &statement.value {
                        arguments.push(vir_low::Expression::local_no_pos(
                            lifetime.to_procedure_snapshot(lowerer)?,
                        ));
                    }
                    let perm_amount = statement
                        .lifetime_token_permission
                        .to_procedure_snapshot(lowerer)?;
                    arguments.push(perm_amount);
                    let statements = vec![Statement::method_call(
                        format!("lft_tok_sep_take${}", statement.value.len()),
                        arguments.clone(),
                        vec![lowerer
                            .new_snapshot_variable_version(&statement.target, statement.position)?
                            .into()],
                        statement.position,
                    )];
                    Ok(statements)
                }
            }
            Self::LifetimeReturn(statement) => {
                if statement.value.len() > 1 {
                    lowerer.encode_lft_tok_sep_return_method(statement.value.len())?;
                    let mut arguments: Vec<vir_low::Expression> =
                        vec![vir_low::Expression::local_no_pos(
                            statement.target.to_procedure_snapshot(lowerer)?,
                        )];
                    for lifetime in &statement.value {
                        arguments.push(vir_low::Expression::local_no_pos(
                            lifetime.to_procedure_snapshot(lowerer)?,
                        ));
                    }
                    let perm_amount = statement
                        .lifetime_token_permission
                        .to_procedure_snapshot(lowerer)?;
                    arguments.push(perm_amount);
                    Ok(vec![Statement::method_call(
                        format!("lft_tok_sep_return${}", statement.value.len()),
                        arguments,
                        vec![],
                        statement.position,
                    )])
                } else {
                    Ok(vec![])
                }
            }
            Self::OpenFracRef(statement) => {
                let ty = statement.place.get_type();
                lowerer.encode_open_frac_bor_atomic_method(ty)?;
                let lifetime = lowerer.encode_lifetime_const_into_variable(statement.lifetime)?;
                let perm_amount = statement
                    .lifetime_token_permission
                    .to_procedure_snapshot(lowerer)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let current_snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let targets = vec![statement
                    .predicate_permission_amount
                    .to_procedure_snapshot(lowerer)?
                    .into()];
                Ok(vec![Statement::method_call(
                    method_name!(frac_bor_atomic_acc<ty>),
                    vec![
                        lifetime.into(),
                        perm_amount,
                        place,
                        address,
                        current_snapshot,
                    ],
                    targets,
                    statement.position,
                )])
            }
            Self::CloseFracRef(statement) => {
                let ty = statement.place.get_type();
                let lifetime = lowerer.encode_lifetime_const_into_variable(statement.lifetime)?;
                let perm_amount = statement
                    .lifetime_token_permission
                    .to_procedure_snapshot(lowerer)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let current_snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let tmp_frac_ref_perm = statement
                    .predicate_permission_amount
                    .to_procedure_snapshot(lowerer)?;
                Ok(vec![stmtp! {
                    statement.position =>
                    apply (
                        acc(OwnedNonAliased<ty>(
                            [place.clone()], [address.clone()], [current_snapshot.clone()]),
                            tmp_frac_ref_perm
                        )
                    ) --* (
                        (acc(LifetimeToken(lifetime), [perm_amount])) &&
                        (acc(FracRef<ty>(lifetime, [place], [address], [current_snapshot])))
                    )
                }])
            }
            Self::ObtainMutRef(_statement) => {
                Ok(vec![]) // NOTE: nothing to do, we only want the fold_unfold
            }
            Self::OpenMutRef(statement) => {
                let ty = statement.place.get_type();
                lowerer.encode_open_close_mut_ref_methods(ty)?;
                let lifetime = lowerer.encode_lifetime_const_into_variable(statement.lifetime)?;
                let perm_amount = statement
                    .lifetime_token_permission
                    .to_procedure_snapshot(lowerer)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let current_snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let final_snapshot = statement.place.to_procedure_final_snapshot(lowerer)?;
                let statements = vec![stmtp! { statement.position =>
                    call open_mut_ref<ty>(
                        lifetime,
                        [perm_amount],
                        [place],
                        [address],
                        [current_snapshot],
                        [final_snapshot]
                    )
                }];
                Ok(statements)
            }
            Self::CloseMutRef(statement) => {
                let ty = statement.place.get_type();
                lowerer.encode_open_close_mut_ref_methods(ty)?;
                let lifetime = lowerer.encode_lifetime_const_into_variable(statement.lifetime)?;
                let perm_amount = statement
                    .lifetime_token_permission
                    .to_procedure_snapshot(lowerer)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let current_snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let final_snapshot = statement.place.to_procedure_final_snapshot(lowerer)?;
                let statements = vec![stmtp! { statement.position =>
                    call close_mut_ref<ty>(
                        lifetime,
                        [perm_amount],
                        [place],
                        [address],
                        [current_snapshot],
                        [final_snapshot]
                    )
                }];
                Ok(statements)
            }
            Self::BorShorten(statement) => {
                let ty = statement.value.get_type();
                lowerer.encode_bor_shorten_method(ty)?;
                let perm_amount = statement
                    .lifetime_token_permission
                    .to_procedure_snapshot(lowerer)?;
                let lifetime =
                    lowerer.encode_lifetime_const_into_variable(statement.lifetime.clone())?;
                let old_lifetime =
                    lowerer.encode_lifetime_const_into_variable(statement.old_lifetime.clone())?;
                let reference_place = lowerer.encode_expression_as_place(&statement.value)?;
                let deref_place =
                    lowerer.reference_deref_place(reference_place, statement.position)?;
                let reference_value = statement.value.to_procedure_snapshot(lowerer)?;
                let address =
                    lowerer.reference_address(ty, reference_value.clone(), statement.position)?;
                let current_snapshot = lowerer.reference_target_current_snapshot(
                    ty,
                    reference_value.clone(),
                    statement.position,
                )?;
                let final_snapshot = lowerer.reference_target_final_snapshot(
                    ty,
                    reference_value,
                    statement.position,
                )?;
                Ok(vec![stmtp! { statement.position =>
                    call bor_shorten<ty>(
                        lifetime,
                        old_lifetime,
                        [perm_amount],
                        [deref_place],
                        [address],
                        [current_snapshot],
                        [final_snapshot]
                    )
                }])
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
            Predicate::LifetimeToken(predicate) => {
                lowerer.encode_lifetime_token_predicate()?;
                let lifetime = lowerer.encode_lifetime_const_into_variable(predicate.lifetime)?;
                let permission = predicate.permission.to_procedure_snapshot(lowerer)?;
                expr! { acc(LifetimeToken([lifetime.into()]), [permission])}
                    .set_default_position(predicate.position)
            }
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
                let lifetimes = lowerer
                    .extract_lifetime_variables(ty)?
                    .into_iter()
                    .map(|lifetime| lifetime.into());
                exprp! {
                    predicate.position =>
                    (acc(OwnedNonAliased<ty>([place], [address], [snapshot]; lifetimes))) &&
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
