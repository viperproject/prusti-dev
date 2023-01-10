use super::IntoLow;
use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        block_markers::BlockMarkersInterface,
        builtin_methods::{BuiltinMethodCallsInterface, BuiltinMethodsInterface, CallContext},
        labels::LabelsInterface,
        lifetimes::LifetimesInterface,
        lowerer::{Lowerer, VariablesLowererInterface},
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        references::ReferencesInterface,
        snapshots::{
            IntoProcedureAssertion, IntoProcedureBoolExpression, IntoProcedureFinalSnapshot,
            IntoProcedureSnapshot, IntoSnapshotLowerer, PredicateKind,
            ProcedureExpressionToSnapshot, ProcedureSnapshot, SnapshotValidityInterface,
            SnapshotValuesInterface, SnapshotVariablesInterface,
        },
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    common::{check_mode::CheckMode, expression::QuantifierHelpers},
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
            Self::OldLabel(statement) => {
                lowerer.save_old_label(statement.name.clone())?;
                lowerer.save_custom_label(statement.name.clone())?;
                Ok(vec![vir_low::Statement::label(
                    statement.name,
                    statement.position,
                )])
            }
            Self::InhalePredicate(statement) => {
                if let vir_mid::Predicate::OwnedNonAliased(owned) = &statement.predicate {
                    lowerer.mark_owned_non_aliased_as_unfolded(owned.place.get_type())?;
                }
                Ok(vec![Statement::inhale(
                    statement.predicate.into_low(lowerer)?,
                    statement.position,
                )])
            }
            Self::ExhalePredicate(statement) => {
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
            Self::GhostHavoc(statement) => {
                let mut statements = Vec::new();
                lowerer.encode_ghost_havoc_method_call(
                    &mut statements,
                    statement.variable,
                    statement.position,
                )?;
                Ok(statements)
            }
            Self::HeapHavoc(statement) => {
                let new_version = lowerer.new_heap_variable_version(statement.position)?;
                Ok(vec![vir_low::Statement::comment(format!(
                    "new heap version: {}",
                    new_version
                ))])
            }
            Self::InhaleExpression(statement) => Ok(vec![Statement::inhale(
                statement.expression.to_procedure_assertion(lowerer)?,
                statement.position,
            )]),
            Self::ExhaleExpression(statement) => {
                let assertion = statement.expression.to_procedure_assertion(lowerer)?;
                let exhale = Statement::exhale(assertion, statement.position);
                Ok(vec![exhale])
            }
            Self::Assume(statement) => {
                assert!(
                    statement.expression.is_pure(),
                    "must be pure: {}",
                    statement.expression
                );
                Ok(vec![Statement::assume(
                    statement.expression.to_procedure_assertion(lowerer)?,
                    statement.position,
                )])
            }
            Self::Assert(statement) => {
                assert!(
                    statement.expression.is_pure(),
                    "must be pure: {}",
                    statement.expression
                );
                let assert = Statement::assert(
                    statement.expression.to_procedure_assertion(lowerer)?,
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
                let ty = statement.place.get_type();
                lowerer.mark_owned_non_aliased_as_unfolded(ty)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let root_address = lowerer.extract_root_address(&statement.place)?;
                let mut place_encoder =
                    ProcedureExpressionToSnapshot::for_place(PredicateKind::Owned);
                let snapshot =
                    place_encoder.expression_to_snapshot(lowerer, &statement.place, false)?;
                // let snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let predicate = lowerer.owned_non_aliased_predicate(
                    CallContext::Procedure,
                    ty,
                    ty,
                    place,
                    root_address,
                    snapshot,
                    None,
                )?;
                assert!(predicate.is_predicate_access_predicate());
                let mut low_statement = vir_low::Statement::fold_no_pos(predicate);
                if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    low_statement = vir_low::Statement::conditional_no_pos(
                        low_condition,
                        vec![low_statement],
                        Vec::new(),
                    );
                }
                Ok(vec![low_statement.set_default_position(statement.position)])
            }
            Self::UnfoldOwned(statement) => {
                let ty = statement.place.get_type();
                lowerer.mark_owned_non_aliased_as_unfolded(ty)?;
                let root_address = lowerer.extract_root_address(&statement.place)?;
                let mut place_encoder =
                    ProcedureExpressionToSnapshot::for_place(PredicateKind::Owned);
                let snapshot =
                    place_encoder.expression_to_snapshot(lowerer, &statement.place, false)?;
                // let snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let predicate = lowerer.owned_non_aliased_predicate(
                    CallContext::Procedure,
                    ty,
                    ty,
                    place,
                    root_address,
                    snapshot,
                    None,
                )?;
                assert!(predicate.is_predicate_access_predicate());
                let mut low_statement = vir_low::Statement::unfold_no_pos(predicate);
                if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    low_statement = vir_low::Statement::conditional_no_pos(
                        low_condition,
                        vec![low_statement],
                        Vec::new(),
                    );
                }
                Ok(vec![low_statement.set_default_position(statement.position)])
            }
            Self::FoldRef(statement) => {
                let ty = statement.place.get_type();
                lowerer.mark_owned_non_aliased_as_unfolded(ty)?;
                let lifetime =
                    lowerer.encode_lifetime_const_into_procedure_variable(statement.lifetime)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let root_address = lowerer.extract_root_address(&statement.place)?;
                // let current_snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let predicate = if statement.uniqueness.is_shared() {
                    let mut place_encoder =
                        ProcedureExpressionToSnapshot::for_place(PredicateKind::FracRef {
                            lifetime: lifetime.clone().into(),
                        });
                    let current_snapshot =
                        place_encoder.expression_to_snapshot(lowerer, &statement.place, false)?;
                    lowerer.frac_ref_predicate(
                        CallContext::Procedure,
                        ty,
                        ty,
                        place,
                        root_address,
                        current_snapshot,
                        lifetime.into(),
                        None,
                    )?
                } else {
                    let mut place_encoder =
                        ProcedureExpressionToSnapshot::for_place(PredicateKind::UniqueRef {
                            lifetime: lifetime.clone().into(),
                            is_final: false,
                        });
                    let current_snapshot =
                        place_encoder.expression_to_snapshot(lowerer, &statement.place, false)?;
                    let mut place_encoder =
                        ProcedureExpressionToSnapshot::for_place(PredicateKind::UniqueRef {
                            lifetime: lifetime.clone().into(),
                            is_final: false,
                        });
                    let final_snapshot =
                        place_encoder.expression_to_snapshot(lowerer, &statement.place, true)?;
                    // let final_snapshot = statement.place.to_procedure_final_snapshot(lowerer)?;
                    lowerer.unique_ref_predicate(
                        CallContext::Procedure,
                        ty,
                        ty,
                        place,
                        root_address,
                        current_snapshot,
                        final_snapshot,
                        lifetime.into(),
                        None,
                    )?
                };
                let mut low_statement = vir_low::Statement::fold_no_pos(predicate);
                if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    low_statement = vir_low::Statement::conditional_no_pos(
                        low_condition,
                        vec![low_statement],
                        Vec::new(),
                    );
                }
                Ok(vec![low_statement.set_default_position(statement.position)])
            }
            Self::UnfoldRef(statement) => {
                let ty = statement.place.get_type();
                lowerer.mark_owned_non_aliased_as_unfolded(ty)?;
                let lifetime =
                    lowerer.encode_lifetime_const_into_procedure_variable(statement.lifetime)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let root_address = lowerer.extract_root_address(&statement.place)?;
                // let current_snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let predicate = if statement.uniqueness.is_shared() {
                    let mut place_encoder =
                        ProcedureExpressionToSnapshot::for_place(PredicateKind::FracRef {
                            lifetime: lifetime.clone().into(),
                        });
                    let current_snapshot =
                        place_encoder.expression_to_snapshot(lowerer, &statement.place, false)?;
                    lowerer.frac_ref_predicate(
                        CallContext::Procedure,
                        ty,
                        ty,
                        place,
                        root_address,
                        current_snapshot,
                        lifetime.into(),
                        None,
                    )?
                } else {
                    let mut place_encoder =
                        ProcedureExpressionToSnapshot::for_place(PredicateKind::UniqueRef {
                            lifetime: lifetime.clone().into(),
                            is_final: false,
                        });
                    let current_snapshot =
                        place_encoder.expression_to_snapshot(lowerer, &statement.place, false)?;
                    let mut place_encoder =
                        ProcedureExpressionToSnapshot::for_place(PredicateKind::UniqueRef {
                            lifetime: lifetime.clone().into(),
                            is_final: false,
                        });
                    let final_snapshot =
                        place_encoder.expression_to_snapshot(lowerer, &statement.place, true)?;
                    // let final_snapshot = statement.place.to_procedure_final_snapshot(lowerer)?;
                    lowerer.unique_ref_predicate(
                        CallContext::Procedure,
                        ty,
                        ty,
                        place,
                        root_address,
                        current_snapshot,
                        final_snapshot,
                        lifetime.into(),
                        None,
                    )?
                };
                let mut low_statement = vir_low::Statement::unfold_no_pos(predicate);
                if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    low_statement = vir_low::Statement::conditional_no_pos(
                        low_condition,
                        vec![low_statement],
                        Vec::new(),
                    );
                }
                Ok(vec![low_statement.set_default_position(statement.position)])
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
            Self::JoinRange(statement) => {
                let ty = statement.address.get_type();
                let vir_mid::Type::Pointer(pointer_type) = ty else {
                    unreachable!()
                };
                let target_type = &*pointer_type.target_type;
                lowerer.encode_memory_block_range_join_method(target_type)?;
                let pointer_value = statement.address.to_procedure_snapshot(lowerer)?;
                let start_address =
                    lowerer.pointer_address(ty, pointer_value, statement.position)?;
                let start_index = statement.start_index.to_procedure_snapshot(lowerer)?;
                let end_index = statement.end_index.to_procedure_snapshot(lowerer)?;
                let low_statement = stmtp! {
                    statement.position =>
                    call memory_block_range_join<target_type>(
                        [start_address], [start_index], [end_index]
                    )
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
            Self::SplitRange(statement) => {
                let ty = statement.address.get_type();
                let vir_mid::Type::Pointer(pointer_type) = ty else {
                    unreachable!()
                };
                let target_type = &*pointer_type.target_type;
                lowerer.encode_memory_block_range_split_method(target_type)?;
                let pointer_value = statement.address.to_procedure_snapshot(lowerer)?;
                let start_address =
                    lowerer.pointer_address(ty, pointer_value, statement.position)?;
                let start_index = statement.start_index.to_procedure_snapshot(lowerer)?;
                let end_index = statement.end_index.to_procedure_snapshot(lowerer)?;
                let low_statement = stmtp! {
                    statement.position =>
                    call memory_block_range_split<target_type>(
                        [start_address], [start_index], [end_index]
                    )
                };
                Ok(vec![low_statement])
            }
            Self::ConvertOwnedIntoMemoryBlock(statement) => {
                let ty = statement.place.get_type();
                lowerer.encode_into_memory_block_method(ty)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let root_address = lowerer.extract_root_address(&statement.place)?;
                // let snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let mut place_encoder =
                    ProcedureExpressionToSnapshot::for_place(PredicateKind::Owned);
                let snapshot =
                    place_encoder.expression_to_snapshot(lowerer, &statement.place, false)?;
                let low_condition = statement
                    .condition
                    .map(|condition| lowerer.lower_block_marker_condition(condition))
                    .transpose()?;
                let low_statement = lowerer.call_into_memory_block_method(
                    CallContext::Procedure,
                    ty,
                    ty,
                    statement.position,
                    low_condition,
                    place,
                    root_address,
                    snapshot,
                )?;
                Ok(vec![low_statement.set_default_position(statement.position)])
            }
            Self::RestoreMutBorrowed(statement) => {
                let ty = statement.place.get_type();
                lowerer.encode_into_memory_block_method(ty)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let root_address = lowerer.extract_root_address(&statement.place)?;
                let current_snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                let lifetime =
                    lowerer.encode_lifetime_const_into_procedure_variable(statement.lifetime)?;
                let validity =
                    lowerer.encode_snapshot_valid_call_for_type(current_snapshot.clone(), ty)?;
                let restored_predicate = if let Some((deref_lifetime, uniqueness)) =
                    statement.place.get_dereference_kind()
                {
                    let deref_lifetime = lowerer
                        .encode_lifetime_const_into_procedure_variable(deref_lifetime)?
                        .into();
                    if uniqueness.is_unique() {
                        let final_snapshot =
                            statement.place.to_procedure_final_snapshot(lowerer)?;
                        lowerer.unique_ref(
                            CallContext::Procedure,
                            ty,
                            ty,
                            place,
                            root_address,
                            current_snapshot,
                            final_snapshot,
                            deref_lifetime,
                            None, // FIXME
                        )?
                    } else {
                        lowerer.frac_ref(
                            CallContext::Procedure,
                            ty,
                            ty,
                            place,
                            root_address,
                            current_snapshot,
                            deref_lifetime,
                        )?
                    }
                } else {
                    lowerer.owned_non_aliased(
                        CallContext::Procedure,
                        ty,
                        ty,
                        place,
                        root_address,
                        current_snapshot,
                        None,
                    )?
                };
                let low_statement = if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    stmtp! {
                        statement.position =>
                        apply<low_condition> (acc(DeadLifetimeToken(lifetime))) --* (
                            [restored_predicate] &&
                            [validity] &&
                            (acc(DeadLifetimeToken(lifetime)))
                        )
                    }
                } else {
                    stmtp! {
                        statement.position =>
                        apply (acc(DeadLifetimeToken(lifetime))) --* (
                            [restored_predicate] &&
                            [validity] &&
                            (acc(DeadLifetimeToken(lifetime)))
                        )
                    }
                };
                Ok(vec![low_statement])
            }
            Self::RestoreRawBorrowed(statement) => {
                let ty = statement.restored_place.get_type();
                lowerer.encode_restore_raw_borrowed_method(ty)?;
                let borrowing_place_parent = statement.borrowing_place.get_parent_ref().unwrap();
                let borrowing_snapshot = borrowing_place_parent.to_procedure_snapshot(lowerer)?;
                let borrowing_address = lowerer.pointer_address(
                    borrowing_place_parent.get_type(),
                    borrowing_snapshot,
                    statement.position,
                )?;
                let restored_place =
                    lowerer.encode_expression_as_place(&statement.restored_place)?;
                let restored_root_address =
                    lowerer.extract_root_address(&statement.restored_place)?;
                let snapshot = statement.borrowing_place.to_procedure_snapshot(lowerer)?;
                let mut statements = vec![lowerer.call_restore_raw_borrowed_method(
                    CallContext::Procedure,
                    ty,
                    ty,
                    statement.position,
                    borrowing_address,
                    restored_place,
                    restored_root_address,
                    snapshot.clone(),
                )?];
                lowerer.encode_snapshot_update(
                    &mut statements,
                    &statement.restored_place,
                    snapshot,
                    statement.position,
                )?;
                Ok(statements)
            }
            Self::MovePlace(statement) => {
                // TODO: Remove code duplication with Self::CopyPlace
                let target_ty = statement.target.get_type();
                let source_ty = statement.source.get_type();
                let target_ty_without_lifetime = target_ty.clone().erase_lifetimes();
                let source_ty_without_lifetime = source_ty.clone().erase_lifetimes();
                assert_eq!(target_ty_without_lifetime, source_ty_without_lifetime);
                lowerer.encode_move_place_method(target_ty)?;
                let target_place = lowerer.encode_expression_as_place(&statement.target)?;
                let target_root_address = lowerer.extract_root_address(&statement.target)?;
                let source_place = lowerer.encode_expression_as_place(&statement.source)?;
                let source_root_address = lowerer.extract_root_address(&statement.source)?;
                // let source_snapshot = statement.source.to_procedure_snapshot(lowerer)?;
                let mut place_encoder =
                    ProcedureExpressionToSnapshot::for_place(PredicateKind::Owned);
                let source_snapshot =
                    place_encoder.expression_to_snapshot(lowerer, &statement.source, false)?;
                let mut statements = Vec::new();
                lowerer.encode_snapshot_update(
                    &mut statements,
                    &statement.target,
                    source_snapshot.clone(),
                    statement.position,
                )?;
                statements.push(lowerer.call_move_place_method(
                    CallContext::Procedure,
                    target_ty,
                    target_ty,
                    statement.position,
                    target_place,
                    target_root_address,
                    source_place,
                    source_root_address,
                    source_snapshot.clone(),
                )?);
                Ok(statements)
            }
            Self::CopyPlace(statement) => {
                // TODO: Remove code duplication with Self::MovePlace
                let target_ty = statement.target.get_type();
                let source_ty = statement.source.get_type();
                assert_eq!(target_ty, source_ty);
                lowerer.encode_copy_place_method(target_ty)?;
                let target_place = lowerer.encode_expression_as_place(&statement.target)?;
                let target_root_address = lowerer.extract_root_address(&statement.target)?;
                let source_place = lowerer.encode_expression_as_place(&statement.source)?;
                let source_root_address = lowerer.extract_root_address(&statement.source)?;
                let source_permission_amount =
                    if let Some(source_permission) = statement.source_permission {
                        source_permission.to_procedure_snapshot(lowerer)?.into()
                    } else {
                        vir_low::Expression::full_permission()
                    };
                // let source_snapshot = statement.source.to_procedure_snapshot(lowerer)?;
                let mut place_encoder =
                    ProcedureExpressionToSnapshot::for_place(PredicateKind::Owned);
                let source_snapshot =
                    place_encoder.expression_to_snapshot(lowerer, &statement.source, false)?;
                let mut statements = Vec::new();
                lowerer.encode_snapshot_update(
                    &mut statements,
                    &statement.target,
                    source_snapshot.clone(),
                    statement.position,
                )?;
                statements.push(lowerer.call_copy_place_method(
                    CallContext::Procedure,
                    target_ty,
                    target_ty,
                    statement.position,
                    target_place,
                    target_root_address,
                    source_place,
                    source_root_address,
                    source_snapshot.clone(),
                    source_permission_amount,
                )?);
                Ok(statements)
            }
            Self::WritePlace(statement) => {
                let target_ty = statement.target.get_type();
                let source_ty = statement.value.get_type();
                assert_eq!(target_ty, source_ty);
                lowerer.encode_write_place_constant_method(target_ty)?;
                let target_place = lowerer.encode_expression_as_place(&statement.target)?;
                let target_root_address = lowerer.extract_root_address(&statement.target)?;
                let source_snapshot = statement.value.to_procedure_snapshot(lowerer)?;
                let mut statements = vec![lowerer.call_write_place_constant_method(
                    CallContext::Procedure,
                    target_ty,
                    target_ty,
                    statement.position,
                    target_place,
                    target_root_address,
                    source_snapshot.clone(),
                )?];
                lowerer.encode_snapshot_update(
                    &mut statements,
                    &statement.target,
                    source_snapshot,
                    statement.position,
                )?;
                Ok(statements)
            }
            Self::WriteAddress(statement) => {
                let target_ty = statement.target.get_type();
                let source_ty = statement.value.get_type();
                assert_eq!(target_ty, source_ty);
                lowerer.encode_write_address_constant_method(target_ty)?;
                let target_address =
                    lowerer.encode_expression_as_place_address(&statement.target)?;
                let value = statement.value.to_procedure_snapshot(lowerer)?;
                let statements = vec![stmtp! { statement.position =>
                    call write_address_constant<target_ty>(
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
            Self::SetUnionVariant(statement) => {
                let variant_place = statement.variant_place.get_parent_ref().unwrap();
                // FIXME: Implement a macro that takes a reference to avoid clonning.
                let variant_index = variant_place.clone().unwrap_variant().variant_index;
                let union_place = variant_place.get_parent_ref().unwrap();
                let mut statements = Vec::new();
                lowerer.encode_snapshot_havoc(&mut statements, union_place, statement.position)?;
                let snapshot = union_place.to_procedure_snapshot(lowerer)?;
                let discriminant = lowerer.obtain_enum_discriminant(
                    snapshot,
                    union_place.get_type(),
                    statement.position,
                )?;
                let type_decl = lowerer.encoder.get_type_decl_mid(union_place.get_type())?;
                let union_decl = type_decl.unwrap_enum();
                assert!(union_decl.safety.is_union());
                let discriminant_value =
                    union_decl.get_discriminant(&variant_index).unwrap().into();
                statements.push(stmtp! { statement.position =>
                assume ([discriminant] == [discriminant_value]) });
                Ok(statements)
            }
            Self::GhostAssign(statement) => {
                let mut stmts = Vec::new();
                let value = statement.value.to_procedure_snapshot(lowerer)?;
                lowerer.encode_snapshot_update(
                    &mut stmts,
                    &statement.target,
                    value,
                    statement.position,
                )?;
                Ok(stmts)
            }
            Self::StashRange(statement) => {
                let ty = statement.address.get_type();
                let pointer_value = statement.address.to_procedure_snapshot(lowerer)?;
                let start_index = statement.start_index.to_procedure_snapshot(lowerer)?;
                let end_index = statement.end_index.to_procedure_snapshot(lowerer)?;
                let mut statements = Vec::new();
                lowerer.encode_stash_range_call(
                    &mut statements,
                    ty,
                    pointer_value,
                    start_index,
                    end_index,
                    statement.label,
                    statement.position,
                )?;
                Ok(statements)
            }
            Self::StashRangeRestore(statement) => {
                assert_eq!(
                    statement.old_address.get_type(),
                    statement.new_address.get_type()
                );
                let ty = statement.old_address.get_type();
                let old_pointer_value = statement.old_address.to_procedure_snapshot(lowerer)?;
                let old_start_index = statement.old_start_index.to_procedure_snapshot(lowerer)?;
                let old_end_index = statement.old_end_index.to_procedure_snapshot(lowerer)?;
                let new_address = statement.new_address.to_procedure_snapshot(lowerer)?;
                let new_start_index = statement.new_start_index.to_procedure_snapshot(lowerer)?;
                let mut statements = Vec::new();
                lowerer.encode_restore_stash_range_call(
                    &mut statements,
                    ty,
                    old_pointer_value,
                    old_start_index,
                    old_end_index,
                    statement.old_label,
                    new_address,
                    new_start_index,
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
            Self::DeadReference(statement) => {
                let ty = statement.target.get_type();
                let (lifetime, uniqueness) = statement.target.get_dereference_kind().unwrap();
                let lifetime = lowerer.encode_lifetime_const_into_procedure_variable(lifetime)?;
                let place = lowerer.encode_expression_as_place(&statement.target)?;
                let root_address = lowerer.extract_root_address(&statement.target)?;
                let current_snapshot = statement.target.to_procedure_snapshot(lowerer)?;
                // TODO: These should be method calls.
                let statements = match uniqueness {
                    vir_mid::ty::Uniqueness::Unique => {
                        let final_snapshot =
                            statement.target.to_procedure_final_snapshot(lowerer)?;
                        let predicate = lowerer.unique_ref(
                            CallContext::Procedure,
                            ty,
                            ty,
                            place,
                            root_address,
                            current_snapshot.clone(),
                            final_snapshot.clone(),
                            lifetime.into(),
                            None, // FIXME: This should be a proper value
                        )?;
                        lowerer.mark_unique_ref_as_used(ty)?;
                        let mut statements = vec![
                            vir_low::Statement::comment(format!(
                                "dead reference: {}",
                                statement.target
                            )),
                            vir_low::Statement::exhale_no_pos(predicate)
                                .set_default_position(statement.position),
                            stmtp! {
                                statement.position =>
                                assume ([current_snapshot] == [final_snapshot])
                            },
                        ];
                        if let Some(condition) = statement.condition {
                            let low_condition = lowerer.lower_block_marker_condition(condition)?;
                            statements = vec![Statement::conditional(
                                low_condition,
                                statements,
                                Vec::new(),
                                statement.position,
                            )];
                        }
                        statements
                    }
                    vir_mid::ty::Uniqueness::Shared => {
                        let predicate = lowerer.frac_ref(
                            CallContext::Procedure,
                            ty,
                            ty,
                            place,
                            root_address,
                            current_snapshot,
                            lifetime.into(),
                        )?;
                        let low_statement = vir_low::Statement::exhale_no_pos(predicate)
                            .set_default_position(statement.position);
                        if let Some(condition) = statement.condition {
                            let low_condition = lowerer.lower_block_marker_condition(condition)?;
                            vec![Statement::conditional(
                                low_condition,
                                vec![low_statement],
                                Vec::new(),
                                statement.position,
                            )]
                        } else {
                            vec![low_statement]
                        }
                    }
                };
                Ok(statements)
            }
            Self::DeadLifetime(_statement) => {
                // TODO: This should resolve the lifetime for statement.target
                // instead of just marking the lifetime as dead. Once that is
                // done, we can mark the lifetime as not alive anymore.
                let statements = Vec::new();
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
                let lifetime =
                    lowerer.encode_lifetime_const_into_procedure_variable(statement.lifetime)?;
                let perm_amount = statement
                    .lifetime_token_permission
                    .to_procedure_snapshot(lowerer)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let targets = vec![statement
                    .predicate_permission_amount
                    .to_procedure_snapshot(lowerer)?
                    .into()];
                let mut arguments = vec![lifetime.into(), perm_amount, place, address];
                if lowerer.check_mode.unwrap() == CheckMode::PurificationSoudness {
                    let current_snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                    arguments.push(current_snapshot);
                }
                Ok(vec![Statement::method_call(
                    method_name!(frac_bor_atomic_acc<ty>),
                    arguments,
                    targets,
                    statement.position,
                )])
            }
            Self::CloseFracRef(statement) => {
                let ty = statement.place.get_type();
                let lifetime =
                    lowerer.encode_lifetime_const_into_procedure_variable(statement.lifetime)?;
                let perm_amount = statement
                    .lifetime_token_permission
                    .to_procedure_snapshot(lowerer)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let root_address = lowerer.extract_root_address(&statement.place)?;
                let tmp_frac_ref_perm = statement
                    .predicate_permission_amount
                    .to_procedure_snapshot(lowerer)?;
                let owned_predicate = lowerer.owned_non_aliased_predicate(
                    CallContext::Procedure,
                    ty,
                    ty,
                    place.clone(),
                    root_address.clone(),
                    true.into(), // FIXME: Not used.
                    Some(tmp_frac_ref_perm.into()),
                )?;
                let current_snapshot =
                    if lowerer.check_mode.unwrap() == CheckMode::PurificationSoudness {
                        Some(statement.place.to_procedure_snapshot(lowerer)?)
                    } else {
                        None
                    };
                let frac_predicate = lowerer.frac_ref_opt(
                    CallContext::Procedure,
                    ty,
                    ty,
                    place,
                    root_address,
                    current_snapshot,
                    lifetime.clone().into(),
                )?;
                Ok(vec![stmtp! {
                    statement.position =>
                    apply (
                        [owned_predicate]
                    ) --* (
                        (acc(LifetimeToken(lifetime), [perm_amount])) &&
                        [frac_predicate]
                    )
                }])
            }
            Self::OpenMutRef(statement) => {
                let ty = statement.place.get_type();
                lowerer.encode_open_close_mut_ref_methods(ty)?;
                let lifetime =
                    lowerer.encode_lifetime_const_into_procedure_variable(statement.lifetime)?;
                let perm_amount = statement
                    .lifetime_token_permission
                    .to_procedure_snapshot(lowerer)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let mut place_encoder =
                    ProcedureExpressionToSnapshot::for_place(PredicateKind::UniqueRef {
                        lifetime: lifetime.clone().into(),
                        is_final: false,
                    });
                let current_snapshot =
                    place_encoder.expression_to_snapshot(lowerer, &statement.place, false)?;
                // let current_snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                // let final_snapshot = statement.place.to_procedure_final_snapshot(lowerer)?;
                let mut place_encoder =
                    ProcedureExpressionToSnapshot::for_place(PredicateKind::UniqueRef {
                        lifetime: lifetime.clone().into(),
                        is_final: true,
                    });
                let final_snapshot =
                    place_encoder.expression_to_snapshot(lowerer, &statement.place, false)?;
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
                let lifetime =
                    lowerer.encode_lifetime_const_into_procedure_variable(statement.lifetime)?;
                let perm_amount = statement
                    .lifetime_token_permission
                    .to_procedure_snapshot(lowerer)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                // let current_snapshot = statement.place.to_procedure_snapshot(lowerer)?;
                // let final_snapshot = statement.place.to_procedure_final_snapshot(lowerer)?;
                let mut place_encoder =
                    ProcedureExpressionToSnapshot::for_place(PredicateKind::Owned);
                let current_snapshot =
                    place_encoder.expression_to_snapshot(lowerer, &statement.place, false)?;
                let mut place_encoder =
                    ProcedureExpressionToSnapshot::for_place(PredicateKind::UniqueRef {
                        lifetime: lifetime.clone().into(),
                        is_final: true,
                    });
                let final_snapshot =
                    place_encoder.expression_to_snapshot(lowerer, &statement.place, false)?;
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
                let lifetime = lowerer
                    .encode_lifetime_const_into_procedure_variable(statement.lifetime.clone())?;
                let old_lifetime = lowerer.encode_lifetime_const_into_procedure_variable(
                    statement.old_lifetime.clone(),
                )?;
                let reference_place = lowerer.encode_expression_as_place(&statement.value)?;
                let deref_place =
                    lowerer.reference_deref_place(reference_place, statement.position)?;
                let reference_value = statement.value.to_procedure_snapshot(lowerer)?;
                let root_address =
                    lowerer.reference_address(ty, reference_value.clone(), statement.position)?;
                let current_snapshot = lowerer.reference_target_current_snapshot(
                    ty,
                    reference_value.clone(),
                    statement.position,
                )?;
                assert!(ty.is_reference(), "{:?}", ty);
                let reference = ty.clone().unwrap_reference();
                let final_snapshot = if reference.uniqueness.is_unique() {
                    Some(lowerer.reference_target_final_snapshot(
                        ty,
                        reference_value,
                        statement.position,
                    )?)
                } else {
                    None
                };
                let statements = vec![lowerer.call_bor_shorten(
                    CallContext::Procedure,
                    ty,
                    &*reference.target_type,
                    statement.position,
                    deref_place,
                    root_address,
                    current_snapshot,
                    final_snapshot,
                    lifetime.into(),
                    old_lifetime.into(),
                    perm_amount,
                )?];
                Ok(statements)
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
                let lifetime =
                    lowerer.encode_lifetime_const_into_procedure_variable(predicate.lifetime)?;
                let permission = predicate.permission.to_procedure_snapshot(lowerer)?;
                expr! { acc(LifetimeToken([lifetime.into()]), [permission])}
                    .set_default_position(predicate.position)
            }
            Predicate::MemoryBlockStack(predicate) => {
                lowerer.encode_memory_block_predicate()?;
                let place = lowerer.encode_expression_as_place_address(&predicate.place)?;
                let size = predicate.size.to_procedure_snapshot(lowerer)?;
                lowerer.encode_memory_block_stack_acc(place, size, predicate.position)?
            }
            Predicate::MemoryBlockStackDrop(predicate) => {
                let place = lowerer.encode_expression_as_place_address(&predicate.place)?;
                let size = predicate.size.to_procedure_snapshot(lowerer)?;
                lowerer.encode_memory_block_stack_drop_acc(place, size, predicate.position)?
            }
            Predicate::MemoryBlockHeap(predicate) => {
                unimplemented!("predicate: {}", predicate);
            }
            Predicate::MemoryBlockHeapRange(predicate) => {
                unimplemented!("predicate: {}", predicate);
            }
            Predicate::MemoryBlockHeapDrop(predicate) => {
                unimplemented!("predicate: {}", predicate);
            }
            Predicate::OwnedNonAliased(predicate) => {
                let place = lowerer.encode_expression_as_place(&predicate.place)?;
                let root_address = lowerer.extract_root_address(&predicate.place)?;
                let snapshot = predicate.place.to_procedure_snapshot(lowerer)?;
                let ty = predicate.place.get_type();
                let valid = lowerer.encode_snapshot_valid_call_for_type(snapshot.clone(), ty)?;
                let low_predicate = lowerer.owned_non_aliased(
                    CallContext::Procedure,
                    ty,
                    ty,
                    place,
                    root_address,
                    snapshot,
                    None,
                )?;
                exprp! {
                    predicate.position =>
                    [low_predicate] &&
                    [valid]
                }
            }
            Predicate::OwnedRange(_) => todo!(),
            Predicate::OwnedSet(_) => todo!(),
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
