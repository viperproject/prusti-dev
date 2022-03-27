use super::{IntoLow, IntoLowInterface};
use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        block_markers::BlockMarkersInterface,
        builtin_methods::BuiltinMethodsInterface,
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates_memory_block::PredicatesMemoryBlockInterface,
        predicates_owned::PredicatesOwnedInterface,
        snapshots::{
            IntoSnapshot, SnapshotValidityInterface, SnapshotValuesInterface,
            SnapshotVariablesInterface,
        },
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low, operations::ToLow},
    middle::{self as vir_mid, operations::ty::Typed},
};

impl IntoLow for vir_mid::FunctionDecl {
    type Target = vir_low::FunctionDecl;
    fn into_low<'p, 'v: 'p, 'tcx: 'v>(
        self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        Ok(vir_low::FunctionDecl {
            name: self.get_identifier(),
            parameters: self.parameters.into_low(lowerer)?,
            return_type: self.return_type.into_low(lowerer)?,
            pres: self.pres.into_low(lowerer)?,
            posts: self.posts.into_low(lowerer)?,
            body: self.body.into_low(lowerer)?,
        })
    }
}

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

impl<S: IntoLow> IntoLow for Option<S> {
    type Target = Option<<S as IntoLow>::Target>;
    fn into_low<'p, 'v: 'p, 'tcx: 'v>(
        self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        self.map(|decl| decl.into_low(lowerer)).transpose()
    }
}

impl IntoLow for vir_mid::VariableDecl {
    type Target = vir_low::VariableDecl;
    fn into_low<'p, 'v: 'p, 'tcx: 'v>(
        self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        Ok(vir_low::VariableDecl {
            name: self.name,
            ty: self.ty.into_low(lowerer)?,
        })
    }
}

impl IntoLow for vir_mid::Type {
    type Target = vir_low::Type;
    fn into_low<'p, 'v: 'p, 'tcx: 'v>(
        self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        lowerer.lower_type(self)
    }
}

impl IntoLow for vir_mid::Expression {
    type Target = vir_low::Expression;
    fn into_low<'p, 'v: 'p, 'tcx: 'v>(
        self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        IntoLowInterface::lower_expression(lowerer, self)
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
            Self::Inhale(statement) => Ok(vec![Statement::inhale(
                statement.predicate.into_low(lowerer)?,
                statement.position,
            )]),
            Self::Exhale(statement) => Ok(vec![Statement::exhale(
                statement.predicate.into_low(lowerer)?,
                statement.position,
            )]),
            Self::Assert(statement) => Ok(vec![Statement::assert(
                statement.expression.into_low(lowerer)?,
                statement.position,
            )]),
            Self::FoldOwned(statement) => {
                let ty = statement.place.get_type();
                lowerer.mark_owned_non_aliased_as_unfolded(ty)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let snapshot = lowerer.lower_expression_into_snapshot(&statement.place)?;
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
                let snapshot = lowerer.lower_expression_into_snapshot(&statement.place)?;
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
                        vir_mid::TypeDecl::Enum(decl) => Some(
                            decl.get_discriminant(variant_index)
                                .unwrap()
                                .clone()
                                .to_low(lowerer)?,
                        ),
                        vir_mid::TypeDecl::Union(decl) => Some(
                            decl.get_discriminant(variant_index)
                                .unwrap()
                                .clone()
                                .to_low(lowerer)?,
                        ),
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
                    let enum_decl = type_decl.unwrap_enum();
                    Some(
                        enum_decl
                            .get_discriminant(variant_index)
                            .unwrap()
                            .clone()
                            .to_low(lowerer)?,
                    )
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
                let snapshot = lowerer.lower_expression_into_snapshot(&statement.place)?;
                let low_statement = if let Some(condition) = statement.condition {
                    let low_condition = lowerer.lower_block_marker_condition(condition)?;
                    stmtp! {
                        statement.position =>
                        call<low_condition> into_memory_block<ty>([place], [address], [snapshot])
                    }
                } else {
                    stmtp! {
                        statement.position =>
                        call into_memory_block<ty>([place], [address], [snapshot])
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
                let value = lowerer.lower_expression_into_snapshot(&statement.source)?;
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
                let value = lowerer.lower_expression_into_snapshot(&statement.source)?;
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
                let value = lowerer.lower_expression_into_snapshot(&statement.value)?;
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
                let value = lowerer.lower_expression_into_snapshot(&statement.value)?;
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
                let size = predicate.size.into_low(lowerer)?;
                expr! { acc(MemoryBlock([place], [size]))}.set_default_position(predicate.position)
            }
            Predicate::MemoryBlockStackDrop(predicate) => {
                let place = lowerer.encode_expression_as_place_address(&predicate.place)?;
                let size = predicate.size.into_low(lowerer)?;
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
                let snapshot = lowerer.lower_expression_into_snapshot(&predicate.place)?;
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
                    let test_snapshot = test.create_snapshot(lowerer)?;
                    let test_low = lowerer.obtain_constant_value(
                        test.get_type(),
                        test_snapshot,
                        Default::default(),
                    )?;
                    new_targets.push((test_low, target.into_low(lowerer)?))
                }
                Ok(vir_low::Successor::GotoSwitch(new_targets))
            }
        }
    }
}
