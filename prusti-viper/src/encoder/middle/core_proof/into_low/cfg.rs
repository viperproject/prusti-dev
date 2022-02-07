use super::{IntoLow, IntoLowInterface};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface, builtin_methods::BuiltinMethodsInterface, lowerer::Lowerer,
        places::PlacesInterface, predicates_memory_block::PredicatesMemoryBlockInterface,
        predicates_owned::PredicatesOwnedInterface, snapshots::SnapshotsInterface,
    },
};

use vir_crate::{
    common::identifier::WithIdentifier,
    low as vir_low,
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
            Self::FoldOwned(statement) => {
                let ty = statement.place.get_type();
                lowerer.mark_owned_non_aliased_as_unfolded(ty)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let snapshot = lowerer.lower_expression_into_snapshot(&statement.place)?;
                let low_statement = stmtp! {
                    statement.position => fold OwnedNonAliased<ty>([place], [address], [snapshot])
                };
                Ok(vec![low_statement])
            }
            Self::UnfoldOwned(statement) => {
                let ty = statement.place.get_type();
                lowerer.mark_owned_non_aliased_as_unfolded(ty)?;
                let place = lowerer.encode_expression_as_place(&statement.place)?;
                let address = lowerer.extract_root_address(&statement.place)?;
                let snapshot = lowerer.lower_expression_into_snapshot(&statement.place)?;
                let low_statement = stmtp! {
                    statement.position => unfold OwnedNonAliased<ty>([place], [address], [snapshot])
                };
                Ok(vec![low_statement])
            }
            Self::JoinBlock(statement) => {
                let ty = statement.place.get_type();
                lowerer.encode_memory_block_join_method(ty)?;
                let address = lowerer.encode_expression_as_place_address(&statement.place)?;
                let low_statement = stmtp! {
                    statement.position => call memory_block_join<ty>([address])
                };
                Ok(vec![low_statement])
            }
            Self::SplitBlock(statement) => {
                let ty = statement.place.get_type();
                lowerer.encode_memory_block_split_method(ty)?;
                let address = lowerer.encode_expression_as_place_address(&statement.place)?;
                let low_statement = stmtp! {
                    statement.position => call memory_block_split<ty>([address])
                };
                Ok(vec![low_statement])
            }
            Self::MovePlace(statement) => {
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
            Self::CopyPlace(_statement) => {
                unimplemented!();
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
            vir_mid::Successor::Return => Ok(vir_low::Successor::Return),
            vir_mid::Successor::Goto(target) => {
                Ok(vir_low::Successor::Goto(target.into_low(lowerer)?))
            }
            vir_mid::Successor::GotoSwitch(targets) => {
                let mut new_targets = Vec::new();
                for (test, target) in targets {
                    new_targets.push((test.into_low(lowerer)?, target.into_low(lowerer)?))
                }
                Ok(vir_low::Successor::GotoSwitch(new_targets))
            }
        }
    }
}
