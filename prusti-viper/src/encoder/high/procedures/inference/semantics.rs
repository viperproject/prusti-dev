use super::permission::{Blocked, Permission};
use crate::encoder::{
    errors::SpannedEncodingResult, high::to_typed::types::HighToTypedTypeEncoderInterface, Encoder,
};
use vir_crate::{
    common::{builtin_constants::ADDRESS_FIELD_NAME, position::Positioned},
    typed::{self as vir_typed, operations::ty::Typed},
};

pub(in super::super) fn collect_permission_changes<'v, 'tcx>(
    encoder: &mut Encoder<'v, 'tcx>,
    statement: &vir_typed::Statement,
) -> SpannedEncodingResult<(Vec<Permission>, Vec<Permission>)> {
    let mut consumed_permissions = Vec::new();
    let mut produced_permissions = Vec::new();
    statement.collect(
        encoder,
        &mut consumed_permissions,
        &mut produced_permissions,
    )?;
    consumed_permissions.retain(|permission| !permission.place().is_behind_pointer_dereference());
    produced_permissions.retain(|permission| !permission.place().is_behind_pointer_dereference());
    // remove_after_pointer_deref(&mut consumed_permissions);
    // remove_after_pointer_deref(&mut produced_permissions);
    Ok((consumed_permissions, produced_permissions))
}

// fn remove_after_pointer_deref(permissions: &mut Vec<Permission>) {
//     permissions.retain_mut(|permission| {
//         match permission {
//             Permission::MemoryBlock(place) => {
//                 !place.is_behind_pointer_dereference()
//             }
//             Permission::Owned(place) => {
//                 if let Some(pointer_place) = place.get_first_dereferenced_pointer() {
//                     *place = pointer_place.clone();
//                 }
//                 true
//             }
//             Permission::Blocked(_) => unreachable!(),
//         }
//     });
// }

trait CollectPermissionChanges {
    #[allow(clippy::ptr_arg)] // Clippy false positive.
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()>;
}

impl CollectPermissionChanges for vir_typed::Statement {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        match self {
            vir_typed::Statement::Comment(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::OldLabel(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::InhalePredicate(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::ExhalePredicate(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::InhaleExpression(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::ExhaleExpression(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::Consume(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::Havoc(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::GhostHavoc(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::HeapHavoc(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::GhostAssign(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::Assume(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::Assert(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::LoopInvariant(_) => {
                unreachable!("LoopInvariant statement should have been removed before.");
            }
            vir_typed::Statement::MovePlace(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::CopyPlace(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::WritePlace(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::WriteAddress(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::Assign(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::LeakAll(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::SetUnionVariant(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::Pack(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::Unpack(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::Obtain(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::Join(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::JoinRange(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::Split(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::SplitRange(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::StashRange(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::StashRangeRestore(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::ForgetInitialization(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::ForgetInitializationRange(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::RestoreRawBorrowed(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::NewLft(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::EndLft(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::DeadReference(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::DeadReferenceRange(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::DeadLifetime(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::DeadInclusion(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::LifetimeTake(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::ObtainMutRef(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::OpenMutRef(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::OpenFracRef(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::CloseMutRef(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::CloseFracRef(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::BorShorten(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::LifetimeReturn(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_typed::Statement::MaterializePredicate(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
        }
    }
}

impl CollectPermissionChanges for vir_typed::HeapHavoc {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::GhostHavoc {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::GhostAssign {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        // Ghost Assign should work without permissions
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::Comment {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        // No requirements and nothing ensured.
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::OldLabel {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        // No requirements and nothing ensured.
        Ok(())
    }
}

fn extract_managed_predicate_place(
    predicate: &vir_typed::Predicate,
) -> SpannedEncodingResult<Option<Permission>> {
    match predicate {
        vir_typed::Predicate::MemoryBlockStack(predicate) => {
            Ok(Some(Permission::MemoryBlock(predicate.place.clone())))
        }
        vir_typed::Predicate::OwnedNonAliased(predicate) => {
            Ok(Some(Permission::Owned(predicate.place.clone())))
        }
        vir_typed::Predicate::UniqueRef(predicate) => {
            Ok(Some(Permission::Owned(predicate.place.clone())))
        }
        vir_typed::Predicate::FracRef(predicate) => {
            Ok(Some(Permission::Owned(predicate.place.clone())))
        }
        vir_typed::Predicate::MemoryBlockStackDrop(_)
        | vir_typed::Predicate::LifetimeToken(_)
        | vir_typed::Predicate::MemoryBlockHeap(_)
        | vir_typed::Predicate::MemoryBlockHeapRange(_)
        | vir_typed::Predicate::MemoryBlockHeapDrop(_)
        | vir_typed::Predicate::OwnedRange(_)
        | vir_typed::Predicate::OwnedSet(_)
        | vir_typed::Predicate::UniqueRefRange(_)
        | vir_typed::Predicate::FracRefRange(_) => {
            // Unmanaged predicates.
            Ok(None)
        }
    }
}

impl CollectPermissionChanges for vir_typed::InhalePredicate {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        produced_permissions.extend(extract_managed_predicate_place(&self.predicate)?);
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ExhalePredicate {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.extend(extract_managed_predicate_place(&self.predicate)?);
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::InhaleExpression {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ExhaleExpression {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::Consume {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        self.operand
            .collect(encoder, consumed_permissions, produced_permissions)?;
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::Havoc {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.extend(extract_managed_predicate_place(&self.predicate)?);
        produced_permissions.extend(extract_managed_predicate_place(&self.predicate)?);
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::Assume {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::Assert {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::MovePlace {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::MemoryBlock(self.target.clone()));
        consumed_permissions.push(Permission::Owned(self.source.clone()));
        produced_permissions.push(Permission::Owned(self.target.clone()));
        produced_permissions.push(Permission::MemoryBlock(self.source.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::CopyPlace {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        // if let Some(source_pointer_place) = self.source.get_first_dereferenced_pointer() {

        // }
        consumed_permissions.push(Permission::MemoryBlock(self.target.clone()));
        consumed_permissions.push(Permission::Owned(self.source.clone()));
        produced_permissions.push(Permission::Owned(self.target.clone()));
        produced_permissions.push(Permission::Owned(self.source.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::WritePlace {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::MemoryBlock(self.target.clone()));
        produced_permissions.push(Permission::Owned(self.target.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::WriteAddress {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        todo!();
    }
}

impl CollectPermissionChanges for vir_typed::Assign {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::MemoryBlock(self.target.clone()));
        if let vir_typed::Rvalue::CheckedBinaryOp(_value) = &self.value {
            let type_decl = encoder
                .encode_type_def_typed(self.target.get_type())?
                .unwrap_struct();
            let (operation_result_field, flag_field) = {
                let mut iter = type_decl.fields.iter();
                (iter.next().unwrap().clone(), iter.next().unwrap().clone())
            };
            produced_permissions.push(Permission::Owned(
                self.target
                    .clone()
                    .field(flag_field, self.target.position()),
            ));
            produced_permissions.push(Permission::MemoryBlock(
                self.target
                    .clone()
                    .field(operation_result_field, self.target.position()),
            ));
        } else {
            produced_permissions.push(Permission::Owned(self.target.clone()));
        }
        self.value
            .collect(encoder, consumed_permissions, produced_permissions)
    }
}

impl CollectPermissionChanges for vir_typed::Rvalue {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        match self {
            Self::Repeat(rvalue) => {
                rvalue.collect(encoder, consumed_permissions, produced_permissions)
            }
            Self::Reborrow(rvalue) => {
                rvalue.collect(encoder, consumed_permissions, produced_permissions)
            }
            Self::Ref(rvalue) => {
                rvalue.collect(encoder, consumed_permissions, produced_permissions)
            }
            Self::AddressOf(rvalue) => {
                rvalue.collect(encoder, consumed_permissions, produced_permissions)
            }
            Self::Len(rvalue) => {
                rvalue.collect(encoder, consumed_permissions, produced_permissions)
            }
            Self::Cast(rvalue) => {
                rvalue.collect(encoder, consumed_permissions, produced_permissions)
            }
            Self::UnaryOp(rvalue) => {
                rvalue.collect(encoder, consumed_permissions, produced_permissions)
            }
            Self::BinaryOp(rvalue) => {
                rvalue.collect(encoder, consumed_permissions, produced_permissions)
            }
            Self::CheckedBinaryOp(rvalue) => {
                rvalue.collect(encoder, consumed_permissions, produced_permissions)
            }
            Self::Discriminant(rvalue) => {
                rvalue.collect(encoder, consumed_permissions, produced_permissions)
            }
            Self::Aggregate(rvalue) => {
                rvalue.collect(encoder, consumed_permissions, produced_permissions)
            }
        }
    }
}

impl CollectPermissionChanges for vir_typed::ast::rvalue::Repeat {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        self.argument
            .collect(encoder, consumed_permissions, produced_permissions)?;
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ast::rvalue::Reborrow {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::Owned(self.deref_place.clone()));
        if self
            .deref_place
            .get_deref_uniqueness()
            .unwrap_or(self.uniqueness)
            .is_unique()
        {
            produced_permissions.push(Permission::Blocked(Blocked {
                lifetime: self.new_borrow_lifetime.clone(),
                place: self.deref_place.clone(),
                is_reborrow: true,
            }));
        } else {
            produced_permissions.push(Permission::Owned(self.deref_place.clone()));
        }
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ast::rvalue::Ref {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::Owned(self.place.clone()));
        produced_permissions.push(Permission::Blocked(Blocked {
            lifetime: self.new_borrow_lifetime.clone(),
            place: self.place.clone(),
            is_reborrow: false,
        }));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ast::rvalue::AddressOf {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        // To take an address of a place on a stack, it must not be moved out.
        // The following fails to compile:
        // ```rust
        // struct T {
        //     g: u32,
        // }
        // struct G {
        //     f: T,
        // }
        // fn test1() {
        //     let a = 4u32;
        //     let b = T { g: a };
        //     let c = G { f: b };
        //     let _d = c.f;
        //     let _x = std::ptr::addr_of!(c);
        // }
        // ```
        consumed_permissions.push(Permission::Owned(self.place.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ast::rvalue::Len {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::Owned(self.place.clone()));
        produced_permissions.push(Permission::Owned(self.place.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ast::rvalue::Cast {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        self.operand
            .collect(encoder, consumed_permissions, produced_permissions)?;
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ast::rvalue::UnaryOp {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        self.argument
            .collect(encoder, consumed_permissions, produced_permissions)
    }
}

impl CollectPermissionChanges for vir_typed::ast::rvalue::BinaryOp {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        self.left
            .collect(encoder, consumed_permissions, produced_permissions)?;
        self.right
            .collect(encoder, consumed_permissions, produced_permissions)?;
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ast::rvalue::CheckedBinaryOp {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        self.left
            .collect(encoder, consumed_permissions, produced_permissions)?;
        self.right
            .collect(encoder, consumed_permissions, produced_permissions)?;
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ast::rvalue::Discriminant {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        unreachable!("Discriminants should be special-cased.");
    }
}

impl CollectPermissionChanges for vir_typed::ast::rvalue::Aggregate {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        for operand in &self.operands {
            operand.collect(encoder, consumed_permissions, produced_permissions)?;
        }
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ast::rvalue::Operand {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        use vir_typed::ast::rvalue::OperandKind::*;
        match self.kind {
            Copy => {
                consumed_permissions.push(Permission::Owned(self.expression.clone()));
                produced_permissions.push(Permission::Owned(self.expression.clone()));
            }
            Move => {
                consumed_permissions.push(Permission::Owned(self.expression.clone()));
                produced_permissions.push(Permission::MemoryBlock(self.expression.clone()));
            }
            Constant => {}
        }
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::LeakAll {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::SetUnionVariant {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        // FIXME: The place is provided by the user. Therefore, instead of just
        // unwrapping we should check that we got the variant of an union and
        // report an error if that is not the case.
        let parent = self
            .variant_place
            .get_parent_ref()
            .unwrap()
            .get_parent_ref()
            .unwrap();
        consumed_permissions.push(Permission::MemoryBlock(parent.clone()));
        produced_permissions.push(Permission::MemoryBlock(self.variant_place.clone()));
        Ok(())
    }
}

fn add_struct_expansion(
    place: &vir_typed::Expression,
    fields: Vec<vir_typed::FieldDecl>,
    permissions: &mut Vec<Permission>,
) {
    let position = place.position();
    for field in fields {
        permissions.push(Permission::Owned(vir_typed::Expression::field(
            place.clone(),
            field,
            position,
        )));
    }
}

impl CollectPermissionChanges for vir_typed::Pack {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        if self.place.is_behind_pointer_dereference() {
            produced_permissions.push(Permission::Owned(self.place.clone()));
        } else {
            let type_decl = encoder.encode_type_def_typed(self.place.get_type())?;
            match type_decl {
                vir_typed::TypeDecl::Struct(decl) => {
                    // if decl.is_manually_managed_type() {
                    produced_permissions.push(Permission::Owned(self.place.clone()));
                    add_struct_expansion(&self.place, decl.fields, consumed_permissions);
                    // } else {
                    //     produced_permissions.push(Permission::Owned(self.place.clone()));
                    //     add_struct_expansion(&self.place, decl.fields, consumed_permissions);
                    //     // unimplemented!(
                    //     //     "Unpacking an automatically managed type: {}\n{}",
                    //     //     self.place,
                    //     //     self.place.get_type(),
                    //     // );
                    // }
                }
                vir_typed::TypeDecl::Reference(_) => {
                    // FIXME: Code duplication with
                    // prusti-viper/src/encoder/high/procedures/inference/visitor/context.rs
                    produced_permissions.push(Permission::Owned(self.place.clone()));
                    let ty = self.place.get_type();
                    let target_type = ty.clone().unwrap_reference().target_type;
                    let deref_place = vir_typed::Expression::deref(
                        self.place.clone(),
                        *target_type,
                        self.place.position(),
                    );
                    let address_place = vir_typed::Expression::field(
                        self.place.clone(),
                        vir_typed::FieldDecl::new(
                            ADDRESS_FIELD_NAME,
                            0usize,
                            vir_typed::Type::Int(vir_typed::ty::Int::Usize),
                        ),
                        self.place.position(),
                    );
                    consumed_permissions.push(Permission::Owned(address_place));
                    consumed_permissions.push(Permission::Owned(deref_place));
                }
                _ => {
                    unimplemented!(
                        "Report a proper error message that only structs can be unfolded: {:?}",
                        self.place
                    );
                }
            }
        }
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::Unpack {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        if self.place.is_behind_pointer_dereference() {
            consumed_permissions.push(Permission::Owned(self.place.clone()));
        } else {
            let type_decl = encoder.encode_type_def_typed(self.place.get_type())?;
            if let vir_typed::TypeDecl::Struct(decl) = type_decl {
                if decl.is_manually_managed_type() {
                    consumed_permissions.push(Permission::Owned(self.place.clone()));
                    add_struct_expansion(&self.place, decl.fields, produced_permissions);
                } else {
                    consumed_permissions.push(Permission::Owned(self.place.clone()));
                    add_struct_expansion(&self.place, decl.fields, produced_permissions);
                    // unimplemented!(
                    //     "Unpacking an automatically managed type: {}\n{}",
                    //     self.place,
                    //     self.place.get_type()
                    // );
                }
            } else {
                unimplemented!(
                    "Report a proper error message that only structs can be unfolded: {}",
                    self.place
                );
            }
        }
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::Obtain {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::Owned(self.place.clone()));
        produced_permissions.push(Permission::Owned(self.place.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::Join {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        if !self.place.is_behind_pointer_dereference() {
            unimplemented!(
                "Report a proper error message that only memory blocks behind \
                a raw pointer could be joined by hand: {}",
                self.place
            );
        }
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::JoinRange {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::Split {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        if !self.place.is_behind_pointer_dereference() {
            unimplemented!(
                "Report a proper error message that only memory blocks behind \
                a raw pointer could be split by hand: {}",
                self.place
            );
        }
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::SplitRange {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::StashRange {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::StashRangeRestore {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ForgetInitialization {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        if self.place.is_behind_pointer_dereference() {
            consumed_permissions.push(Permission::Owned(self.place.clone()));
        } else {
            let type_decl = encoder.encode_type_def_typed(self.place.get_type())?;
            if let vir_typed::TypeDecl::Struct(decl) = &type_decl {
                if decl.is_manually_managed_type() {
                    consumed_permissions.push(Permission::Owned(self.place.clone()));
                } else {
                    unimplemented!(
                        "Forgetting initialization of an automatically managed type: {:?}\n{:?}",
                        self.place,
                        type_decl
                    );
                }
            } else {
                unimplemented!(
                    "Report a proper error message that only structs can be unfolded: {:?}",
                    self.place
                );
            }
        }
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ForgetInitializationRange {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::RestoreRawBorrowed {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        produced_permissions.push(Permission::Owned(self.restored_place.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::NewLft {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::EndLft {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::DeadReference {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::Owned(self.target.clone()));
        // // FIXME: This is a lie: the permission is actually gone, we should not
        // // require it.
        // produced_permissions.push(Permission::Owned(self.target.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::DeadReferenceRange {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::DeadLifetime {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        unreachable!("DeadLifetime is special cased in the caller");
    }
}

impl CollectPermissionChanges for vir_typed::DeadInclusion {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::LifetimeTake {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::LifetimeReturn {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::MaterializePredicate {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        // Materialize predicate is applied only to non-managed predicates.
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::ObtainMutRef {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        let ty = *self.place.get_type().clone().unwrap_reference().target_type;
        let place = self.place.clone().deref(ty, self.position);
        consumed_permissions.push(Permission::Owned(place.clone()));
        produced_permissions.push(Permission::Owned(place));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::OpenMutRef {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::Owned(self.place.clone()));
        produced_permissions.push(Permission::Owned(self.place.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::OpenFracRef {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::Owned(self.place.clone()));
        produced_permissions.push(Permission::Owned(self.place.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::CloseMutRef {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::Owned(self.place.clone()));
        produced_permissions.push(Permission::Owned(self.place.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::CloseFracRef {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::Owned(self.place.clone()));
        produced_permissions.push(Permission::Owned(self.place.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_typed::BorShorten {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        let ty = *self.value.get_type().clone().unwrap_reference().target_type;
        let place = self.value.clone().deref(ty, self.position);
        consumed_permissions.push(Permission::Owned(place.clone()));
        produced_permissions.push(Permission::Owned(place));
        Ok(())
    }
}
