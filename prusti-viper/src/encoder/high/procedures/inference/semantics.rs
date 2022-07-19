use super::permission::{MutBorrowed, Permission};
use crate::encoder::{errors::SpannedEncodingResult, mir::types::MirTypeEncoderInterface, Encoder};
use vir_crate::{
    common::position::Positioned,
    high::{self as vir_high, operations::ty::Typed},
};

pub(in super::super) fn collect_permission_changes<'v, 'tcx>(
    encoder: &mut Encoder<'v, 'tcx>,
    statement: &vir_high::Statement,
) -> SpannedEncodingResult<(Vec<Permission>, Vec<Permission>)> {
    let mut consumed_permissions = Vec::new();
    let mut produced_permissions = Vec::new();
    statement.collect(
        encoder,
        &mut consumed_permissions,
        &mut produced_permissions,
    )?;
    Ok((consumed_permissions, produced_permissions))
}

trait CollectPermissionChanges {
    #[allow(clippy::ptr_arg)] // Clippy false positive.
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()>;
}

impl CollectPermissionChanges for vir_high::Statement {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        match self {
            vir_high::Statement::Comment(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::OldLabel(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::Inhale(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::Exhale(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::Consume(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::Havoc(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::Assume(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::Assert(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::LoopInvariant(_) => {
                unreachable!("LoopInvariant statement should have been removed before.");
            }
            vir_high::Statement::MovePlace(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::CopyPlace(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::WritePlace(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::WriteAddress(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::Assign(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::LeakAll(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::SetUnionVariant(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::NewLft(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::EndLft(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::DeadLifetime(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::DeadInclusion(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::LifetimeTake(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::ObtainMutRef(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::OpenMutRef(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::OpenFracRef(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::CloseMutRef(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::CloseFracRef(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::BorShorten(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
            vir_high::Statement::LifetimeReturn(statement) => {
                statement.collect(encoder, consumed_permissions, produced_permissions)
            }
        }
    }
}

impl CollectPermissionChanges for vir_high::Comment {
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

impl CollectPermissionChanges for vir_high::OldLabel {
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
    predicate: &vir_high::Predicate,
) -> SpannedEncodingResult<Option<Permission>> {
    match predicate {
        vir_high::Predicate::MemoryBlockStack(predicate) => {
            Ok(Some(Permission::MemoryBlock(predicate.place.clone())))
        }
        vir_high::Predicate::OwnedNonAliased(predicate) => {
            Ok(Some(Permission::Owned(predicate.place.clone())))
        }
        vir_high::Predicate::MemoryBlockStackDrop(_)
        | vir_high::Predicate::LifetimeToken(_)
        | vir_high::Predicate::MemoryBlockHeap(_)
        | vir_high::Predicate::MemoryBlockHeapDrop(_) => {
            // Unmanaged predicates.
            Ok(None)
        }
    }
}

impl CollectPermissionChanges for vir_high::Inhale {
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

impl CollectPermissionChanges for vir_high::Exhale {
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

impl CollectPermissionChanges for vir_high::Consume {
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

impl CollectPermissionChanges for vir_high::Havoc {
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

impl CollectPermissionChanges for vir_high::Assume {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::Assert {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::MovePlace {
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

impl CollectPermissionChanges for vir_high::CopyPlace {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::MemoryBlock(self.target.clone()));
        consumed_permissions.push(Permission::Owned(self.source.clone()));
        produced_permissions.push(Permission::Owned(self.target.clone()));
        produced_permissions.push(Permission::Owned(self.source.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::WritePlace {
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

impl CollectPermissionChanges for vir_high::WriteAddress {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        todo!();
    }
}

impl CollectPermissionChanges for vir_high::Assign {
    fn collect<'v, 'tcx>(
        &self,
        encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::MemoryBlock(self.target.clone()));
        if let vir_high::Rvalue::CheckedBinaryOp(_value) = &self.value {
            let type_decl = encoder
                .encode_type_def(self.target.get_type())?
                .unwrap_tuple();
            let (operation_result_field, flag_field) = {
                let mut iter = type_decl.iter_fields();
                (
                    iter.next().unwrap().into_owned(),
                    iter.next().unwrap().into_owned(),
                )
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

impl CollectPermissionChanges for vir_high::Rvalue {
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

impl CollectPermissionChanges for vir_high::ast::rvalue::Repeat {
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

impl CollectPermissionChanges for vir_high::ast::rvalue::Reborrow {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::Owned(self.place.clone()));
        if self.is_mut {
            produced_permissions.push(Permission::MutBorrowed(MutBorrowed {
                lifetime: self.operand_lifetime.clone(),
                place: self.place.clone(),
            }));
        } else {
            produced_permissions.push(Permission::Owned(self.place.clone()));
        }
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::ast::rvalue::Ref {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::Owned(self.place.clone()));
        produced_permissions.push(Permission::MutBorrowed(MutBorrowed {
            lifetime: self.operand_lifetime.clone(),
            place: self.place.clone(),
        }));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::ast::rvalue::AddressOf {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
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
        produced_permissions.push(Permission::Owned(self.place.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::ast::rvalue::Len {
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

impl CollectPermissionChanges for vir_high::ast::rvalue::UnaryOp {
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

impl CollectPermissionChanges for vir_high::ast::rvalue::BinaryOp {
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

impl CollectPermissionChanges for vir_high::ast::rvalue::CheckedBinaryOp {
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

impl CollectPermissionChanges for vir_high::ast::rvalue::Discriminant {
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

impl CollectPermissionChanges for vir_high::ast::rvalue::Aggregate {
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

impl CollectPermissionChanges for vir_high::ast::rvalue::Operand {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        use vir_high::ast::rvalue::OperandKind::*;
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

impl CollectPermissionChanges for vir_high::LeakAll {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::SetUnionVariant {
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

impl CollectPermissionChanges for vir_high::NewLft {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::EndLft {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::DeadLifetime {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        unreachable!("DeadLifetime is special cased in the caller");
    }
}

impl CollectPermissionChanges for vir_high::DeadInclusion {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::LifetimeTake {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::LifetimeReturn {
    fn collect<'v, 'tcx>(
        &self,
        _encoder: &mut Encoder<'v, 'tcx>,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::ObtainMutRef {
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

impl CollectPermissionChanges for vir_high::OpenMutRef {
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

impl CollectPermissionChanges for vir_high::OpenFracRef {
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

impl CollectPermissionChanges for vir_high::CloseMutRef {
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

impl CollectPermissionChanges for vir_high::CloseFracRef {
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

impl CollectPermissionChanges for vir_high::BorShorten {
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
