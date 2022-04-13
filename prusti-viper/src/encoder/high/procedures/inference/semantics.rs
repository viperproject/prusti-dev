use super::permission::Permission;
use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::high as vir_high;

pub(in super::super) fn collect_permission_changes(
    statement: &vir_high::Statement,
) -> SpannedEncodingResult<(Vec<Permission>, Vec<Permission>)> {
    let mut consumed_permissions = Vec::new();
    let mut produced_permissions = Vec::new();
    statement.collect(&mut consumed_permissions, &mut produced_permissions)?;
    Ok((consumed_permissions, produced_permissions))
}

trait CollectPermissionChanges {
    #[allow(clippy::ptr_arg)] // Clippy false positive.
    fn collect(
        &self,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()>;
}

impl CollectPermissionChanges for vir_high::Statement {
    fn collect(
        &self,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        match self {
            vir_high::Statement::Comment(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::Inhale(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::Exhale(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::Consume(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::Assume(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::Assert(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::MovePlace(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::CopyPlace(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::WritePlace(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::WriteAddress(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::Assign(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::LeakAll(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::NewLft(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::EndLft(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
            vir_high::Statement::GhostAssignment(statement) => {
                statement.collect(consumed_permissions, produced_permissions)
            }
        }
    }
}

impl CollectPermissionChanges for vir_high::Comment {
    fn collect(
        &self,
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
        | vir_high::Predicate::MemoryBlockHeap(_)
        | vir_high::Predicate::MemoryBlockHeapDrop(_) => {
            // Unmanaged predicates.
            Ok(None)
        }
    }
}

impl CollectPermissionChanges for vir_high::Inhale {
    fn collect(
        &self,
        _consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        produced_permissions.extend(extract_managed_predicate_place(&self.predicate)?);
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::Exhale {
    fn collect(
        &self,
        consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.extend(extract_managed_predicate_place(&self.predicate)?);
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::Consume {
    fn collect(
        &self,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        self.operand
            .collect(consumed_permissions, produced_permissions)?;
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::Assume {
    fn collect(
        &self,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::Assert {
    fn collect(
        &self,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::MovePlace {
    fn collect(
        &self,
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
    fn collect(
        &self,
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
    fn collect(
        &self,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::MemoryBlock(self.target.clone()));
        produced_permissions.push(Permission::Owned(self.target.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::WriteAddress {
    fn collect(
        &self,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        todo!();
    }
}

impl CollectPermissionChanges for vir_high::Assign {
    fn collect(
        &self,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::MemoryBlock(self.target.clone()));
        produced_permissions.push(Permission::Owned(self.target.clone()));
        self.value
            .collect(consumed_permissions, produced_permissions)
    }
}

impl CollectPermissionChanges for vir_high::Rvalue {
    fn collect(
        &self,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        match self {
            Self::Ref(rvalue) => rvalue.collect(consumed_permissions, produced_permissions),
            Self::AddressOf(rvalue) => rvalue.collect(consumed_permissions, produced_permissions),
            Self::UnaryOp(rvalue) => rvalue.collect(consumed_permissions, produced_permissions),
            Self::BinaryOp(rvalue) => rvalue.collect(consumed_permissions, produced_permissions),
            Self::Discriminant(rvalue) => {
                rvalue.collect(consumed_permissions, produced_permissions)
            }
            Self::Aggregate(rvalue) => rvalue.collect(consumed_permissions, produced_permissions),
        }
    }
}

impl CollectPermissionChanges for vir_high::ast::rvalue::Ref {
    fn collect(
        &self,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::Owned(self.place.clone()));
        produced_permissions.push(Permission::Owned(self.place.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::ast::rvalue::AddressOf {
    fn collect(
        &self,
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

impl CollectPermissionChanges for vir_high::ast::rvalue::UnaryOp {
    fn collect(
        &self,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        self.argument
            .collect(consumed_permissions, produced_permissions)
    }
}

impl CollectPermissionChanges for vir_high::ast::rvalue::BinaryOp {
    fn collect(
        &self,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        self.left
            .collect(consumed_permissions, produced_permissions)?;
        self.right
            .collect(consumed_permissions, produced_permissions)?;
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::ast::rvalue::Discriminant {
    fn collect(
        &self,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        consumed_permissions.push(Permission::Owned(self.place.clone()));
        produced_permissions.push(Permission::Owned(self.place.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::ast::rvalue::Aggregate {
    fn collect(
        &self,
        consumed_permissions: &mut Vec<Permission>,
        produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        for operand in &self.operands {
            operand.collect(consumed_permissions, produced_permissions)?;
        }
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::ast::rvalue::Operand {
    fn collect(
        &self,
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
    fn collect(
        &self,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::NewLft {
    fn collect(
        &self,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::EndLft {
    fn collect(
        &self,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::GhostAssignment {
    fn collect(
        &self,
        _consumed_permissions: &mut Vec<Permission>,
        _produced_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}
