use super::permission::Permission;
use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::high as vir_high;

pub(in super::super) fn collect_permission_changes(
    statement: &vir_high::Statement,
) -> SpannedEncodingResult<(Vec<Permission>, Vec<Permission>)> {
    let mut required_permissions = Vec::new();
    let mut ensured_permissions = Vec::new();
    statement.collect(&mut required_permissions, &mut ensured_permissions)?;
    Ok((required_permissions, ensured_permissions))
}

trait CollectPermissionChanges {
    fn collect(
        &self,
        required_permissions: &mut Vec<Permission>,
        ensured_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()>;
}

impl CollectPermissionChanges for vir_high::Statement {
    fn collect(
        &self,
        required_permissions: &mut Vec<Permission>,
        ensured_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        match self {
            vir_high::Statement::Comment(statement) => {
                statement.collect(required_permissions, ensured_permissions)
            }
            vir_high::Statement::Inhale(statement) => {
                statement.collect(required_permissions, ensured_permissions)
            }
            vir_high::Statement::Exhale(statement) => {
                statement.collect(required_permissions, ensured_permissions)
            }
            vir_high::Statement::MovePlace(statement) => {
                statement.collect(required_permissions, ensured_permissions)
            }
            vir_high::Statement::CopyPlace(statement) => {
                statement.collect(required_permissions, ensured_permissions)
            }
            vir_high::Statement::WritePlace(statement) => {
                statement.collect(required_permissions, ensured_permissions)
            }
            vir_high::Statement::WriteAddress(statement) => {
                statement.collect(required_permissions, ensured_permissions)
            }
        }
    }
}

impl CollectPermissionChanges for vir_high::Comment {
    fn collect(
        &self,
        _required_permissions: &mut Vec<Permission>,
        _ensured_permissions: &mut Vec<Permission>,
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
        _required_permissions: &mut Vec<Permission>,
        ensured_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        ensured_permissions.extend(extract_managed_predicate_place(&self.predicate)?);
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::Exhale {
    fn collect(
        &self,
        required_permissions: &mut Vec<Permission>,
        _ensured_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        required_permissions.extend(extract_managed_predicate_place(&self.predicate)?);
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::MovePlace {
    fn collect(
        &self,
        required_permissions: &mut Vec<Permission>,
        ensured_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        required_permissions.push(Permission::MemoryBlock(self.target.clone()));
        required_permissions.push(Permission::Owned(self.source.clone()));
        ensured_permissions.push(Permission::Owned(self.target.clone()));
        ensured_permissions.push(Permission::MemoryBlock(self.source.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::CopyPlace {
    fn collect(
        &self,
        _required_permissions: &mut Vec<Permission>,
        _ensured_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        todo!();
    }
}

impl CollectPermissionChanges for vir_high::WritePlace {
    fn collect(
        &self,
        required_permissions: &mut Vec<Permission>,
        ensured_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        required_permissions.push(Permission::MemoryBlock(self.target.clone()));
        ensured_permissions.push(Permission::Owned(self.target.clone()));
        Ok(())
    }
}

impl CollectPermissionChanges for vir_high::WriteAddress {
    fn collect(
        &self,
        _required_permissions: &mut Vec<Permission>,
        _ensured_permissions: &mut Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        todo!();
    }
}
