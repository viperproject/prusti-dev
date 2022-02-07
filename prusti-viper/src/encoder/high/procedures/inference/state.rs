use super::permission::{Permission, PermissionKind};
use crate::encoder::errors::SpannedEncodingResult;
use log::debug;
use rustc_hash::FxHashSet;

use vir_crate::high as vir_high;

pub(in super::super) struct FoldUnfoldState {
    owned_non_aliased: FxHashSet<vir_high::Expression>,
    memory_block_stack: FxHashSet<vir_high::Expression>,
}

impl FoldUnfoldState {
    pub(in super::super) fn with_parameters_and_return(
        parameters: impl Iterator<Item = vir_high::VariableDecl>,
        returns: impl Iterator<Item = vir_high::VariableDecl>,
    ) -> Self {
        let mut owned_non_aliased = FxHashSet::default();
        for parameter in parameters {
            owned_non_aliased.insert(parameter.into());
        }
        let mut memory_block_stack = FxHashSet::default();
        for ret in returns {
            memory_block_stack.insert(ret.into());
        }
        Self {
            owned_non_aliased,
            memory_block_stack,
        }
    }

    pub(in super::super) fn debug_print(&self) {
        debug!("owned_non_aliased ({}):", self.owned_non_aliased.len());
        for place in &self.owned_non_aliased {
            debug!("  {}", place);
        }
        debug!("memory_block_stack ({}):", self.memory_block_stack.len());
        for place in &self.memory_block_stack {
            debug!("  {}", place);
        }
    }

    pub(in super::super) fn insert_memory_block(
        &mut self,
        place: vir_high::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(self.memory_block_stack.insert(place));
        Ok(())
    }

    pub(in super::super) fn insert_owned(
        &mut self,
        place: vir_high::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(self.owned_non_aliased.insert(place));
        Ok(())
    }

    pub(in super::super) fn remove_memory_block(
        &mut self,
        place: &vir_high::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(
            self.memory_block_stack.remove(place),
            "not found place: {}",
            place
        );
        Ok(())
    }

    pub(in super::super) fn remove_owned(
        &mut self,
        place: &vir_high::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(
            self.owned_non_aliased.remove(place),
            "not found place: {}",
            place
        );
        Ok(())
    }

    pub(in super::super) fn insert_permissions(
        &mut self,
        permissions: Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        for permission in permissions {
            self.insert_permission(permission)?;
        }
        Ok(())
    }

    pub(in super::super) fn insert_permission(
        &mut self,
        permission: Permission,
    ) -> SpannedEncodingResult<()> {
        match permission {
            Permission::MemoryBlock(place) => self.insert_memory_block(place)?,
            Permission::Owned(place) => self.insert_owned(place)?,
        }
        Ok(())
    }

    pub(in super::super) fn remove_permissions(
        &mut self,
        permissions: &[Permission],
    ) -> SpannedEncodingResult<()> {
        for permission in permissions {
            self.remove_permission(permission)?;
        }
        Ok(())
    }

    pub(in super::super) fn remove_permission(
        &mut self,
        permission: &Permission,
    ) -> SpannedEncodingResult<()> {
        match permission {
            Permission::MemoryBlock(place) => self.remove_memory_block(place)?,
            Permission::Owned(place) => self.remove_owned(place)?,
        }
        Ok(())
    }

    pub(in super::super) fn get_memory_block_places(&self) -> SpannedEncodingResult<Places<'_>> {
        Ok(Places {
            places: &self.memory_block_stack,
        })
    }

    pub(in super::super) fn get_owned_places(&self) -> SpannedEncodingResult<Places<'_>> {
        Ok(Places {
            places: &self.owned_non_aliased,
        })
    }

    pub(in super::super) fn remove(
        &mut self,
        kind: PermissionKind,
        place: &vir_high::Expression,
    ) -> SpannedEncodingResult<()> {
        match kind {
            PermissionKind::MemoryBlock => self.remove_memory_block(place)?,
            PermissionKind::Owned => self.remove_owned(place)?,
        }
        Ok(())
    }

    pub(in super::super) fn insert(
        &mut self,
        kind: PermissionKind,
        place: vir_high::Expression,
    ) -> SpannedEncodingResult<()> {
        match kind {
            PermissionKind::MemoryBlock => self.insert_memory_block(place)?,
            PermissionKind::Owned => self.insert_owned(place)?,
        }
        Ok(())
    }

    pub(in super::super) fn collect_owned_with_prefix(
        &self,
        prefix: &vir_high::Expression,
    ) -> SpannedEncodingResult<Vec<vir_high::Expression>> {
        let collected_places = self
            .owned_non_aliased
            .iter()
            .filter(|place| place.has_prefix(prefix))
            .cloned()
            .collect();
        Ok(collected_places)
    }
}

pub(in super::super) struct Places<'a> {
    places: &'a FxHashSet<vir_high::Expression>,
}

impl<'a> Places<'a> {
    pub(in super::super) fn contains(&self, place: &vir_high::Expression) -> bool {
        self.places.contains(place)
    }

    pub(in super::super) fn find_prefix(
        &self,
        place: &vir_high::Expression,
    ) -> Option<vir_high::Expression> {
        self.places.iter().find(|p| place.has_prefix(p)).cloned()
    }

    pub(in super::super) fn contains_with_prefix(&self, prefix: &vir_high::Expression) -> bool {
        self.places.iter().any(|p| p.has_prefix(prefix))
    }
}
