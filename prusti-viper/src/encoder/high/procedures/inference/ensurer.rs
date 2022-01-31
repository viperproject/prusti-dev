use super::{
    action::Action,
    permission::{Permission, PermissionKind},
    FoldUnfoldState,
};
use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::high as vir_high;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(in super::super) enum ExpandedPermissionKind {
    /// The permission is the same as was the original one.
    Same,
    /// The permission was changed to a memory block.
    MemoryBlock,
}

pub(in super::super) trait Context {
    fn state(&self) -> &FoldUnfoldState;

    fn state_mut(&mut self) -> &mut FoldUnfoldState;

    fn expand_place(
        &mut self,
        place: &vir_high::Expression,
    ) -> SpannedEncodingResult<Vec<(ExpandedPermissionKind, vir_high::Expression)>>;
}

pub(in super::super) fn ensure_required_permissions(
    context: &mut impl Context,
    required_permissions: Vec<Permission>,
) -> SpannedEncodingResult<Vec<Action>> {
    let mut actions = Vec::new();
    for permission in required_permissions {
        ensure_required_permission(context, permission, &mut actions)?;
    }
    Ok(actions)
}

fn ensure_required_permission(
    context: &mut impl Context,
    required_permission: Permission,
    actions: &mut Vec<Action>,
) -> SpannedEncodingResult<()> {
    let (place, existing_places, permission_kind) = match required_permission {
        Permission::MemoryBlock(place) => (
            place,
            context.state().get_memory_block_places()?,
            PermissionKind::MemoryBlock,
        ),
        Permission::Owned(place) => (
            place,
            context.state().get_owned_places()?,
            PermissionKind::Owned,
        ),
    };
    if existing_places.contains(&place) {
        // The requirement is satisfied, do nothing.
    } else if let Some(prefix) = existing_places.find_prefix(&place) {
        // Unfold.
        context.state_mut().remove(permission_kind, &prefix)?;
        let expanded_place = context.expand_place(&prefix)?;
        actions.push(Action::Unfold(permission_kind, prefix));
        for (kind, new_place) in expanded_place {
            assert_eq!(
                kind,
                ExpandedPermissionKind::Same,
                "This should never lead to unfolding up to memory blocks."
            );
            context.state_mut().insert(permission_kind, new_place)?;
        }
        ensure_required_permission(context, Permission::new(permission_kind, place), actions)?;
    } else if permission_kind == PermissionKind::MemoryBlock
        && context
            .state()
            .get_owned_places()?
            .contains_with_prefix(&place)
    {
        // We have Owned and we need MemoryBlock. Fully unfold.
        for place in context.state().collect_owned_with_prefix(&place)? {
            context.state_mut().remove(PermissionKind::Owned, &place)?;
            ensure_fully_unfolded(context, place, actions)?;
        }
        ensure_required_permission(context, Permission::new(permission_kind, place), actions)?;
    } else {
        // Fold.
        assert!(existing_places.contains_with_prefix(&place));
        for (kind, new_place) in context.expand_place(&place)? {
            assert_eq!(kind, ExpandedPermissionKind::Same);
            ensure_required_permission(
                context,
                Permission::new(permission_kind, new_place.clone()),
                actions,
            )?;
            context.state_mut().remove(permission_kind, &new_place)?;
        }
        actions.push(Action::Fold(permission_kind, place.clone()));
        context.state_mut().insert(permission_kind, place)?;
    }
    Ok(())
}

/// Important: the `place` has to be already removed from `context`. This is
/// done to avoid unnecessary copying.
fn ensure_fully_unfolded(
    context: &mut impl Context,
    place: vir_high::Expression,
    actions: &mut Vec<Action>,
) -> SpannedEncodingResult<()> {
    let place_expansion = context.expand_place(&place)?;
    actions.push(Action::Unfold(PermissionKind::Owned, place));
    for (kind, new_place) in place_expansion {
        match kind {
            ExpandedPermissionKind::Same => {
                // Still need to unfold.
                ensure_fully_unfolded(context, new_place, actions)?;
            }
            ExpandedPermissionKind::MemoryBlock => {
                // Reached the bottom.
                context
                    .state_mut()
                    .insert(PermissionKind::MemoryBlock, new_place)?;
            }
        }
    }
    Ok(())
}
