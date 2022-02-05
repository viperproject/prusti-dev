use super::{
    action::Action,
    permission::{Permission, PermissionKind},
    state::PredicateState,
    FoldUnfoldState,
};
use crate::encoder::errors::SpannedEncodingResult;
use log::debug;
use vir_crate::high as vir_high;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(in super::super) enum ExpandedPermissionKind {
    /// The permission is the same as was the original one.
    Same,
    /// The permission was changed to a memory block.
    MemoryBlock,
}

pub(in super::super) trait Context {
    fn expand_place(
        &mut self,
        place: &vir_high::Expression,
    ) -> SpannedEncodingResult<Vec<(ExpandedPermissionKind, vir_high::Expression)>>;
}

pub(in super::super) fn ensure_required_permissions(
    context: &mut impl Context,
    state: &mut FoldUnfoldState,
    required_permissions: Vec<Permission>,
) -> SpannedEncodingResult<Vec<Action>> {
    let mut actions = Vec::new();
    for permission in required_permissions {
        ensure_required_permission(context, state, permission, &mut actions)?;
    }
    Ok(actions)
}

fn ensure_required_permission(
    context: &mut impl Context,
    state: &mut FoldUnfoldState,
    required_permission: Permission,
    actions: &mut Vec<Action>,
) -> SpannedEncodingResult<()> {
    debug!("required_permission: {}", required_permission);
    state.debug_print();

    let (place, permission_kind) = match required_permission {
        Permission::MemoryBlock(place) => (place, PermissionKind::MemoryBlock),
        Permission::Owned(place) => (place, PermissionKind::Owned),
    };

    let unconditional_predicate_state = state.get_unconditional_state()?;
    if can_place_be_ensured_in(&place, permission_kind, unconditional_predicate_state)? {
        ensure_permission_in_state(
            context,
            unconditional_predicate_state,
            place,
            permission_kind,
            actions,
        )?;
    } else {
        for (condition, conditional_predicate_state) in state.get_conditional_states()? {
            if can_place_be_ensured_in(&place, permission_kind, conditional_predicate_state)? {
                let mut conditional_actions = Vec::new();
                ensure_permission_in_state(
                    context,
                    conditional_predicate_state,
                    place.clone(),
                    permission_kind,
                    &mut conditional_actions,
                )?;
                actions.extend(
                    conditional_actions
                        .into_iter()
                        .map(|action| action.set_condition(condition)),
                );
                conditional_predicate_state.remove(permission_kind, &place)?;
            }
        }
        state.remove_empty_conditional_states()?;
        state
            .get_unconditional_state()?
            .insert(permission_kind, place)?;
    }
    Ok(())
}

#[allow(clippy::if_same_then_else)] // Clippy is ignoring comments.
fn can_place_be_ensured_in(
    place: &vir_high::Expression,
    permission_kind: PermissionKind,
    predicate_state: &PredicateState,
) -> SpannedEncodingResult<bool> {
    let can = if predicate_state.contains(permission_kind, place) {
        // The requirement is already satisfied.
        true
    } else if predicate_state.contains_prefix_of(permission_kind, place) {
        // The requirement can be satisifed by unfolding.
        true
    } else if predicate_state.contains_with_prefix(permission_kind, place) {
        // The requirement can be satisifed by folding.
        true
    } else {
        permission_kind == PermissionKind::MemoryBlock
            && can_place_be_ensured_in(place, PermissionKind::Owned, predicate_state)?
    };
    Ok(can)
}

fn ensure_permission_in_state(
    context: &mut impl Context,
    predicate_state: &mut PredicateState,
    place: vir_high::Expression,
    permission_kind: PermissionKind,
    actions: &mut Vec<Action>,
) -> SpannedEncodingResult<()> {
    if predicate_state.contains(permission_kind, &place) {
        // The requirement is already satisfied.
    } else if let Some(prefix) = predicate_state.find_prefix(permission_kind, &place) {
        // The requirement can be satisifed by unfolding.
        predicate_state.remove(permission_kind, &prefix)?;
        let expanded_place = context.expand_place(&prefix)?;
        actions.push(Action::unfold(permission_kind, prefix));
        for (kind, new_place) in expanded_place {
            assert_eq!(
                kind,
                ExpandedPermissionKind::Same,
                "This should never lead to unfolding up to memory blocks."
            );
            predicate_state.insert(permission_kind, new_place)?;
        }
        ensure_permission_in_state(context, predicate_state, place, permission_kind, actions)?;
    } else if predicate_state.contains_with_prefix(permission_kind, &place) {
        // The requirement can be satisifed by folding.
        for (kind, new_place) in context.expand_place(&place)? {
            assert_eq!(kind, ExpandedPermissionKind::Same);
            ensure_permission_in_state(
                context,
                predicate_state,
                new_place.clone(),
                permission_kind,
                actions,
            )?;
            predicate_state.remove(permission_kind, &new_place)?;
        }
        actions.push(Action::fold(permission_kind, place.clone()));
        predicate_state.insert(permission_kind, place)?;
    } else if permission_kind == PermissionKind::MemoryBlock
        && can_place_be_ensured_in(&place, PermissionKind::Owned, predicate_state)?
    {
        // We have Owned and we need MemoryBlock. Fully unfold.
        for place in predicate_state.collect_owned_with_prefix(&place)? {
            predicate_state.remove(PermissionKind::Owned, &place)?;
            ensure_fully_unfolded(context, predicate_state, place, actions)?;
        }
        ensure_permission_in_state(context, predicate_state, place, permission_kind, actions)?;
    } else {
        // There requirement cannot be satisfied.
        unreachable!("{} {:?}", place, permission_kind);
    };
    Ok(())
}

/// Important: the `place` has to be already removed from `context`. This is
/// done to avoid unnecessary copying.
fn ensure_fully_unfolded(
    context: &mut impl Context,
    predicate_state: &mut PredicateState,
    place: vir_high::Expression,
    actions: &mut Vec<Action>,
) -> SpannedEncodingResult<()> {
    let place_expansion = context.expand_place(&place)?;
    actions.push(Action::unfold(PermissionKind::Owned, place));
    for (kind, new_place) in place_expansion {
        match kind {
            ExpandedPermissionKind::Same => {
                // Still need to unfold.
                ensure_fully_unfolded(context, predicate_state, new_place, actions)?;
            }
            ExpandedPermissionKind::MemoryBlock => {
                // Reached the bottom.
                predicate_state.insert(PermissionKind::MemoryBlock, new_place)?;
            }
        }
    }
    Ok(())
}
