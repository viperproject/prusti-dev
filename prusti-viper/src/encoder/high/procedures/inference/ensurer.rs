use super::{
    action::Action,
    permission::{Permission, PermissionKind},
    state::PredicateState,
    FoldUnfoldState,
};
use crate::encoder::errors::{ErrorCtxt, SpannedEncodingError, SpannedEncodingResult};
use log::debug;
use vir_crate::{
    common::position::Positioned,
    high::{self as vir_high, operations::ty::Typed},
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(in super::super) enum ExpandedPermissionKind {
    /// The permission is the same as was the original one.
    Same,
    /// The permission was changed to a memory block.
    MemoryBlock,
}

pub(in super::super) trait Context {
    /// The guiding place is used to determine which variant of the enum should
    /// be used.
    fn expand_place(
        &mut self,
        place: &vir_high::Expression,
        guiding_place: &vir_high::Expression,
    ) -> SpannedEncodingResult<Vec<(ExpandedPermissionKind, vir_high::Expression)>>;
    fn get_span(&mut self, position: vir_high::Position) -> Option<rustc_span::MultiSpan>;
    fn change_error_context(
        &mut self,
        position: vir_high::Position,
        error_ctxt: ErrorCtxt,
    ) -> vir_high::Position;
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
    if can_place_be_ensured_in(
        context,
        &place,
        permission_kind,
        unconditional_predicate_state,
    )? {
        ensure_permission_in_state(
            context,
            unconditional_predicate_state,
            place,
            permission_kind,
            actions,
        )?;
    } else {
        for (condition, conditional_predicate_state) in state.get_conditional_states()? {
            if can_place_be_ensured_in(
                context,
                &place,
                permission_kind,
                conditional_predicate_state,
            )? {
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

fn can_place_be_ensured_in(
    context: &mut impl Context,
    place: &vir_high::Expression,
    permission_kind: PermissionKind,
    predicate_state: &PredicateState,
) -> SpannedEncodingResult<bool> {
    // The requirement is already satisfied.
    let already_satisfied = predicate_state.contains(permission_kind, place);
    // The requirement can be satisifed by unfolding.
    let by_unfolding = predicate_state.contains_prefix_of(permission_kind, place);
    // The requirement can be satisifed by folding.
    let by_folding = predicate_state
        .contains_non_discriminant_with_prefix(permission_kind, place)
        .is_some();
    // The requirement can be satisfied by converting into Memory Block.
    let by_into_memory_block = permission_kind == PermissionKind::MemoryBlock
        && can_place_be_ensured_in(context, place, PermissionKind::Owned, predicate_state)?;
    let can = already_satisfied || by_unfolding || by_folding || by_into_memory_block;
    if !can {
        // Check whether required_permission conflicts with state (has a
        // different variant) and report an error to the user suggesting that
        // they should fold.
        for prefix in place.iter_prefixes() {
            if let vir_high::Expression::Variant(variant) = prefix {
                for prefixed in predicate_state.get_all_with_prefix(permission_kind, &variant.base)
                {
                    if !prefixed.has_prefix(prefix) {
                        let place_span = context.get_span(place.position()).unwrap();
                        let prefixed_span = context.get_span(prefixed.position()).unwrap();
                        let mut error = SpannedEncodingError::unsupported(
                            "failed to obtain the required capability because a conflicting \
                                    capability is present",
                            place_span,
                        );
                        error.add_note(
                            "this typically happens when trying to read from different union fields \
                            because Prusti does not yet support reinterpreting memory",
                            None,
                        );
                        error.add_note("the conflicting capability", Some(prefixed_span));
                        error.set_help("try manually packaging the union capability");
                        return Err(error);
                    }
                }
            }
        }
    }
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
        let expanded_place = context.expand_place(&prefix, &place)?;
        debug!("expand_place(place={}, guiding_place={})", prefix, place);
        let enum_variant = if prefix.get_type().has_variants() {
            Some(prefix.get_variant_name(&place).clone())
        } else {
            None
        };
        let position = {
            let error_ctxt = if let vir_high::Type::Union(vir_high::ty::Union {
                variant: Some(_),
                ..
            }) = prefix.get_type()
            {
                ErrorCtxt::UnfoldUnionVariant
            } else {
                ErrorCtxt::Unfold
            };
            context.change_error_context(place.position(), error_ctxt)
        };
        let prefix = prefix.replace_position(position);
        actions.push(Action::unfold(permission_kind, prefix, enum_variant));
        for (kind, new_place) in expanded_place {
            debug!("  kind={:?} new_place={}", kind, new_place);
            new_place.check_no_default_position();
            assert_eq!(
                kind,
                ExpandedPermissionKind::Same,
                "This should never lead to unfolding up to memory blocks."
            );
            predicate_state.insert(permission_kind, new_place)?;
        }
        ensure_permission_in_state(context, predicate_state, place, permission_kind, actions)?;
    } else if let Some(witness) =
        predicate_state.contains_non_discriminant_with_prefix(permission_kind, &place)
    {
        // The requirement can be satisifed by folding.
        let enum_variant = if place.get_type().has_variants() {
            Some(place.get_variant_name(witness).clone())
        } else {
            None
        };
        for (kind, new_place) in context.expand_place(&place, witness)? {
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
        actions.push(Action::fold(permission_kind, place.clone(), enum_variant));
        predicate_state.insert(permission_kind, place)?;
    } else if permission_kind == PermissionKind::MemoryBlock
        && can_place_be_ensured_in(context, &place, PermissionKind::Owned, predicate_state)?
    {
        let places = predicate_state.collect_owned_with_prefix(&place)?;
        if places.is_empty() {
            // We have Owned and we need MemoryBlock. Fully unfold.
            // PROBLEM: we don't have a place here for a deref and it will recursively call itself without doing anything
            unimplemented!("Deref not yet supported");
        }
        for place in places {
            predicate_state.remove(PermissionKind::Owned, &place)?;
            predicate_state.insert(PermissionKind::MemoryBlock, place.clone())?;
            actions.push(Action::owned_into_memory_block(place));
        }
        ensure_permission_in_state(context, predicate_state, place, permission_kind, actions)?;
    } else {
        // The requirement cannot be satisfied.
        unreachable!("{} {:?}", place, permission_kind);
    };
    Ok(())
}
