use super::{
    action::Action,
    permission::{Permission, PermissionKind},
    state::PredicateStateOnPath,
    FoldUnfoldState,
};
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingError, SpannedEncodingResult},
    high::procedures::inference::state::PredicateState,
};
use log::debug;
use prusti_rustc_interface::errors::MultiSpan;
use vir_crate::{
    common::position::Positioned,
    middle as vir_mid,
    typed::{self as vir_typed, operations::ty::Typed},
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
        place: &vir_typed::Expression,
        guiding_place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<Vec<(ExpandedPermissionKind, vir_typed::Expression)>>;
    fn get_span(&mut self, position: vir_typed::Position) -> Option<MultiSpan>;
    fn change_error_context(
        &mut self,
        position: vir_typed::Position,
        error_ctxt: ErrorCtxt,
    ) -> vir_typed::Position;
}

pub(in super::super) fn ensure_required_permissions(
    context: &mut impl Context,
    state: &mut FoldUnfoldState,
    required_permissions: Vec<Permission>,
) -> SpannedEncodingResult<Vec<Action>> {
    state.check_consistency();
    let mut actions = Vec::new();
    for permission in required_permissions {
        ensure_required_permission(context, state, permission, &mut actions)?;
    }
    state.check_consistency();
    Ok(actions)
}

/// A special cased version of `ensure_required_permissions` for enum
/// discriminants. The problem with enum discriminants is that we cannot always
/// change the folding state to something specific (for example, require that
/// the enum is always folded). Therefore, we use this method to check in what
/// state is the discriminant and emit a discriminant lookup operation that
/// either requires a field or a folded enum.
///
/// `place` – place of the enum.
pub(in super::super) fn try_ensure_enum_discriminant_by_unfolding(
    context: &mut impl Context,
    state: &mut FoldUnfoldState,
    place: &vir_typed::Expression,
    permission_kind: PermissionKind,
) -> SpannedEncodingResult<(Option<Vec<vir_mid::BlockMarkerCondition>>, Vec<Action>)> {
    let mut actions = Vec::new();
    match state.get_predicates_state(place)? {
        PredicateState::Unconditional(unconditional_predicate_state) => {
            if check_contains_place(unconditional_predicate_state, place, permission_kind)?
                || unconditional_predicate_state
                    .find_prefix(permission_kind, place)
                    .is_some()
            {
                ensure_permission_in_state(
                    context,
                    unconditional_predicate_state,
                    place.clone(),
                    permission_kind,
                    &mut actions,
                )?;
                Ok((Some(Vec::new()), actions))
            } else {
                debug_assert!(
                    unconditional_predicate_state
                        .contains_discriminant_with_prefix(place)
                        .is_some(),
                    "The state must contain the discriminant of the enum: {place}. State: {unconditional_predicate_state}",
                );
                Ok((None, Vec::new()))
            }
        }
        PredicateState::Conditional(conditional_predicate_states) => {
            let mut conditions = Vec::new();
            for (condition, conditional_predicate_state) in conditional_predicate_states {
                if check_contains_place(conditional_predicate_state, place, permission_kind)?
                    || conditional_predicate_state
                        .find_prefix(permission_kind, place)
                        .is_some()
                {
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
                } else {
                    conditions.push(condition.clone());
                }
            }
            Ok((Some(conditions), actions))
        }
    }
}

#[tracing::instrument(level = "debug", skip(context, state, actions))]
pub(in super::super) fn ensure_required_permission(
    context: &mut impl Context,
    state: &mut FoldUnfoldState,
    required_permission: Permission,
    actions: &mut Vec<Action>,
) -> SpannedEncodingResult<()> {
    return Ok(()); // TODO: Remove permission reasoning
    state.debug_print();

    let (place, permission_kind) = match required_permission {
        Permission::MemoryBlock(place) => (place, PermissionKind::MemoryBlock),
        Permission::Owned(place) => (place, PermissionKind::Owned),
        Permission::MutBorrowed(borrow) => unreachable!("requiring a borrow: {}", borrow),
    };

    let base = place.get_base().erase_lifetime();
    match state.get_predicates_state(&place)? {
        PredicateState::Unconditional(unconditional_predicate_state) => {
            if ensure_permission_in_state(
                context,
                unconditional_predicate_state,
                place,
                permission_kind,
                actions,
            )? {
                debug!("Dropping unconditional state due to conflicting requirements.");
                unconditional_predicate_state.clear()?;
            }
        }
        PredicateState::Conditional(conditional_predicate_states) => {
            for (condition, conditional_predicate_state) in conditional_predicate_states {
                let mut conditional_actions = Vec::new();
                let to_drop = ensure_permission_in_state(
                    context,
                    conditional_predicate_state,
                    place.clone(),
                    permission_kind,
                    &mut conditional_actions,
                )?;
                // Even if the state is unreachable, we add the actions because
                // one of them should be the marker that the state is
                // unreachable.
                actions.extend(
                    conditional_actions
                        .into_iter()
                        .map(|action| action.set_condition(condition)),
                );
                if to_drop {
                    // The state should be unreachable. Drop it.
                    conditional_predicate_state.clear()?;
                }
            }
        }
    }
    state.remove_empty_states(&base)?;
    state.check_consistency();
    Ok(())
}

fn check_can_place_be_ensured_in(
    context: &mut impl Context,
    place: &vir_typed::Expression,
    permission_kind: PermissionKind,
    predicate_state: &PredicateStateOnPath,
    check_conversions: bool,
) -> SpannedEncodingResult<bool> {
    // The requirement is already satisfied.
    let already_satisfied = predicate_state.contains(permission_kind, place);
    // The requirement can be satisifed by unfolding.
    let by_unfolding = predicate_state.contains_prefix_of(permission_kind, place);
    // The requirement can be satisifed by folding.
    let by_folding = predicate_state
        .contains_non_discriminant_with_prefix(permission_kind, place)
        .is_some();
    let by_folding_discriminant = predicate_state
        .contains_discriminant_with_prefix(place)
        .is_some();
    // The requirement can be satisfied by restoring a mutable borrow.
    let by_restoring_blocked = predicate_state.contains_blocked(place)?.is_some();
    // The requirement can be satisfied by converting into Memory Block.
    // Short circuiting is used to prevent infinite recursion.
    let by_into_memory_block = check_conversions
        && permission_kind == PermissionKind::MemoryBlock
        && check_can_place_be_ensured_in(
            context,
            place,
            PermissionKind::Owned,
            predicate_state,
            false,
        )?;
    // The requirement can be satisfied by converting into Owned.
    // Short circuiting is used to prevent infinite recursion.
    let by_into_owned = check_conversions
        && permission_kind == PermissionKind::Owned
        && check_can_place_be_ensured_in(
            context,
            place,
            PermissionKind::MemoryBlock,
            predicate_state,
            false,
        )?;
    let can = already_satisfied
        || by_unfolding
        || by_folding
        || by_folding_discriminant
        || by_restoring_blocked
        || by_into_memory_block
        || by_into_owned;
    if !can {
        // Check whether required_permission conflicts with state (has a
        // different variant) and report an error to the user suggesting that
        // they should fold.
        for prefix in place.iter_prefixes() {
            if let vir_typed::Expression::Variant(variant) = prefix {
                for prefixed in predicate_state.get_all_with_prefix(permission_kind, &variant.base)
                {
                    if !prefixed.has_prefix(prefix) && !prefixed.is_discriminant_field() {
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

fn can_place_be_ensured_in(
    context: &mut impl Context,
    place: &vir_typed::Expression,
    permission_kind: PermissionKind,
    predicate_state: &PredicateStateOnPath,
) -> SpannedEncodingResult<bool> {
    check_can_place_be_ensured_in(context, place, permission_kind, predicate_state, true)
}

fn check_contains_place(
    predicate_state: &mut PredicateStateOnPath,
    place: &vir_typed::Expression,
    permission_kind: PermissionKind,
) -> SpannedEncodingResult<bool> {
    let contains = if predicate_state.contains(permission_kind, place) {
        true
    } else if permission_kind == PermissionKind::MemoryBlock {
        let address_place = vir_typed::Expression::field(
            place.clone(),
            vir_typed::FieldDecl::new(
                "address$",
                0usize,
                vir_typed::Type::Int(vir_typed::ty::Int::Usize),
            ),
            place.position(),
        );
        if predicate_state.contains(PermissionKind::MemoryBlock, &address_place) {
            predicate_state.remove(PermissionKind::MemoryBlock, &address_place)?;
            predicate_state.insert(PermissionKind::MemoryBlock, place.clone())?;
            true
        } else if predicate_state.contains(PermissionKind::Owned, &address_place) {
            for deref_place in predicate_state.collect_owned_with_prefix(place)? {
                predicate_state.remove(PermissionKind::Owned, &deref_place)?;
            }
            predicate_state.insert(PermissionKind::MemoryBlock, place.clone())?;
            true
        } else {
            false
        }
    } else {
        false
    };
    Ok(contains)
}

/// Returns `true` if the state should be droped because it should be
/// unreachable.
#[tracing::instrument(level = "debug", skip(context, predicate_state, actions))]
fn ensure_permission_in_state(
    context: &mut impl Context,
    predicate_state: &mut PredicateStateOnPath,
    place: vir_typed::Expression,
    permission_kind: PermissionKind,
    actions: &mut Vec<Action>,
) -> SpannedEncodingResult<bool> {
    return Ok(true); // TODO: Remove permission reasoning
    predicate_state.check_consistency();
    let to_drop = if check_contains_place(predicate_state, &place, permission_kind)? {
        debug!("  satisfied: {:?} {}", permission_kind, place);
        // The requirement is already satisfied.
        false
    } else if let Some(prefix) = predicate_state.find_prefix(permission_kind, &place) {
        // The requirement can be satisifed by unfolding.
        if prefix.get_type().is_trusted() {
            // Trusted types cannot be unfolded.
            let place_span = context.get_span(place.position()).unwrap();
            let prefix_span = context.get_span(prefix.position()).unwrap();
            let mut error = SpannedEncodingError::incorrect(
                "accessing fields of #[trusted] types is not allowed",
                place_span,
            );
            error.add_note(
                "the type of this place is marked as #[trusted]",
                Some(prefix_span),
            );
            error.set_help("you might want to mark the function as #[trusted]");
            return Err(error);
        }
        predicate_state.remove(permission_kind, &prefix)?;
        let expanded_place = context.expand_place(&prefix, &place)?;
        debug!("expand_place(place={}, guiding_place={})", prefix, place);
        let enum_variant = if prefix.get_type().has_variants() {
            Some(prefix.get_variant_name(&place).clone())
        } else {
            None
        };
        let position = {
            let error_ctxt = if let vir_typed::Type::Enum(vir_typed::ty::Enum {
                variant: Some(_),
                safety: vir_typed::ty::EnumSafety::Union,
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
        ensure_permission_in_state(context, predicate_state, place, permission_kind, actions)?
    } else if let Some(witness) = predicate_state
        .contains_non_discriminant_with_prefix(permission_kind, &place)
        .cloned()
    {
        // The requirement can be satisifed by folding.
        let enum_variant = if place.get_type().has_variants() {
            Some(place.get_variant_name(&witness).clone())
        } else {
            None
        };
        for (kind, new_place) in context.expand_place(&place, &witness)? {
            assert_eq!(kind, ExpandedPermissionKind::Same);
            if ensure_permission_in_state(
                context,
                predicate_state,
                new_place.clone(),
                permission_kind,
                actions,
            )? {
                return Ok(true);
            }
            predicate_state.remove(permission_kind, &new_place)?;
        }
        actions.push(Action::fold(permission_kind, place.clone(), enum_variant));
        predicate_state.insert(permission_kind, place)?;
        false
    } else if let Some((prefix, lifetime)) = predicate_state.contains_blocked(&place)? {
        let prefix = prefix.clone();
        let lifetime = lifetime.clone();
        predicate_state.remove_mut_borrowed(&prefix)?;
        predicate_state.insert(PermissionKind::Owned, prefix.clone())?;
        actions.push(Action::restore_mut_borrowed(lifetime, prefix.clone()));
        ensure_permission_in_state(context, predicate_state, place, permission_kind, actions)?
    } else if permission_kind == PermissionKind::MemoryBlock
        && can_place_be_ensured_in(context, &place, PermissionKind::Owned, predicate_state)?
    {
        // We have Owned and we need MemoryBlock.
        if predicate_state.contains_prefix_of(PermissionKind::Owned, &place) {
            // We have Owned that contains the place we need. Unfold as we need
            // and convert into MemoryBlock.
            let to_drop = ensure_permission_in_state(
                context,
                predicate_state,
                place.clone(),
                PermissionKind::Owned,
                actions,
            )?;
            predicate_state.remove(PermissionKind::Owned, &place)?;
            predicate_state.insert(PermissionKind::MemoryBlock, place.clone())?;
            actions.push(Action::owned_into_memory_block(place));
            to_drop
        } else if place.get_type().is_reference() {
            // We need to special case references to be no-op here because
            // `_2.*` is both `Owned` and `MemoryBlock`.
            let target_type = *place.get_type().clone().unwrap_reference().target_type;
            let deref_place =
                vir_typed::Expression::deref(place.clone(), target_type, place.position());
            let to_drop = ensure_permission_in_state(
                context,
                predicate_state,
                deref_place.clone(),
                PermissionKind::Owned,
                actions,
            )?;
            predicate_state.remove(PermissionKind::Owned, &deref_place)?;
            predicate_state.insert(PermissionKind::MemoryBlock, place.clone())?;
            to_drop
        } else if place.get_type().is_array() {
            // We need to special case arrays, because when the array is
            // unfolded, we track only a single element of the array and only
            // that element would be converted. It is fine to require Owned of
            // the entire array, because either the entire array can be Owned or
            // MemoryBlock. In Rust, having a mix is not allowed.
            let to_drop = ensure_permission_in_state(
                context,
                predicate_state,
                place.clone(),
                PermissionKind::Owned,
                actions,
            )?;
            predicate_state.remove(PermissionKind::Owned, &place)?;
            predicate_state.insert(PermissionKind::MemoryBlock, place.clone())?;
            actions.push(Action::owned_into_memory_block(place));
            to_drop
        } else {
            // We have a mix of Owned and MemoryBlock. Convert all Owned into
            // MemoryBlock and then obtain the MemoryBlock we need.
            let places = predicate_state.collect_owned_with_prefix(&place)?;
            assert!(!places.is_empty(), "Something went wrong.");
            for place in places {
                predicate_state.remove(PermissionKind::Owned, &place)?;
                predicate_state.insert(PermissionKind::MemoryBlock, place.clone())?;
                actions.push(Action::owned_into_memory_block(place));
            }
            ensure_permission_in_state(context, predicate_state, place, permission_kind, actions)?
        }
    } else if permission_kind == PermissionKind::Owned
        && can_place_be_ensured_in(
            context,
            &place,
            PermissionKind::MemoryBlock,
            predicate_state,
        )?
    {
        if predicate_state.contains(PermissionKind::MemoryBlock, &place)
            && place.get_type().is_int()
        {
            predicate_state.remove(PermissionKind::MemoryBlock, &place)?;
            predicate_state.insert(PermissionKind::Owned, place.clone())?;
            actions.push(Action::fold(PermissionKind::Owned, place, None));
            false
        } else {
            // We have MemoryBlock and we need Owned, which means that this
            // state should be unreachable. This typically happens when dropck
            // tries to drop different enum variants one after another:
            // ```rust
            // if discriminant(x) == 0 {
            //     drop(x.0);
            // }
            // if discriminant(x) == 1 {
            //     // We are here.
            //     drop(x.1);
            // }
            // ```
            let position =
                context.change_error_context(place.position(), ErrorCtxt::UnreachableFoldingState);
            actions.push(Action::unreachable(position));
            true
        }
    } else {
        // The requirement cannot be satisfied.
        unreachable!(
            "place={} permission_kind={:?} predicate_state={}",
            place, permission_kind, predicate_state
        );
    };
    predicate_state.check_consistency();
    Ok(to_drop)
}
