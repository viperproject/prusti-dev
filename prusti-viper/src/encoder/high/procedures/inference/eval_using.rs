use super::state::PredicateState;
use crate::{
    encoder::{
        errors::SpannedEncodingResult, high::procedures::inference::permission::PermissionKind,
        Encoder,
    },
    error_incorrect, error_internal,
};
use vir_crate::{
    common::{builtin_constants::ADDRESS_FIELD_NAME, position::Positioned},
    typed::{self as vir_typed, operations::ty::Typed},
};

pub(super) fn wrap_in_eval_using(
    encoder: &mut Encoder<'_, '_>,
    state: &mut super::state::FoldUnfoldState,
    mut expression: vir_typed::Expression,
) -> SpannedEncodingResult<vir_typed::Expression> {
    let accessed_places = strip_dereferences(expression.collect_all_places());
    let mut framing_places = Vec::new();
    let mut context_kinds = Vec::new();
    for accessed_place in accessed_places {
        if let Some(old_wrap) = check_old_wraps_and_return_first(&accessed_place, None) {
            let context_kind = match old_wrap {
                vir_typed::Expression::LabelledOld(vir_typed::LabelledOld {
                    base: box vir_typed::Expression::Local(_),
                    ..
                }) => vir_typed::EvalInContextKind::Old,
                _ => vir_typed::EvalInContextKind::OldOpenedRefPredicate,
            };
            if !framing_places.contains(old_wrap) {
                framing_places.push(old_wrap.clone());
                context_kinds.push(context_kind);
            }
            continue;
        }
        let predicates_state =
            if let Some(predicate_state) = state.try_get_predicates_state(&accessed_place)? {
                predicate_state
            } else {
                // If `place` is not known to fold-unfold, then it is not an encoded
                // Rust place, but a ghost variable emitted by the encoding.
                //
                // FIXME: Instead of relying on fold-unfold, we should distinguish
                // between Rust places and places emitted as part of our encoding.
                continue;
            };
        match predicates_state {
            PredicateState::Unconditional(state) => {
                collect_framing_places_from_a_state(
                    encoder,
                    state,
                    &accessed_place,
                    &mut framing_places,
                    &mut context_kinds,
                    expression.position(),
                )?;
            }
            PredicateState::Conditional(states) => {
                let mut states_iter = states.values();
                let first_state = states_iter.next().unwrap();
                if states_iter.all(|state| {
                    state.owned_equal(first_state)
                        && state.memory_block_stack_equal(first_state)
                        && state.blocked_equal(first_state)
                }) {
                    collect_framing_places_from_a_state(
                        encoder,
                        first_state,
                        &accessed_place,
                        &mut framing_places,
                        &mut context_kinds,
                        expression.position(),
                    )?;
                } else {
                    unimplemented!("Conditional predicate state: {predicates_state}");
                }
            }
        }
    }
    let position = expression.position();
    while let Some(framing_place) = framing_places.pop() {
        let kind = context_kinds.pop().unwrap();
        let context = if matches!(
            kind,
            vir_typed::EvalInContextKind::Predicate
                | vir_typed::EvalInContextKind::OpenedRefPredicate
                | vir_typed::EvalInContextKind::Old
                | vir_typed::EvalInContextKind::OldOpenedRefPredicate
        ) {
            vir_typed::Expression::acc_predicate(
                vir_typed::Predicate::owned_non_aliased(framing_place, position),
                position,
            )
        } else {
            framing_place
        };
        expression = vir_typed::Expression::eval_in(context, kind, expression, position);
    }
    Ok(expression)
}

fn collect_framing_places_from_a_state(
    encoder: &Encoder<'_, '_>,
    state: &super::state::PredicateStateOnPath,
    accessed_place: &vir_typed::Expression,
    framing_places: &mut Vec<vir_typed::Expression>,
    context_kinds: &mut Vec<vir_typed::EvalInContextKind>,
    position: vir_typed::Position,
) -> SpannedEncodingResult<()> {
    if let Some(framing_place) = state.find_prefix(PermissionKind::Owned, accessed_place) {
        if !framing_places.contains(&framing_place) {
            framing_places.push(framing_place);
            if state.is_opened_ref(accessed_place)?.is_some() {
                context_kinds.push(vir_typed::EvalInContextKind::OpenedRefPredicate);
            } else {
                context_kinds.push(vir_typed::EvalInContextKind::Predicate);
            }
        }
    } else if let Some(_) = state.find_prefix(PermissionKind::MemoryBlock, accessed_place) {
        let span = encoder
            .error_manager()
            .position_manager()
            .get_span(position.into())
            .cloned()
            .unwrap();
        error_internal!(span => "found an uninitialized place in specification: {accessed_place}");
    } else if state.contains_blocked(accessed_place)?.is_some() {
        let span = encoder
            .error_manager()
            .position_manager()
            .get_span(position.into())
            .cloned()
            .unwrap();
        error_incorrect!(span => "cannot use specifications to trigger unblocking of a blocked place");
    } else {
        let constituent_places = state.collect_owned_with_prefix(accessed_place)?;
        for framing_place in &constituent_places {
            if !framing_places.contains(framing_place) {
                framing_places.push(framing_place.clone());
                context_kinds.push(vir_typed::EvalInContextKind::Predicate);
            }
        }
        for mut framing_place in &constituent_places {
            while let Some(parent_framing_place) = framing_place.get_parent_ref() {
                framing_place = parent_framing_place;
                if !framing_places.contains(framing_place) {
                    framing_places.push(framing_place.clone());
                    context_kinds.push(vir_typed::EvalInContextKind::SafeConstructor);
                    unimplemented!();
                }
                if framing_place == accessed_place {
                    break;
                }
            }
        }
    }
    Ok(())
}

fn check_old_wraps_and_return_first<'a>(
    accessed_place: &'a vir_typed::Expression,
    current_label: Option<&'a str>,
) -> Option<&'a vir_typed::Expression> {
    if let vir_typed::Expression::LabelledOld(vir_typed::LabelledOld { base, label, .. }) =
        accessed_place
    {
        if let Some(current_label) = current_label {
            assert_eq!(
                label, current_label,
                "the current implementation assumes that all labels are the same"
            );
        }
        let result = check_old_wraps_and_return_first(base, Some(label));
        if result.is_some() {
            result
        } else {
            Some(accessed_place)
        }
    } else if let Some(parent) = accessed_place.get_parent_ref_step_into_old() {
        check_old_wraps_and_return_first(parent, current_label)
    } else {
        None
    }
}

/// Does the following clean-up actions:
///
/// 1. Strips places up to the first raw pointer dereference. We need to do this
///    because accesses below raw pointer dereferences are not guarded by PCS.
/// 2. Strips places up to the first reference dereference. We can do this
///    because having a capability to a reference requires having a capability
///    to entire subtree below it because things cannot be moved out of a
///    reference in safe code.
fn strip_dereferences(places: Vec<vir_typed::Expression>) -> Vec<vir_typed::Expression> {
    let mut expanded_places = Vec::new();
    #[derive(PartialEq, Eq, Debug)]
    enum SearchResult {
        FoundReferenceOrPointer,
        FoundOld,
        FoundNothing,
    }
    /// Returns `true` if the place is below a raw pointer dereference and
    /// should not be considered.
    fn expand_place(
        place: &vir_typed::Expression,
        expanded_places: &mut Vec<vir_typed::Expression>,
    ) -> SearchResult {
        if let Some(parent) = place.get_parent_ref_step_into_old() {
            let parent_result = expand_place(parent, expanded_places);
            if parent_result != SearchResult::FoundNothing {
                return parent_result;
            }
            if place.is_labelled_old() {
                return SearchResult::FoundOld;
            }
            match parent.get_type() {
                vir_typed::Type::Reference(_) => {
                    let address_place = vir_typed::Expression::field(
                        parent.clone(),
                        vir_typed::FieldDecl::new(
                            ADDRESS_FIELD_NAME,
                            0usize,
                            vir_typed::Type::Int(vir_typed::ty::Int::Usize),
                        ),
                        parent.position(),
                    );
                    expanded_places.push(address_place);
                    SearchResult::FoundNothing
                }
                vir_typed::Type::Pointer(_) => {
                    assert!(place.is_deref(), "{place}");
                    expanded_places.push(parent.clone());
                    SearchResult::FoundReferenceOrPointer
                }
                _ => SearchResult::FoundNothing,
            }
        } else {
            SearchResult::FoundNothing
        }
    }
    for place in places {
        if expand_place(&place, &mut expanded_places) != SearchResult::FoundReferenceOrPointer {
            expanded_places.push(place);
        }
    }
    expanded_places
}

// struct Wrapper<'p, 'v, 'tcx> {
//     encoder: &'p mut Encoder<'v, 'tcx>,
//     state: &'p mut super::state::FoldUnfoldState,
// }
