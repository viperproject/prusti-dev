use crate::encoder::{
    errors::SpannedEncodingResult, high::procedures::inference::permission::Permission,
};
use log::debug;
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    middle::{self as vir_mid},
    typed::{self as vir_typed},
};

use super::PredicateState;

#[derive(Clone, Debug)]
pub(in super::super::super) struct FoldUnfoldState {
    /// If this state is a merge of multiple incoming states, then
    /// `incoming_labels` contains the list of basic blocks from where the
    /// already merged states came.
    incoming_labels: Vec<vir_mid::BasicBlockId>,
    /// `VariableDecl` indicates the root of the allocation. Currently, we
    /// support only stack allocations. They can be uniquely identified by
    /// `VariableDecl` of their base.
    predicates: BTreeMap<vir_typed::VariableDecl, PredicateState>,
    /// The stack of opened reference permissions. This is used as an heuristic
    /// to fill in permission amounts for pointer dereferences.
    ///
    /// The first element of the tuple is the expression that is opened, it is
    /// used only for error reporting and debugging.
    opened_ref_permission: Vec<(vir_typed::Expression, Option<vir_typed::VariableDecl>)>,
}

impl std::fmt::Display for FoldUnfoldState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "incoming labels: ")?;
        for label in &self.incoming_labels {
            write!(f, "{label}, ")?;
        }
        writeln!(f, "\nstates:")?;
        for (variable, predicate) in &self.predicates {
            writeln!(f, "{variable}:\n{predicate}")?;
        }
        Ok(())
    }
}

impl FoldUnfoldState {
    pub(in super::super) fn new() -> Self {
        Self {
            incoming_labels: Vec::new(),
            predicates: Default::default(),
            opened_ref_permission: Vec::new(),
        }
    }

    pub(in super::super) fn debug_print(&self) {
        debug!("state:\n{}", self);
    }

    pub(in super::super) fn contains_only_leakable(&self) -> bool {
        self.predicates
            .values()
            .all(|predicate| predicate.contains_only_leakable())
    }

    pub(in super::super) fn reset_incoming_labels_with(
        &mut self,
        incoming_label: vir_mid::BasicBlockId,
        path_disambiguators: &[vir_mid::BasicBlockId],
    ) -> SpannedEncodingResult<()> {
        for predicate_state in self.predicates.values_mut() {
            if let PredicateState::Conditional(states) = predicate_state {
                *states = std::mem::take(states)
                    .into_iter()
                    .map(|(mut labels, state)| {
                        for non_incoming_label in path_disambiguators {
                            labels.elements.push(vir_mid::BlockMarkerConditionElement {
                                visited: false,
                                basic_block_id: non_incoming_label.clone(),
                            });
                        }
                        labels.elements.push(vir_mid::BlockMarkerConditionElement {
                            visited: true,
                            basic_block_id: incoming_label.clone(),
                        });
                        (labels, state)
                    })
                    .collect();
            }
        }
        self.incoming_labels = vec![incoming_label];
        self.check_no_default_position();
        Ok(())
    }

    /// Merge `incoming_state` coming from block with label `incoming_label`
    /// into `self`.
    pub(in super::super) fn merge(
        &mut self,
        incoming_label: vir_mid::BasicBlockId,
        current_label: vir_mid::BasicBlockId,
        path_disambiguators: &BTreeMap<
            (vir_mid::BasicBlockId, vir_mid::BasicBlockId),
            Vec<vir_mid::BasicBlockId>,
        >,
        mut incoming_state: Self,
    ) -> SpannedEncodingResult<()> {
        // Roots that are available in both `self` and `incoming_state`.
        let all_roots = self
            .predicates
            .keys()
            .chain(incoming_state.predicates.keys())
            .cloned()
            .collect::<BTreeSet<_>>();

        // Merge `self` and `incoming_state` root by root.
        let empty_vec = Vec::new();
        let incoming_label_path_disambiguators = path_disambiguators
            .get(&(incoming_label.clone(), current_label.clone()))
            .unwrap_or(&empty_vec);
        for root in all_roots {
            let self_state = self.predicates.remove(&root);
            let incoming_predicate = incoming_state.predicates.remove(&root);

            let mut unconditional = None;
            let mut existing_self_conditional = None;
            let mut new_self_conditional = None;
            let mut existing_incoming_conditional = None;
            let mut new_incoming_conditional = None;
            match (self_state, incoming_predicate) {
                (None, None) => unreachable!(),
                (
                    Some(PredicateState::Unconditional(uself)),
                    Some(PredicateState::Unconditional(uincoming)),
                ) => {
                    if uself == uincoming {
                        unconditional = Some(uself);
                    } else {
                        new_self_conditional = Some(uself);
                        new_incoming_conditional = Some(uincoming);
                    }
                }
                (Some(PredicateState::Unconditional(uself)), None) => {
                    new_self_conditional = Some(uself);
                }
                (
                    Some(PredicateState::Unconditional(uself)),
                    Some(PredicateState::Conditional(cincoming)),
                ) => {
                    new_self_conditional = Some(uself);
                    existing_incoming_conditional = Some(cincoming);
                }
                (None, Some(PredicateState::Unconditional(uincoming))) => {
                    new_incoming_conditional = Some(uincoming);
                }
                (
                    Some(PredicateState::Conditional(cself)),
                    Some(PredicateState::Unconditional(uincoming)),
                ) => {
                    existing_self_conditional = Some(cself);
                    new_incoming_conditional = Some(uincoming);
                }
                (
                    Some(PredicateState::Conditional(cself)),
                    Some(PredicateState::Conditional(cincoming)),
                ) => {
                    existing_self_conditional = Some(cself);
                    existing_incoming_conditional = Some(cincoming);
                }
                (None, Some(PredicateState::Conditional(cincoming))) => {
                    existing_incoming_conditional = Some(cincoming);
                }
                (Some(PredicateState::Conditional(cself)), None) => {
                    existing_self_conditional = Some(cself);
                }
            };
            let merged_state = if let Some(unconditional) = unconditional {
                assert!(existing_self_conditional.is_none());
                assert!(new_self_conditional.is_none());
                assert!(existing_incoming_conditional.is_none());
                assert!(new_incoming_conditional.is_none());
                PredicateState::Unconditional(unconditional)
            } else {
                let mut states = BTreeMap::new();
                // Copy over conditional from self.
                if let Some(existing_self_conditional) = existing_self_conditional {
                    states.extend(existing_self_conditional);
                }
                // Copy over conditional from incoming.
                if let Some(existing_incoming_conditional) = existing_incoming_conditional {
                    states.extend(existing_incoming_conditional.into_iter().map(
                        |(mut labels, state)| {
                            for non_incoming_label in incoming_label_path_disambiguators {
                                labels.elements.push(vir_mid::BlockMarkerConditionElement {
                                    visited: false,
                                    basic_block_id: non_incoming_label.clone(),
                                });
                            }
                            labels.elements.push(vir_mid::BlockMarkerConditionElement {
                                visited: true,
                                basic_block_id: incoming_label.clone(),
                            });
                            (labels, state)
                        },
                    ));
                }
                // Create new conditionals from self.
                if let Some(new_self_conditional) = new_self_conditional {
                    for label in &self.incoming_labels {
                        let mut elements = vec![vir_mid::BlockMarkerConditionElement {
                            basic_block_id: label.clone(),
                            visited: true,
                        }];
                        for disambiguator in path_disambiguators
                            .get(&(label.clone(), current_label.clone()))
                            .unwrap_or(&empty_vec)
                        {
                            elements.push(vir_mid::BlockMarkerConditionElement {
                                visited: false,
                                basic_block_id: disambiguator.clone(),
                            });
                        }
                        states.insert(
                            vir_mid::BlockMarkerCondition { elements },
                            new_self_conditional.clone(),
                        );
                    }
                }
                // Create new conditionals from incoming.
                if let Some(new_incoming_conditional) = new_incoming_conditional {
                    let mut elements = vec![vir_mid::BlockMarkerConditionElement {
                        basic_block_id: incoming_label.clone(),
                        visited: true,
                    }];
                    for non_incoming_label in incoming_label_path_disambiguators {
                        elements.push(vir_mid::BlockMarkerConditionElement {
                            visited: false,
                            basic_block_id: non_incoming_label.clone(),
                        });
                    }
                    states.insert(
                        vir_mid::BlockMarkerCondition { elements },
                        new_incoming_conditional,
                    );
                }
                {
                    // Check whether all states are the same.
                    let mut states_iter = states.values();
                    let first_state = states_iter.next().unwrap();
                    if states_iter.all(|state| state.equal_ignoring_dead_lifetimes(first_state)) {
                        PredicateState::Unconditional(states.into_values().next().unwrap())
                    } else {
                        PredicateState::Conditional(states)
                    }
                }
            };
            self.predicates.insert(root, merged_state);
        }
        self.incoming_labels.push(incoming_label);
        self.check_no_default_position();
        Ok(())
    }

    pub(in super::super) fn insert_permissions(
        &mut self,
        permissions: Vec<Permission>,
    ) -> SpannedEncodingResult<()> {
        for permission in permissions {
            self.insert_permission(permission)?;
        }
        self.check_no_default_position();
        Ok(())
    }

    pub(in super::super) fn insert_permission(
        &mut self,
        permission: Permission,
    ) -> SpannedEncodingResult<()> {
        self.check_no_default_position();
        let place = permission.get_place();
        if let Some(state) = self.try_get_predicates_state_mut(place)? {
            state.insert_permission(permission)?;
        } else {
            let base = place.get_base().erase_lifetime();
            assert!(self
                .predicates
                .insert(base, PredicateState::new_unconditional(permission))
                .is_none());
        }
        self.check_no_default_position();
        Ok(())
    }

    pub(in super::super) fn remove_permissions(
        &mut self,
        permissions: &[Permission],
    ) -> SpannedEncodingResult<()> {
        self.check_no_default_position();
        for permission in permissions {
            self.remove_permission(permission)?;
        }
        Ok(())
    }

    pub(in super::super) fn remove_permission(
        &mut self,
        permission: &Permission,
    ) -> SpannedEncodingResult<()> {
        self.check_no_default_position();
        let place = permission.get_place();
        if let Some(state) = self.try_get_predicates_state_mut(place)? {
            state.remove_permission(permission)?;
            if state.is_empty() {
                let base = place.get_base().erase_lifetime();
                self.predicates.remove(&base);
            } else {
                state.remove_empty_states()?;
            }
        }
        Ok(())
    }

    pub(in super::super) fn open_ref(
        &mut self,
        place: vir_typed::Expression,
        predicate_permission_amount: Option<vir_typed::VariableDecl>,
    ) -> SpannedEncodingResult<()> {
        if !place.is_behind_pointer_dereference() {
            let state = self.get_predicates_state_mut(&place)?;
            state.open_ref(place.clone(), predicate_permission_amount.clone())?;
        }
        self.opened_ref_permission
            .push((place, predicate_permission_amount));
        Ok(())
    }

    pub(in super::super) fn close_ref(
        &mut self,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<Option<vir_typed::VariableDecl>> {
        let (opened_place, permission) = self.opened_ref_permission.pop().unwrap();
        assert_eq!(place, &opened_place);
        if !place.is_behind_pointer_dereference() {
            let state = self.get_predicates_state_mut(place)?;
            let precise_permission = state.close_ref(place)?;
            assert_eq!(permission, precise_permission);
        }
        Ok(permission)
    }

    pub(in super::super) fn is_opened_ref(
        &self,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<Option<&Option<vir_typed::VariableDecl>>> {
        if !place.is_behind_pointer_dereference() {
            let state = self.get_predicates_state(place)?;
            state.is_opened_ref(place)
        } else {
            Ok(self
                .opened_ref_permission
                .last()
                .map(|(_, permission)| permission))
        }
    }

    pub(in super::super) fn iter_mut(
        &mut self,
    ) -> SpannedEncodingResult<impl Iterator<Item = &mut PredicateState>> {
        self.check_no_default_position();
        Ok(self.predicates.values_mut())
    }

    pub(in super::super) fn get_predicates_state_mut(
        &mut self,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<&mut PredicateState> {
        Ok(self
            .try_get_predicates_state_mut(place)?
            .unwrap_or_else(|| unreachable!("place: {place}")))
    }

    pub(super) fn try_get_predicates_state_mut(
        &mut self,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<Option<&mut PredicateState>> {
        self.check_no_default_position();
        let base = place.get_base().erase_lifetime();
        Ok(self.predicates.get_mut(&base))
    }

    pub(in super::super) fn try_get_predicates_state(
        &self,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<Option<&PredicateState>> {
        self.check_no_default_position();
        let base = place.get_base().erase_lifetime();
        let state = self.predicates.get(&base);
        Ok(state)
    }

    pub(in super::super) fn get_predicates_state(
        &self,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<&PredicateState> {
        let state = self
            .try_get_predicates_state(place)?
            .unwrap_or_else(|| unreachable!("place: {place}"));
        Ok(state)
    }

    pub(in super::super) fn remove_empty_states(
        &mut self,
        variable: &vir_typed::VariableDecl,
    ) -> SpannedEncodingResult<()> {
        if let Some(predicate) = self.predicates.get_mut(variable) {
            if predicate.is_empty() {
                self.predicates.remove(variable);
            } else {
                predicate.remove_empty_states()?;
            }
        }
        Ok(())
    }

    /// Remove all permissions. This is intended to be used only by `LeakAll` statement.
    pub(in super::super) fn clear(&mut self) -> SpannedEncodingResult<()> {
        self.check_no_default_position();
        self.predicates.clear();
        Ok(())
    }

    pub(super) fn check_no_default_position(&self) {
        if cfg!(debug_assertions) {
            for predicate in self.predicates.values() {
                predicate.check_no_default_position();
            }
        }
    }

    pub(in super::super) fn check_consistency(&self) {
        if cfg!(debug_assertions) {
            for predicate in self.predicates.values() {
                predicate.check_consistency();
            }
        }
    }
}
