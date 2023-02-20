use super::PredicateStateOnPath;
use crate::encoder::{
    errors::SpannedEncodingResult, high::procedures::inference::permission::Permission,
};

use std::collections::BTreeMap;
use vir_crate::middle::{self as vir_mid};

#[derive(Clone, Debug)]
pub(in super::super) enum PredicateState {
    Unconditional(PredicateStateOnPath),
    Conditional(BTreeMap<vir_mid::BlockMarkerCondition, PredicateStateOnPath>),
}

impl std::fmt::Display for PredicateState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PredicateState::Unconditional(state) => write!(f, "Unconditional:\n{state}")?,
            PredicateState::Conditional(states) => {
                writeln!(f, "Conditional:")?;
                for (condition, state) in states {
                    write!(f, "  {condition}:\n{state}")?;
                }
            }
        }
        Ok(())
    }
}

impl PredicateState {
    pub(in super::super) fn new_unconditional(permission: Permission) -> Self {
        Self::Unconditional(PredicateStateOnPath::new(permission))
    }

    fn foreach_mut(&mut self, mut callback: impl FnMut(&mut PredicateStateOnPath)) {
        match self {
            PredicateState::Unconditional(state) => {
                callback(state);
            }
            PredicateState::Conditional(states) => {
                for state in states.values_mut() {
                    callback(state);
                }
            }
        }
    }

    fn foreach(&self, mut callback: impl FnMut(&PredicateStateOnPath)) {
        match self {
            PredicateState::Unconditional(state) => {
                callback(state);
            }
            PredicateState::Conditional(states) => {
                for state in states.values() {
                    callback(state);
                }
            }
        }
    }

    pub(super) fn contains_only_leakable(&self) -> bool {
        let mut only_leakable = true;
        self.foreach(|state| only_leakable = only_leakable && state.contains_only_leakable());
        only_leakable
    }

    pub(super) fn check_no_default_position(&self) {
        self.foreach(|state| state.check_no_default_position());
    }

    pub(super) fn check_consistency(&self) {
        self.foreach(|state| state.check_consistency());
    }

    pub(super) fn insert_permission(
        &mut self,
        permission: Permission,
    ) -> SpannedEncodingResult<()> {
        self.foreach_mut(|state| state.insert_permission(permission.clone()));
        Ok(())
    }

    pub(super) fn remove_permission(
        &mut self,
        permission: &Permission,
    ) -> SpannedEncodingResult<()> {
        self.foreach_mut(|state| state.remove_permission(permission));
        Ok(())
    }

    pub(super) fn is_empty(&self) -> bool {
        let mut empty = true;
        self.foreach(|state| empty = empty && state.is_empty());
        empty
    }

    pub(in super::super) fn remove_empty_states(&mut self) -> SpannedEncodingResult<()> {
        match self {
            PredicateState::Unconditional(state) => {
                assert!(!state.is_empty())
            }
            PredicateState::Conditional(states) => {
                states.retain(|_, state| !state.is_empty());
            }
        }
        Ok(())
    }
}
