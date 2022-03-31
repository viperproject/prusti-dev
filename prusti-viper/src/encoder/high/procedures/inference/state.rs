use std::collections::{BTreeMap, BTreeSet};

use super::permission::{Permission, PermissionKind};
use crate::encoder::errors::SpannedEncodingResult;
use log::debug;
use std::fmt::Write;
use vir_crate::{high as vir_high, middle as vir_mid};

#[derive(Clone, Default)]
pub(super) struct PredicateState {
    owned_non_aliased: BTreeSet<vir_high::Expression>,
    memory_block_stack: BTreeSet<vir_high::Expression>,
}

#[derive(Clone)]
pub(in super::super) struct FoldUnfoldState {
    /// If this state is a merge of multiple incoming states, then
    /// `incoming_labels` contains the list of basic blocks from where the
    /// already merged states came.
    incoming_labels: Vec<vir_mid::BasicBlockId>,
    /// `OwnedNonAliased` and `MemoryBlock` predicates that are unconditionally
    /// present in the current state.
    unconditional: PredicateState,
    /// `OwnedNonAliased` and `MemoryBlock` predicates that are present in the
    /// current state if we came through the blocks with labels specified in the
    /// key.
    ///
    /// Invariant: the last label in each key must be one of the
    /// `incoming_labels`.
    ///
    /// Invariant: only non-empty entries are present.
    conditional: BTreeMap<Vec<vir_mid::BasicBlockId>, PredicateState>,
}

impl std::fmt::Display for PredicateState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f)?;
        writeln!(f, "owned_non_aliased ({}):", self.owned_non_aliased.len())?;
        for place in &self.owned_non_aliased {
            writeln!(f, "  {}", place)?;
        }
        writeln!(f, "memory_block_stack ({}):", self.memory_block_stack.len())?;
        for place in &self.memory_block_stack {
            writeln!(f, "  {}", place)?;
        }
        Ok(())
    }
}

impl PredicateState {
    fn is_empty(&self) -> bool {
        self.owned_non_aliased.is_empty() && self.memory_block_stack.is_empty()
    }

    fn places_mut(&mut self, kind: PermissionKind) -> &mut BTreeSet<vir_high::Expression> {
        self.check_no_default_position();
        match kind {
            PermissionKind::MemoryBlock => &mut self.memory_block_stack,
            PermissionKind::Owned => &mut self.owned_non_aliased,
        }
    }

    fn places(&self, kind: PermissionKind) -> &BTreeSet<vir_high::Expression> {
        self.check_no_default_position();
        match kind {
            PermissionKind::MemoryBlock => &self.memory_block_stack,
            PermissionKind::Owned => &self.owned_non_aliased,
        }
    }

    pub(super) fn remove(
        &mut self,
        kind: PermissionKind,
        place: &vir_high::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(
            self.places_mut(kind).remove(place),
            "not found: {} in {:?}",
            place,
            kind
        );
        Ok(())
    }

    pub(super) fn insert(
        &mut self,
        kind: PermissionKind,
        place: vir_high::Expression,
    ) -> SpannedEncodingResult<()> {
        place.check_no_default_position();
        assert!(place.is_place());
        assert!(
            self.places_mut(kind).insert(place),
            "already contains a place"
        );
        Ok(())
    }

    pub(super) fn contains(&self, kind: PermissionKind, place: &vir_high::Expression) -> bool {
        self.check_no_default_position();
        assert!(place.is_place());
        self.places(kind).contains(place)
    }

    /// Returns a witness if it exists.
    ///
    /// The witness must not be enum's discriminant because it is useless for
    /// determining the variant statically.
    pub(super) fn contains_non_discriminant_with_prefix(
        &self,
        kind: PermissionKind,
        prefix: &vir_high::Expression,
    ) -> Option<&vir_high::Expression> {
        self.check_no_default_position();
        self.places(kind).iter().find(|p| {
            p.has_prefix(prefix) && {
                if let vir_high::Expression::Field(field) = p {
                    !field.field.is_discriminant()
                } else {
                    true
                }
            }
        })
    }

    pub(super) fn get_all_with_prefix<'a>(
        &'a self,
        kind: PermissionKind,
        prefix: &'a vir_high::Expression,
    ) -> impl Iterator<Item = &'a vir_high::Expression> {
        self.check_no_default_position();
        self.places(kind).iter().filter(|p| p.has_prefix(prefix))
    }

    pub(super) fn contains_prefix_of(
        &self,
        kind: PermissionKind,
        place: &vir_high::Expression,
    ) -> bool {
        self.check_no_default_position();
        self.places(kind).iter().any(|p| place.has_prefix(p))
    }

    pub(super) fn find_prefix(
        &self,
        kind: PermissionKind,
        place: &vir_high::Expression,
    ) -> Option<vir_high::Expression> {
        self.check_no_default_position();
        self.places(kind)
            .iter()
            .find(|p| {
                p.check_no_default_position();
                place.has_prefix(p)
            })
            .cloned()
    }

    pub(super) fn collect_owned_with_prefix(
        &self,
        prefix: &vir_high::Expression,
    ) -> SpannedEncodingResult<Vec<vir_high::Expression>> {
        self.check_no_default_position();
        let collected_places = self
            .owned_non_aliased
            .iter()
            .filter(|place| place.has_prefix(prefix))
            .cloned()
            .collect();
        Ok(collected_places)
    }

    fn clear(&mut self) -> SpannedEncodingResult<()> {
        self.owned_non_aliased.clear();
        self.memory_block_stack.clear();
        self.check_no_default_position();
        Ok(())
    }

    fn check_no_default_position(&self) {
        for expr in self
            .owned_non_aliased
            .iter()
            .chain(&self.memory_block_stack)
        {
            expr.check_no_default_position();
        }
    }
}

impl std::fmt::Display for FoldUnfoldState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "incoming labels: ")?;
        for label in &self.incoming_labels {
            write!(f, "{}, ", label)?;
        }
        writeln!(f, "\nunconditional:")?;
        writeln!(f, "{}", self.unconditional)?;
        for (condition, state) in &self.conditional {
            write!(f, "conditional (")?;
            self.debug_write_condition(condition, f)?;
            writeln!(f, "):\n{}", state)?;
        }
        Ok(())
    }
}

impl FoldUnfoldState {
    pub(in super::super) fn new() -> Self {
        Self {
            incoming_labels: Vec::new(),
            unconditional: Default::default(),
            conditional: Default::default(),
        }
    }

    pub(in super::super) fn debug_print(&self) {
        debug!("state:\n{}", self);
    }

    fn debug_write_condition(
        &self,
        condition: &[vir_mid::BasicBlockId],
        writer: &mut dyn Write,
    ) -> std::fmt::Result {
        let mut iterator = condition.iter();
        if let Some(first) = iterator.next() {
            write!(writer, "{}", first)?;
        }
        for label in iterator {
            write!(writer, "→{}", label)?;
        }
        Ok(())
    }

    pub(in super::super) fn is_empty(&self) -> bool {
        self.unconditional.is_empty() && self.conditional.is_empty()
    }

    pub(in super::super) fn reset_incoming_labels_with(
        &mut self,
        incoming_label: vir_mid::BasicBlockId,
    ) -> SpannedEncodingResult<()> {
        self.conditional = std::mem::take(&mut self.conditional)
            .into_iter()
            .map(|(mut labels, state)| {
                labels.push(incoming_label.clone());
                (labels, state)
            })
            .collect();
        self.incoming_labels = vec![incoming_label];
        self.check_no_default_position();
        Ok(())
    }

    /// Merge `incoming_state` coming from block with label `incoming_label`
    /// into `self`.
    pub(in super::super) fn merge(
        &mut self,
        incoming_label: vir_mid::BasicBlockId,
        incoming_state: Self,
    ) -> SpannedEncodingResult<()> {
        let mut new_conditional = PredicateState::default();
        let mut incoming_conditional = PredicateState::default();

        // Move differences between unconditional into conditional.
        Self::merge_unconditional(
            &mut self.unconditional.owned_non_aliased,
            incoming_state.unconditional.owned_non_aliased,
            &mut new_conditional.owned_non_aliased,
            &mut incoming_conditional.owned_non_aliased,
        )?;
        Self::merge_unconditional(
            &mut self.unconditional.memory_block_stack,
            incoming_state.unconditional.memory_block_stack,
            &mut new_conditional.memory_block_stack,
            &mut incoming_conditional.memory_block_stack,
        )?;

        // Copy over conditional.
        self.conditional
            .extend(
                incoming_state
                    .conditional
                    .into_iter()
                    .map(|(mut condition, state)| {
                        condition.push(incoming_label.clone());
                        (condition, state)
                    }),
            );

        // Create new conditionals.
        if !new_conditional.is_empty() {
            for label in &self.incoming_labels {
                self.conditional
                    .insert(vec![label.clone()], new_conditional.clone());
            }
        }
        if !incoming_conditional.is_empty() {
            self.conditional
                .insert(vec![incoming_label.clone()], incoming_conditional);
        }
        self.incoming_labels.push(incoming_label);
        self.check_no_default_position();
        Ok(())
    }

    fn merge_unconditional(
        unconditional: &mut BTreeSet<vir_high::Expression>,
        incoming_unconditional: BTreeSet<vir_high::Expression>,
        new_conditional: &mut BTreeSet<vir_high::Expression>,
        incoming_conditional: &mut BTreeSet<vir_high::Expression>,
    ) -> SpannedEncodingResult<()> {
        let mut unconditional_predicates = BTreeSet::default();
        // Unconditional: merge incoming into self.
        for predicate in incoming_unconditional {
            if unconditional.contains(&predicate) {
                unconditional_predicates.insert(predicate);
            } else {
                incoming_conditional.insert(predicate);
            }
        }
        // Unconditional: check what needs to be made conditional.
        for predicate in
            unconditional.drain_filter(|predicate| !unconditional_predicates.contains(predicate))
        {
            new_conditional.insert(predicate);
        }
        Ok(())
    }

    pub(in super::super) fn insert_memory_block(
        &mut self,
        place: vir_high::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(self.unconditional.memory_block_stack.insert(place));
        self.check_no_default_position();
        Ok(())
    }

    pub(in super::super) fn insert_owned(
        &mut self,
        place: vir_high::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(self.unconditional.owned_non_aliased.insert(place));
        self.check_no_default_position();
        Ok(())
    }

    pub(in super::super) fn remove_memory_block(
        &mut self,
        place: &vir_high::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(
            self.unconditional.memory_block_stack.remove(place),
            "not found place: {}",
            place
        );
        self.check_no_default_position();
        Ok(())
    }

    pub(in super::super) fn remove_owned(
        &mut self,
        place: &vir_high::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(
            self.unconditional.owned_non_aliased.remove(place),
            "not found place: {}",
            place
        );
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
        match permission {
            Permission::MemoryBlock(place) => self.insert_memory_block(place)?,
            Permission::Owned(place) => self.insert_owned(place)?,
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
        match permission {
            Permission::MemoryBlock(place) => self.remove_memory_block(place)?,
            Permission::Owned(place) => self.remove_owned(place)?,
        }
        Ok(())
    }

    pub(super) fn get_unconditional_state(&mut self) -> SpannedEncodingResult<&mut PredicateState> {
        self.check_no_default_position();
        Ok(&mut self.unconditional)
    }

    pub(super) fn get_conditional_states(
        &mut self,
    ) -> SpannedEncodingResult<
        impl Iterator<Item = (&Vec<vir_mid::BasicBlockId>, &mut PredicateState)>,
    > {
        self.check_no_default_position();
        Ok(self.conditional.iter_mut())
    }

    pub(super) fn remove_empty_conditional_states(&mut self) -> SpannedEncodingResult<()> {
        self.check_no_default_position();
        self.conditional.retain(|_, state| !state.is_empty());
        Ok(())
    }

    /// Remove all permissions. This is intended to be used only by `LeakAll` statement.
    pub(super) fn clear(&mut self) -> SpannedEncodingResult<()> {
        self.check_no_default_position();
        self.unconditional.clear()?;
        self.conditional.clear();
        Ok(())
    }

    pub(super) fn check_no_default_position(&self) {
        self.unconditional.check_no_default_position();
        for predicates in self.conditional.values() {
            predicates.check_no_default_position();
        }
    }
}
