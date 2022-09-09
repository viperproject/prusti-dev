use super::permission::{MutBorrowed, Permission, PermissionKind};
use crate::encoder::errors::SpannedEncodingResult;
use log::debug;
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    middle as vir_mid,
    typed::{
        self as vir_typed,
        operations::{lifetimes::WithLifetimes, ty::Typed},
    },
};

#[derive(Clone, Debug, Default)]
pub(super) struct Places {
    /// A map from a place with erased lifetimes to normal place. We need this
    /// because we do not take lifetimes into account when comparing.
    ///
    /// FIXME: Define an expression and type wrappers that when ordered do not
    /// take lifetimes and constants into account, so that we can use `BTreeSet`
    /// here and avoid many `clone()` (also in `has_prefix`).
    places: BTreeMap<vir_typed::Expression, vir_typed::Expression>,
}

#[derive(Clone, Default, Debug)]
pub(super) struct PredicateState {
    owned_non_aliased: Places,
    memory_block_stack: Places,
    mut_borrowed: BTreeMap<vir_typed::Expression, vir_typed::ty::LifetimeConst>,
    dead_lifetimes: BTreeSet<vir_typed::ty::LifetimeConst>,
}

pub(super) struct PlaceWithDeadLifetimes {
    pub(super) place: vir_typed::Expression,
    pub(super) lifetime: vir_typed::ty::LifetimeConst,
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
    conditional: BTreeMap<vir_mid::BlockMarkerCondition, PredicateState>,
}

impl Places {
    pub(super) fn len(&self) -> usize {
        self.places.len()
    }

    pub(super) fn is_empty(&self) -> bool {
        self.places.is_empty()
    }

    pub(super) fn insert(&mut self, place: vir_typed::Expression) -> bool {
        self.places
            .insert(place.clone().erase_lifetime(), place)
            .is_none()
    }

    fn remove(&mut self, place: &vir_typed::Expression) -> bool {
        // FIXME: Avoid cloning.
        self.places
            .remove(&place.clone().erase_lifetime())
            .is_some()
    }

    fn contains(&self, place: &vir_typed::Expression) -> bool {
        // FIXME: Avoid cloning.
        self.places.contains_key(&place.clone().erase_lifetime())
    }

    fn iter(&self) -> impl Iterator<Item = &'_ vir_typed::Expression> {
        self.places.values()
    }

    fn clear(&mut self) {
        self.places.clear()
    }

    pub(super) fn drain_filter<'a, F>(
        &'a mut self,
        mut pred: F,
    ) -> impl Iterator<Item = vir_typed::Expression> + 'a
    where
        F: 'a + FnMut(&vir_typed::Expression) -> bool,
    {
        self.places
            .drain_filter(move |_, place| pred(place))
            .map(|(_, place)| place)
    }
}

impl<'a> IntoIterator for &'a Places {
    type Item = &'a vir_typed::Expression;

    type IntoIter = Box<dyn Iterator<Item = Self::Item> + 'a>;

    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.places.iter().map(|(_, place)| place))
    }
}

impl IntoIterator for Places {
    type Item = vir_typed::Expression;

    type IntoIter = Box<dyn Iterator<Item = Self::Item>>;

    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.places.into_iter().map(|(_, place)| place))
    }
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
        writeln!(f, "mut_borrowed ({}):", self.mut_borrowed.len())?;
        for (place, lifetime) in &self.mut_borrowed {
            writeln!(f, "  &{} {}", lifetime, place)?;
        }
        Ok(())
    }
}

impl PredicateState {
    fn is_empty(&self) -> bool {
        self.owned_non_aliased.is_empty()
            && self.memory_block_stack.is_empty()
            && self.mut_borrowed.is_empty()
    }

    fn contains_only_leakable(&self) -> bool {
        self.memory_block_stack.is_empty()
            && self.owned_non_aliased.iter().all(|place| {
                // `UniqueRef` and `FracRef` predicates can be leaked.
                place.get_dereference_base().is_some()
            })
    }

    fn places_mut(&mut self, kind: PermissionKind) -> &mut Places {
        self.check_no_default_position();
        match kind {
            PermissionKind::MemoryBlock => &mut self.memory_block_stack,
            PermissionKind::Owned => &mut self.owned_non_aliased,
        }
    }

    fn places(&self, kind: PermissionKind) -> &Places {
        self.check_no_default_position();
        match kind {
            PermissionKind::MemoryBlock => &self.memory_block_stack,
            PermissionKind::Owned => &self.owned_non_aliased,
        }
    }

    pub(super) fn remove(
        &mut self,
        kind: PermissionKind,
        place: &vir_typed::Expression,
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

    pub(super) fn remove_mut_borrowed(
        &mut self,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(
            self.mut_borrowed.remove(place).is_some(),
            "not found in mut_borrowed: {}",
            place,
        );
        Ok(())
    }

    pub(super) fn insert(
        &mut self,
        kind: PermissionKind,
        place: vir_typed::Expression,
    ) -> SpannedEncodingResult<()> {
        place.check_no_default_position();
        assert!(place.is_place());
        assert!(
            self.places_mut(kind).insert(place),
            "already contains a place"
        );
        Ok(())
    }

    pub(super) fn contains(&self, kind: PermissionKind, place: &vir_typed::Expression) -> bool {
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
        prefix: &vir_typed::Expression,
    ) -> Option<&vir_typed::Expression> {
        self.check_no_default_position();
        self.places(kind).iter().find(|p| {
            p.has_prefix(prefix) && {
                if let vir_typed::Expression::Field(field) = p {
                    !field.field.is_discriminant()
                } else {
                    true
                }
            }
        })
    }

    pub(super) fn contains_discriminant_with_prefix(
        &self,
        prefix: &vir_typed::Expression,
    ) -> Option<(PermissionKind, &vir_typed::Expression)> {
        let owned = self
            .places(PermissionKind::Owned)
            .iter()
            .map(|place| (PermissionKind::Owned, place));
        let memory_block = self
            .places(PermissionKind::MemoryBlock)
            .iter()
            .map(|place| (PermissionKind::MemoryBlock, place));
        owned.chain(memory_block).find(|(_, p)| {
            if let vir_typed::Expression::Field(field) = p {
                field.field.is_discriminant() && &*field.base == prefix
            } else {
                false
            }
        })
    }

    pub(super) fn get_all_with_prefix<'a>(
        &'a self,
        kind: PermissionKind,
        prefix: &'a vir_typed::Expression,
    ) -> impl Iterator<Item = &'a vir_typed::Expression> {
        self.check_no_default_position();
        self.places(kind).iter().filter(|p| p.has_prefix(prefix))
    }

    pub(super) fn contains_prefix_of(
        &self,
        kind: PermissionKind,
        place: &vir_typed::Expression,
    ) -> bool {
        self.check_no_default_position();
        self.places(kind).iter().any(|p| place.has_prefix(p))
    }

    pub(super) fn find_prefix(
        &self,
        kind: PermissionKind,
        place: &vir_typed::Expression,
    ) -> Option<vir_typed::Expression> {
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
        prefix: &vir_typed::Expression,
    ) -> SpannedEncodingResult<Vec<vir_typed::Expression>> {
        self.check_no_default_position();
        let collected_places = self
            .owned_non_aliased
            .iter()
            .filter(|place| place.has_prefix(prefix))
            .cloned()
            .collect();
        Ok(collected_places)
    }

    pub(super) fn contains_blocked(
        &self,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<Option<(&vir_typed::Expression, &vir_typed::ty::LifetimeConst)>>
    {
        Ok(self.mut_borrowed.iter().find(|(p, _)| {
            let prefix_expr = match p {
                vir_typed::Expression::BuiltinFuncApp(vir_typed::BuiltinFuncApp {
                    function: vir_typed::BuiltinFunc::Index,
                    type_arguments: _,
                    arguments,
                    ..
                }) => &arguments[0],
                _ => *p,
            };
            place.has_prefix(prefix_expr) || prefix_expr.has_prefix(place)
        }))
    }

    pub(super) fn clear(&mut self) -> SpannedEncodingResult<()> {
        self.owned_non_aliased.clear();
        self.memory_block_stack.clear();
        self.mut_borrowed.clear();
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
        for place in self.mut_borrowed.keys() {
            place.check_no_default_position();
        }
    }

    pub(super) fn check_consistency(&self) {
        if cfg!(debug_assertions) {
            for place1 in &self.owned_non_aliased {
                for place2 in &self.owned_non_aliased {
                    if place1 != place2 {
                        assert!(
                            !place1.has_prefix(place2),
                            "({place1}).has_prefix({place2})"
                        );
                    }
                }
                for place2 in &self.memory_block_stack {
                    if place1 != place2 {
                        assert!(
                            !place1.has_prefix(place2),
                            "({place1}).has_prefix({place2})"
                        );
                    }
                }
            }
            for place1 in &self.memory_block_stack {
                for place2 in &self.owned_non_aliased {
                    if place1 != place2 {
                        assert!(
                            !place1.has_prefix(place2),
                            "({place1}).has_prefix({place2})"
                        );
                    }
                }
                for place2 in &self.memory_block_stack {
                    if place1 != place2 {
                        assert!(
                            !place1.has_prefix(place2),
                            "({place1}).has_prefix({place2})"
                        );
                    }
                }
            }
        }
    }

    /// When a lifetime dies, we can three kinds of places:
    ///
    /// 1.  Places that end with a type containing the dead lifetime as a
    ///     parameter. For example, `z` in the following snippet:
    ///
    ///     ```ignore
    ///     fn callee<'a>(a: &'a mut T3) -> T4<'a> {
    ///         T4 {
    ///             f: a,
    ///         }
    ///     }
    ///     let z = callee(&mut a);
    ///     let _ = z;
    ///     ```
    ///
    ///     Since `T4` might be unsafe, we cannot just unfold it. Therefore, we
    ///     need to call a builtin function that marks the lifetime `'a` as dead
    ///     in `z`.
    /// 2.  Places that dereference a reference with an expiring lifetime. This
    ///     variant has two cases we care about:
    ///
    ///     1.  `UniqueRef` is present. For example, `x` in the following
    ///         snippet:
    ///
    ///         ```ignore
    ///         let x = &mut a;
    ///         // dead(x)
    ///         ```
    ///
    ///         In this case, we know that we have a complete `UniqueRef(*x)`
    ///         and can replace it with a `MemoryBlock(x)`.
    ///
    ///     2.  At least some part of `UniqueRef` is missing. This happens when
    ///         we have a reborrow:
    ///
    ///         ```ignore
    ///         let x = &mut a;
    ///         let y = &mut *x.f;
    ///         // dead(x)
    ///         ```
    ///
    ///         Note: since `y` is borrowing not `x`, but `a.f`, `x` can dye
    ///         before `y`.
    ///
    ///         In this case, we need to forget about `UniqueRef` parts (delete
    ///         them from fold-unfold state) and replace with `MemoryBlock(x)`
    ///         because we know that this is what we have in the verifier's
    ///         state.
    ///
    ///     If at some later point a folded version is requested, the
    ///     fold-unfold algorithm should check that the lifetime is already dead
    ///     and require only the backing memory block for producing `Owned` of
    ///     reference.
    pub(super) fn mark_lifetime_dead(
        &mut self,
        lifetime: &vir_typed::ty::LifetimeConst,
    ) -> (BTreeSet<vir_typed::Expression>, Vec<PlaceWithDeadLifetimes>) {
        assert!(
            !self.dead_lifetimes.contains(lifetime),
            "The lifetime {} is already dead.",
            lifetime
        );
        let all_dead_references: Vec<_> = self
            .owned_non_aliased
            .drain_filter(|place| place.is_deref_of_lifetime(lifetime))
            .collect();
        // Case 2.1.
        let mut dead_references = BTreeSet::new();
        // Case 2.2.
        let mut partial_dead_references = BTreeSet::new();
        for place in all_dead_references {
            if let vir_typed::Expression::Deref(vir_typed::Deref { box base, .. }) = &place {
                if let vir_typed::Type::Reference(vir_typed::ty::Reference {
                    lifetime: lft, ..
                }) = base.get_type()
                {
                    if lifetime == lft {
                        self.memory_block_stack.insert(base.clone());
                        dead_references.insert(place);
                        continue;
                    }
                }
            }
            partial_dead_references.insert(place.into_ref_with_lifetime(lifetime));
        }
        for place in partial_dead_references {
            self.memory_block_stack.insert(place);
        }
        // Case 1.
        let mut places_with_dead_lifetimes = Vec::new();
        for place in &self.owned_non_aliased {
            let lifetimes = place.get_type().get_lifetimes();
            if lifetimes.contains(lifetime) {
                places_with_dead_lifetimes.push(PlaceWithDeadLifetimes {
                    place: place.clone(),
                    lifetime: lifetime.clone(),
                });
            }
        }
        self.dead_lifetimes.insert(lifetime.clone());
        self.check_consistency();
        (dead_references, places_with_dead_lifetimes)
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
            write!(f, "conditional ({}", condition)?;
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

    pub(in super::super) fn contains_only_leakable(&self) -> bool {
        for state in self.conditional.values() {
            if !state.contains_only_leakable() {
                return false;
            }
        }
        self.unconditional.contains_only_leakable()
    }

    pub(in super::super) fn reset_incoming_labels_with(
        &mut self,
        incoming_label: vir_mid::BasicBlockId,
        path_disambiguators: &[vir_mid::BasicBlockId],
    ) -> SpannedEncodingResult<()> {
        self.conditional = std::mem::take(&mut self.conditional)
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
        Self::merge_unconditional_mut_borrowed(
            &mut self.unconditional.mut_borrowed,
            incoming_state.unconditional.mut_borrowed,
            &mut new_conditional.mut_borrowed,
            &mut incoming_conditional.mut_borrowed,
        )?;

        // Copy over conditional.
        let empty_vec = Vec::new();
        let incoming_label_path_disambiguators = path_disambiguators
            .get(&(incoming_label.clone(), current_label.clone()))
            .unwrap_or(&empty_vec);
        self.conditional
            .extend(
                incoming_state
                    .conditional
                    .into_iter()
                    .map(|(mut labels, state)| {
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
                    }),
            );

        // Create new conditionals.
        if !new_conditional.is_empty() {
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
                self.conditional.insert(
                    vir_mid::BlockMarkerCondition { elements },
                    new_conditional.clone(),
                );
            }
        }
        if !incoming_conditional.is_empty() {
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
            self.conditional.insert(
                vir_mid::BlockMarkerCondition { elements },
                incoming_conditional,
            );
        }
        self.incoming_labels.push(incoming_label);
        self.check_no_default_position();
        Ok(())
    }

    fn merge_unconditional_mut_borrowed(
        unconditional: &mut BTreeMap<vir_typed::Expression, vir_typed::ty::LifetimeConst>,
        incoming_unconditional: BTreeMap<vir_typed::Expression, vir_typed::ty::LifetimeConst>,
        new_conditional: &mut BTreeMap<vir_typed::Expression, vir_typed::ty::LifetimeConst>,
        incoming_conditional: &mut BTreeMap<vir_typed::Expression, vir_typed::ty::LifetimeConst>,
    ) -> SpannedEncodingResult<()> {
        let mut unconditional_predicates = BTreeMap::default();
        // Unconditional: merge incoming into self.
        for (predicate, lifetime) in &incoming_unconditional {
            if unconditional.contains_key(predicate) {
                unconditional_predicates.insert(predicate, lifetime);
            } else {
                incoming_conditional.insert(predicate.clone(), lifetime.clone());
            }
        }
        // Unconditional: check what needs to be made conditional.
        for (predicate, lifetime) in unconditional
            .drain_filter(|predicate, _| !unconditional_predicates.contains_key(predicate))
        {
            new_conditional.insert(predicate, lifetime);
        }
        Ok(())
    }

    fn merge_unconditional(
        unconditional: &mut Places,
        incoming_unconditional: Places,
        new_conditional: &mut Places,
        incoming_conditional: &mut Places,
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
        place: vir_typed::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(self.unconditional.memory_block_stack.insert(place));
        self.check_no_default_position();
        Ok(())
    }

    pub(in super::super) fn insert_owned(
        &mut self,
        place: vir_typed::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(self.unconditional.owned_non_aliased.insert(place));
        self.check_no_default_position();
        Ok(())
    }

    pub(in super::super) fn insert_mut_borrowed(
        &mut self,
        borrow: MutBorrowed,
    ) -> SpannedEncodingResult<()> {
        assert!(borrow.place.is_place());
        assert!(self
            .unconditional
            .mut_borrowed
            .insert(borrow.place, borrow.lifetime)
            .is_none());
        self.check_no_default_position();
        Ok(())
    }

    pub(in super::super) fn remove_memory_block(
        &mut self,
        place: &vir_typed::Expression,
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
        place: &vir_typed::Expression,
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
            Permission::MutBorrowed(borrow) => self.insert_mut_borrowed(borrow)?,
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
            Permission::MutBorrowed(_) => unreachable!(),
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
        impl Iterator<Item = (&vir_mid::BlockMarkerCondition, &mut PredicateState)>,
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

    pub(super) fn check_consistency(&self) {
        if cfg!(debug_assertions) {
            self.unconditional.check_consistency();
            for predicates in self.conditional.values() {
                predicates.check_consistency();
            }
        }
    }
}
