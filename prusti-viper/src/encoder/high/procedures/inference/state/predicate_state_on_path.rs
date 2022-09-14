use super::{
    super::permission::{Blocked, Permission, PermissionKind},
    places::PlaceWithDeadLifetimes,
    Places,
};
use crate::encoder::errors::SpannedEncodingResult;
use log::debug;
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    common::display,
    typed::{
        self as vir_typed,
        operations::{lifetimes::WithLifetimes, ty::Typed},
    },
};

#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub(in super::super) struct PredicateStateOnPath {
    owned_non_aliased: Places,
    memory_block_stack: Places,
    /// A map from opened reference places to a permission variable or `None` if
    /// the place was opened with full permission.
    opened_references: BTreeMap<vir_typed::Expression, Option<vir_typed::VariableDecl>>,
    /// place → (lifetime, is_reborrow)
    blocked: BTreeMap<vir_typed::Expression, (vir_typed::ty::LifetimeConst, bool)>,
    dead_lifetimes: BTreeSet<vir_typed::ty::LifetimeConst>,
}

pub(in super::super) struct DeadLifetimeReport {
    pub(in super::super) dead_references: BTreeSet<vir_typed::Expression>,
    pub(in super::super) dead_dereferences: BTreeSet<vir_typed::Expression>,
    pub(in super::super) places_with_dead_lifetimes: Vec<PlaceWithDeadLifetimes>,
    pub(in super::super) blocked_dead_dereferences:
        BTreeMap<vir_typed::Expression, vir_typed::ty::LifetimeConst>,
}

impl std::fmt::Display for PredicateStateOnPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "    owned_non_aliased ({}):",
            self.owned_non_aliased.len()
        )?;
        for place in &self.owned_non_aliased {
            writeln!(f, "      {place}")?;
        }
        writeln!(
            f,
            "    memory_block_stack ({}):",
            self.memory_block_stack.len()
        )?;
        for place in &self.memory_block_stack {
            writeln!(f, "      {place}")?;
        }
        writeln!(
            f,
            "    opened_references ({}):",
            self.opened_references.len()
        )?;
        for (place, permission) in &self.opened_references {
            writeln!(
                f,
                "      {place}: {}",
                display::option!(permission, "{}", "none")
            )?;
        }
        writeln!(f, "    blocked ({}):", self.blocked.len())?;
        for (place, (lifetime, is_reborrow)) in &self.blocked {
            writeln!(
                f,
                "      &{lifetime} {} {place}",
                (if *is_reborrow { "reborrow" } else { "" })
            )?;
        }
        Ok(())
    }
}

impl PredicateStateOnPath {
    pub(super) fn new(permission: Permission) -> Self {
        let mut state = Self::default();
        state.insert_permission(permission);
        state
    }

    pub(super) fn is_empty(&self) -> bool {
        self.owned_non_aliased.is_empty()
            && self.memory_block_stack.is_empty()
            // && self.opened_references.is_empty()
            && self.blocked.is_empty()
    }

    pub(super) fn contains_only_leakable(&self) -> bool {
        self.memory_block_stack.is_empty()
            && self.owned_non_aliased.iter().all(|place| {
                // `UniqueRef` and `FracRef` predicates can be leaked.
                place.get_last_dereferenced_reference().is_some()
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

    #[tracing::instrument(level = "debug", skip(self))]
    pub(in super::super) fn remove(
        &mut self,
        kind: PermissionKind,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        if !self.places_mut(kind).remove(place) {
            debug!("not found: {} in {:?}", place, kind);
        }
        Ok(())
    }

    pub(in super::super) fn remove_mut_borrowed(
        &mut self,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(
            self.blocked.remove(place).is_some(),
            "not found in blocked: {place}",
        );
        Ok(())
    }

    pub(in super::super) fn insert(
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

    pub(super) fn insert_permission(&mut self, permission: Permission) {
        match permission {
            Permission::MemoryBlock(place) => {
                assert!(self.memory_block_stack.insert(place));
            }
            Permission::Owned(place) => {
                assert!(self.owned_non_aliased.insert(place));
            }
            Permission::Blocked(Blocked {
                lifetime,
                place,
                is_reborrow,
            }) => {
                assert!(self
                    .blocked
                    .insert(place, (lifetime, is_reborrow))
                    .is_none());
            }
        }
    }

    pub(super) fn remove_permission(&mut self, permission: &Permission) {
        match permission {
            Permission::MemoryBlock(place) => {
                assert!(self.memory_block_stack.remove(place));
            }
            Permission::Owned(place) => {
                assert!(self.owned_non_aliased.remove(place));
            }
            Permission::Blocked(_) => {
                unreachable!()
            }
        }
    }

    pub(super) fn open_ref(
        &mut self,
        place: vir_typed::Expression,
        predicate_permission_amount: Option<vir_typed::VariableDecl>,
    ) -> SpannedEncodingResult<()> {
        assert!(place.is_place());
        assert!(self.owned_non_aliased.contains(&place));
        for opened_place in self.opened_references.keys() {
            if opened_place.has_prefix(&place) || place.has_prefix(opened_place) {
                unimplemented!("FIXME: a proper error message: failed to open {place} because {opened_place} is already opened");
            }
        }
        assert!(self
            .opened_references
            .insert(place, predicate_permission_amount)
            .is_none());
        Ok(())
    }

    pub(super) fn close_ref(
        &mut self,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<Option<vir_typed::VariableDecl>> {
        assert!(place.is_place());
        assert!(self.owned_non_aliased.contains(place) || place.is_behind_pointer_dereference());
        let predicate_permission_amount = self
            .opened_references
            .remove(place)
            .unwrap_or_else(|| unreachable!("place is not opened: {}", place));
        Ok(predicate_permission_amount)
    }

    pub(in super::super) fn is_opened_ref(
        &self,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<Option<&Option<vir_typed::VariableDecl>>> {
        for (opened_place, permission) in &self.opened_references {
            if place.has_prefix(opened_place) {
                return Ok(Some(permission));
            }
        }
        Ok(None)
    }

    pub(in super::super) fn contains(
        &self,
        kind: PermissionKind,
        place: &vir_typed::Expression,
    ) -> bool {
        self.check_no_default_position();
        assert!(place.is_place());
        self.places(kind).contains(place)
    }

    /// Returns a witness if it exists.
    ///
    /// The witness must not be enum's discriminant because it is useless for
    /// determining the variant statically.
    pub(in super::super) fn contains_non_discriminant_with_prefix(
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

    pub(in super::super) fn contains_discriminant_with_prefix(
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

    pub(in super::super) fn get_all_with_prefix<'a>(
        &'a self,
        kind: PermissionKind,
        prefix: &'a vir_typed::Expression,
    ) -> impl Iterator<Item = &'a vir_typed::Expression> {
        self.check_no_default_position();
        self.places(kind).iter().filter(|p| p.has_prefix(prefix))
    }

    pub(in super::super) fn contains_prefix_of(
        &self,
        kind: PermissionKind,
        place: &vir_typed::Expression,
    ) -> bool {
        self.check_no_default_position();
        self.places(kind).iter().any(|p| place.has_prefix(p))
    }

    pub(in super::super) fn find_prefix(
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

    pub(in super::super) fn collect_owned_with_prefix(
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

    pub(in super::super) fn contains_blocked(
        &self,
        place: &vir_typed::Expression,
    ) -> SpannedEncodingResult<Option<(&vir_typed::Expression, &vir_typed::ty::LifetimeConst, bool)>>
    {
        Ok(self
            .blocked
            .iter()
            .find(|(p, _)| {
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
            })
            .map(|(place, (lifetime, reborrow))| (place, lifetime, *reborrow)))
    }

    pub(in super::super) fn clear(&mut self) -> SpannedEncodingResult<()> {
        self.owned_non_aliased.clear();
        self.memory_block_stack.clear();
        self.blocked.clear();
        self.check_no_default_position();
        Ok(())
    }

    pub(super) fn check_no_default_position(&self) {
        for expr in self
            .owned_non_aliased
            .iter()
            .chain(&self.memory_block_stack)
        {
            expr.check_no_default_position();
        }
        for place in self.blocked.keys() {
            place.check_no_default_position();
        }
    }

    pub(in super::super) fn check_consistency(&self) {
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
            assert!(!self.is_empty(), "self: {self}");
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
    ///         FIXME: We do the same as in 2.1.
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
    pub(in super::super) fn mark_lifetime_dead(
        &mut self,
        lifetime: &vir_typed::ty::LifetimeConst,
    ) -> SpannedEncodingResult<Option<DeadLifetimeReport>> {
        if self.dead_lifetimes.contains(lifetime) {
            // The lifetime is already dead on this trace.
            return Ok(None);
        }
        let dead_references: BTreeSet<_> = self
            .owned_non_aliased
            .drain_filter(|place| {
                if let vir_typed::Type::Reference(reference_type) = place.get_type() {
                    &reference_type.lifetime == lifetime
                } else {
                    false
                }
            })
            .collect();
        for reference in &dead_references {
            self.insert(PermissionKind::MemoryBlock, reference.clone())?;
        }
        let all_dead_dereferences: Vec<_> = self
            .owned_non_aliased
            .drain_filter(|place| place.is_deref_of_lifetime(lifetime))
            .collect();
        let blocked_all_dead_dereferences: Vec<_> = self
            .blocked
            .drain_filter(|place, _| place.is_deref_of_lifetime(lifetime))
            .collect();
        // Case 2.1.
        let mut dead_dereferences = BTreeSet::new();
        let mut blocked_dead_dereferences = BTreeMap::new();
        // Case 2.2.
        let mut partial_dead_references = BTreeSet::new();
        for place in all_dead_dereferences {
            // if let vir_typed::Expression::Deref(vir_typed::Deref { box base, .. }) = &place {
            //     if let vir_typed::Type::Reference(vir_typed::ty::Reference {
            //         lifetime: lft, ..
            //     }) = base.get_type()
            //     {
            //         if lifetime == lft {
            //             self.memory_block_stack.insert(base.clone());
            //             dead_references.insert(place);
            //             continue;
            //         }
            //     }
            // }
            // partial_dead_references.insert(place.into_ref_with_lifetime(lifetime));
            if let Some((deref_lifetime, _)) = place.get_dereference_kind() {
                if &deref_lifetime == lifetime {
                    dead_dereferences.insert(place.clone());
                }
            }
            partial_dead_references.insert(place.into_ref_with_lifetime(lifetime));
        }
        for place in partial_dead_references {
            self.memory_block_stack.insert(place);
        }
        for (place, (reborrowing_lifetime, is_reborrow)) in blocked_all_dead_dereferences {
            assert!(is_reborrow, "place: {place}");
            if let Some((deref_lifetime, _)) = place.get_dereference_kind() {
                if &deref_lifetime == lifetime {
                    blocked_dead_dereferences.insert(place.clone(), reborrowing_lifetime);
                }
            }
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
        Ok(Some(DeadLifetimeReport {
            dead_references,
            dead_dereferences,
            places_with_dead_lifetimes,
            blocked_dead_dereferences,
        }))
    }

    pub(in super::super) fn equal_ignoring_dead_lifetimes(&self, other: &Self) -> bool {
        self.owned_equal(other)
            && self.memory_block_stack_equal(other)
            && self.blocked_equal(other)
            && self.opened_references == other.opened_references
    }

    pub(in super::super) fn owned_equal(&self, other: &Self) -> bool {
        self.owned_non_aliased == other.owned_non_aliased
    }

    pub(in super::super) fn memory_block_stack_equal(&self, other: &Self) -> bool {
        self.memory_block_stack == other.memory_block_stack
    }

    pub(in super::super) fn blocked_equal(&self, other: &Self) -> bool {
        self.blocked == other.blocked
    }
}
