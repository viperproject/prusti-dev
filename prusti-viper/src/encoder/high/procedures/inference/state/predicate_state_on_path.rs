use super::{
    super::permission::{MutBorrowed, Permission, PermissionKind},
    places::PlaceWithDeadLifetimes,
    Places,
};
use crate::encoder::errors::SpannedEncodingResult;
use log::debug;
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::typed::{
    self as vir_typed,
    operations::{lifetimes::WithLifetimes, ty::Typed},
};

#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub(in super::super) struct PredicateStateOnPath {
    owned_non_aliased: Places,
    memory_block_stack: Places,
    mut_borrowed: BTreeMap<vir_typed::Expression, vir_typed::ty::LifetimeConst>,
    dead_lifetimes: BTreeSet<vir_typed::ty::LifetimeConst>,
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
        writeln!(f, "    mut_borrowed ({}):", self.mut_borrowed.len())?;
        for (place, lifetime) in &self.mut_borrowed {
            writeln!(f, "      &{lifetime} {place}")?;
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
            && self.mut_borrowed.is_empty()
    }

    pub(super) fn contains_only_leakable(&self) -> bool {
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
            self.mut_borrowed.remove(place).is_some(),
            "not found in mut_borrowed: {place}",
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
            Permission::MutBorrowed(MutBorrowed { lifetime, place }) => {
                assert!(self.mut_borrowed.insert(place, lifetime).is_none());
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
            Permission::MutBorrowed(_) => {
                unreachable!()
            }
        }
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

    pub(in super::super) fn clear(&mut self) -> SpannedEncodingResult<()> {
        self.owned_non_aliased.clear();
        self.memory_block_stack.clear();
        self.mut_borrowed.clear();
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
        for place in self.mut_borrowed.keys() {
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
    ) -> (BTreeSet<vir_typed::Expression>, Vec<PlaceWithDeadLifetimes>) {
        assert!(
            !self.dead_lifetimes.contains(lifetime),
            "The lifetime {lifetime} is already dead."
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
