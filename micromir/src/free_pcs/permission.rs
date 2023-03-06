// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    cmp::Ordering,
    fmt::{Debug, Display, Formatter, Result},
};

use derive_more::{Deref, DerefMut};

use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    index::vec::IndexVec,
    middle::mir::Local,
};

use crate::{Place, PlaceOrdering, PlaceRepacker};

pub type FreeStateUpdate<'tcx> = LocalsState<LocalUpdate<'tcx>>;
#[derive(Clone, Debug, PartialEq, Eq, Deref, DerefMut, Default)]
pub struct LocalUpdate<'tcx>(
    (
        Option<LocalRequirement<'tcx>>,
        Option<PermissionLocal<'tcx>>,
    ),
);

#[derive(Clone, Debug, PartialEq, Eq, Deref, DerefMut, Default)]
pub struct LocalRequirement<'tcx> {
    unalloc_allowed: bool,
    #[deref]
    #[deref_mut]
    place_reqs: FxHashMap<Place<'tcx>, FxHashSet<PermissionKind>>,
}

impl<'tcx> LocalUpdate<'tcx> {
    fn init_pre(&mut self) -> &mut LocalRequirement<'tcx> {
        assert!(self.0 .0.is_none());
        self.0 .0 = Some(LocalRequirement::default());
        self.0 .0.as_mut().unwrap()
    }
    pub(crate) fn requires_unalloc_or_uninit(&mut self, local: Local) {
        let req = self.init_pre();
        req.unalloc_allowed = true;
        self.requires_alloc(local.into(), &[PermissionKind::Uninit]);
    }
    pub(crate) fn requires_alloc(&mut self, place: Place<'tcx>, perms: &[PermissionKind]) {
        let req = if self.0 .0.is_none() {
            self.init_pre()
        } else {
            self.0 .0.as_mut().unwrap()
        };
        assert!(
            req.keys().all(|other| !place.related_to(*other)),
            "{req:?} {place:?} {perms:?}"
        );
        req.insert(place, perms.iter().copied().collect());
    }
    pub(crate) fn requires_unalloc(&mut self) {
        let req = self.init_pre();
        req.unalloc_allowed = true;
    }
    pub(crate) fn requires_alloc_one(&mut self, place: Place<'tcx>, perm: PermissionKind) {
        self.requires_alloc(place, &[perm]);
    }

    pub(crate) fn ensures_unalloc(&mut self) {
        assert!(self.0 .1.is_none());
        self.0 .1 = Some(PermissionLocal::Unallocated);
    }
    pub(crate) fn ensures_alloc(&mut self, place: Place<'tcx>, perm: PermissionKind) {
        if let Some(pre) = &mut self.0 .1 {
            let pre = pre.get_allocated_mut();
            assert!(pre.keys().all(|other| !place.related_to(*other)));
            pre.insert(place, perm);
        } else {
            self.0 .1 = Some(PermissionLocal::Allocated(
                PermissionProjections::new_update(place, perm),
            ));
        }
    }

    /// Used for the edge case of assigning to the same place you copy from, do not use otherwise!
    pub(crate) fn get_pre_for(&self, place: Place<'tcx>) -> Option<&FxHashSet<PermissionKind>> {
        let pre = self.0 .0.as_ref()?;
        pre.get(&place)
    }

    pub(crate) fn get_pre(&self, state: &PermissionLocal<'tcx>) -> Option<PermissionLocal<'tcx>> {
        let pre = self.0 .0.as_ref()?;
        match state {
            PermissionLocal::Unallocated => {
                assert!(pre.unalloc_allowed);
                return Some(PermissionLocal::Unallocated);
            }
            PermissionLocal::Allocated(state) => {
                let mut achievable = PermissionProjections(FxHashMap::default());
                for (place, allowed_perms) in pre.iter() {
                    let related_set = state.find_all_related(*place, None);
                    let mut perm = None;
                    for &ap in allowed_perms {
                        if related_set.minimum >= ap {
                            perm = Some(ap);
                        }
                        if related_set.minimum == ap {
                            break;
                        }
                    }
                    assert!(
                        perm.is_some(),
                        "{place:?}, {allowed_perms:?}, {state:?}, {:?}, {:?}",
                        related_set.minimum,
                        related_set.from
                    );
                    achievable.insert(*place, perm.unwrap());
                }
                Some(PermissionLocal::Allocated(achievable))
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Deref, DerefMut)]
/// Generic state of a set of locals
pub struct LocalsState<T>(IndexVec<Local, T>);

/// The free pcs of all locals
pub type FreeState<'tcx> = LocalsState<PermissionLocal<'tcx>>;

impl<T> FromIterator<T> for LocalsState<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self(IndexVec::from_iter(iter))
    }
}
impl Display for FreeState<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{{")?;
        let mut first = true;
        for state in self.iter() {
            if let PermissionLocal::Allocated(state) = state {
                if !first {
                    write!(f, ", ")?;
                }
                first = false;
                for (i, (place, perm)) in state.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{perm:?} {place:?}")?;
                }
            }
        }
        write!(f, "}}")
    }
}

impl<'tcx> LocalsState<PermissionLocal<'tcx>> {
    pub fn initial(local_count: usize, initial: impl Fn(Local) -> Option<PermissionKind>) -> Self {
        Self(IndexVec::from_fn_n(
            |local: Local| {
                if let Some(perm) = initial(local) {
                    let places = PermissionProjections::new(local, perm);
                    PermissionLocal::Allocated(places)
                } else {
                    PermissionLocal::Unallocated
                }
            },
            local_count,
        ))
    }
    #[tracing::instrument(level = "trace", skip(rp))]
    pub(crate) fn consistency_check(&self, rp: PlaceRepacker<'_, 'tcx>) {
        for p in self.iter() {
            p.consistency_check(rp);
        }
    }
}
impl<T> LocalsState<T> {
    pub fn default(local_count: usize) -> Self
    where
        T: Default + Clone,
    {
        Self(IndexVec::from_elem_n(T::default(), local_count))
    }
    pub fn empty(local_count: usize, initial: T) -> Self
    where
        T: Clone,
    {
        Self(IndexVec::from_elem_n(initial, local_count))
    }
}
impl<'tcx> LocalsState<LocalUpdate<'tcx>> {
    pub fn update_free(self, state: &mut FreeState<'tcx>) {
        for (local, update) in self.0.into_iter_enumerated() {
            if cfg!(debug_assertions) {
                use PermissionLocal::*;
                match (&state[local], update.get_pre(&state[local])) {
                    (_, None) => {}
                    (Unallocated, Some(Unallocated)) => {}
                    (Allocated(local_state), Some(Allocated(pre))) => {
                        for (place, required_perm) in pre.0 {
                            let perm = *local_state.get(&place).unwrap();
                            let is_read = required_perm.is_shared() && perm.is_exclusive();
                            assert!(
                                perm == required_perm || is_read,
                                "Have\n{state:#?}\n{place:#?}\n{perm:#?}\n{required_perm:#?}\n"
                            );
                        }
                    }
                    _ => unreachable!(),
                }
            }
            if let Some(post) = update.0 .1 {
                match (post, &mut state[local]) {
                    (post @ PermissionLocal::Unallocated, _)
                    | (post, PermissionLocal::Unallocated) => state[local] = post,
                    (PermissionLocal::Allocated(post), PermissionLocal::Allocated(state)) => {
                        state.extend(post.0)
                    }
                }
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
/// The permissions of a local
pub enum PermissionLocal<'tcx> {
    Unallocated,
    Allocated(PermissionProjections<'tcx>),
}
impl Debug for PermissionLocal<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            PermissionLocal::Unallocated => write!(f, "U"),
            PermissionLocal::Allocated(a) => write!(f, "{a:?}"),
        }
    }
}

impl<'tcx> PermissionLocal<'tcx> {
    pub fn get_allocated(&self) -> &PermissionProjections<'tcx> {
        match self {
            PermissionLocal::Allocated(places) => places,
            _ => panic!(),
        }
    }
    pub fn get_allocated_mut(&mut self) -> &mut PermissionProjections<'tcx> {
        match self {
            PermissionLocal::Allocated(places) => places,
            _ => panic!(),
        }
    }

    fn consistency_check(&self, rp: PlaceRepacker<'_, 'tcx>) {
        match self {
            PermissionLocal::Unallocated => {}
            PermissionLocal::Allocated(places) => {
                places.consistency_check(rp);
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Deref, DerefMut)]
/// The permissions for all the projections of a place
// We only need the projection part of the place
pub struct PermissionProjections<'tcx>(FxHashMap<Place<'tcx>, PermissionKind>);

impl<'tcx> Debug for PermissionProjections<'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.0.fmt(f)
    }
}

#[derive(Debug)]
pub(crate) struct RelatedSet<'tcx> {
    pub(crate) from: Vec<(Place<'tcx>, PermissionKind)>,
    pub(crate) to: Place<'tcx>,
    pub(crate) minimum: PermissionKind,
    pub(crate) relation: PlaceOrdering,
}
impl<'tcx> RelatedSet<'tcx> {
    pub fn get_from(&self) -> FxHashSet<Place<'tcx>> {
        assert!(matches!(
            self.relation,
            PlaceOrdering::Suffix | PlaceOrdering::Both
        ));
        self.from.iter().map(|(p, _)| *p).collect()
    }
}

impl<'tcx> PermissionProjections<'tcx> {
    pub fn new(local: Local, perm: PermissionKind) -> Self {
        Self([(local.into(), perm)].into_iter().collect())
    }
    pub fn new_uninit(local: Local) -> Self {
        Self::new(local, PermissionKind::Uninit)
    }
    /// Should only be called when creating an update within `ModifiesFreeState`
    pub(crate) fn new_update(place: Place<'tcx>, perm: PermissionKind) -> Self {
        Self([(place, perm)].into_iter().collect())
    }

    /// Returns all related projections of the given place that are contained in this map.
    /// A `Ordering::Less` means that the given `place` is a prefix of the iterator place.
    /// For example: find_all_related(x.f.g) = [(Less, x.f.g.h), (Greater, x.f)]
    /// It also checks that the ordering conforms to the expected ordering (the above would
    /// fail in any situation since all orderings need to be the same)
    #[tracing::instrument(level = "trace", ret)]
    pub(crate) fn find_all_related(
        &self,
        to: Place<'tcx>,
        mut expected: Option<PlaceOrdering>,
    ) -> RelatedSet<'tcx> {
        let mut minimum = None::<PermissionKind>;
        let mut related = Vec::new();
        for (&from, &perm) in &**self {
            if let Some(ord) = from.partial_cmp(to) {
                minimum = if let Some(min) = minimum {
                    Some(min.minimum(perm).unwrap())
                } else {
                    Some(perm)
                };
                if let Some(expected) = expected {
                    assert_eq!(ord, expected);
                } else {
                    expected = Some(ord);
                }
                related.push((from, perm));
            }
        }
        assert!(
            !related.is_empty(),
            "Cannot find related of {to:?} in {self:?}"
        );
        let relation = expected.unwrap();
        if matches!(relation, PlaceOrdering::Prefix | PlaceOrdering::Equal) {
            assert_eq!(related.len(), 1);
        }
        RelatedSet {
            from: related,
            to,
            minimum: minimum.unwrap(),
            relation,
        }
    }
    // pub fn all_related_with_minimum(
    //     &self,
    //     place: Place<'tcx>,
    // ) -> (PermissionKind, PlaceOrdering, Vec<(Place<'tcx>, PermissionKind)>) {
    //     let mut ord = None;
    //     let related: Vec<_> = self
    //         .find_all_related(place, &mut ord)
    //         .map(|(_, p, k)| (p, k))
    //         .collect();
    //     let mut minimum = related.iter().map(|(_, k)| *k).reduce(|acc, k| {
    //         acc.minimum(k).unwrap()
    //     });
    //     (minimum.unwrap(), ord.unwrap(), related)
    // }

    #[tracing::instrument(name = "PermissionProjections::unpack", level = "trace", skip(rp), ret)]
    pub(crate) fn unpack(
        &mut self,
        from: Place<'tcx>,
        to: Place<'tcx>,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<(Place<'tcx>, Place<'tcx>)> {
        debug_assert!(!self.contains_key(&to));
        let (expanded, others) = rp.expand(from, to);
        let perm = self.remove(&from).unwrap();
        self.extend(others.into_iter().map(|p| (p, perm)));
        self.insert(to, perm);
        expanded
    }

    // TODO: this could be implemented more efficiently, by assuming that a valid
    // state can always be packed up to the root
    #[tracing::instrument(name = "PermissionProjections::pack", level = "trace", skip(rp), ret)]
    pub(crate) fn pack(
        &mut self,
        mut from: FxHashSet<Place<'tcx>>,
        to: Place<'tcx>,
        perm: PermissionKind,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<(Place<'tcx>, Place<'tcx>)> {
        debug_assert!(!self.contains_key(&to));
        for place in &from {
            let p = self.remove(place).unwrap();
            assert_eq!(p, perm, "Cannot pack {place:?} with {p:?} into {to:?}");
        }
        let collapsed = rp.collapse(to, &mut from);
        assert!(from.is_empty());
        self.insert(to, perm);
        collapsed
    }

    #[tracing::instrument(name = "PermissionProjections::join", level = "info", skip(rp))]
    pub(crate) fn join(&self, other: &mut Self, rp: PlaceRepacker<'_, 'tcx>) {
        for (&place, &kind) in &**self {
            let related = other.find_all_related(place, None);
            match related.relation {
                PlaceOrdering::Prefix => {
                    let from = related.from[0].0;
                    let joinable_place = rp.joinable_to(from, place);
                    if joinable_place != from {
                        other.unpack(from, joinable_place, rp);
                    }
                    // Downgrade the permission if needed
                    let new_min = kind.minimum(related.minimum).unwrap();
                    if new_min != related.minimum {
                        other.insert(joinable_place, new_min);
                    }
                }
                PlaceOrdering::Equal => {
                    // Downgrade the permission if needed
                    let new_min = kind.minimum(related.minimum).unwrap();
                    if new_min != related.minimum {
                        other.insert(place, new_min);
                    }
                }
                PlaceOrdering::Suffix => {
                    // Downgrade the permission if needed
                    for &(p, k) in &related.from {
                        let new_min = kind.minimum(k).unwrap();
                        if new_min != k {
                            other.insert(p, new_min);
                        }
                    }
                }
                PlaceOrdering::Both => {
                    // Downgrade the permission if needed
                    let min = kind.minimum(related.minimum).unwrap();
                    for &(p, k) in &related.from {
                        let new_min = min.minimum(k).unwrap();
                        if new_min != k {
                            other.insert(p, new_min);
                        }
                    }
                    let cp = rp.common_prefix(related.from[0].0, place);
                    other.pack(related.get_from(), cp, min, rp);
                }
            }
        }
    }

    fn consistency_check(&self, rp: PlaceRepacker<'_, 'tcx>) {
        // All keys unrelated to each other
        let keys = self.keys().copied().collect::<Vec<_>>();
        for (i, p1) in keys.iter().enumerate() {
            for p2 in keys[i + 1..].iter() {
                assert!(!p1.related_to(*p2), "{p1:?} {p2:?}",);
            }
        }
        // Can always pack up to the root
        let root: Place = self.iter().next().unwrap().0.local.into();
        let mut keys = self.keys().copied().collect();
        rp.collapse(root, &mut keys);
        assert!(keys.is_empty());
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum PermissionKind {
    Shared,
    Exclusive,
    Uninit,
}

impl Debug for PermissionKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            PermissionKind::Shared => write!(f, "s"),
            PermissionKind::Exclusive => write!(f, "e"),
            PermissionKind::Uninit => write!(f, "u"),
        }
    }
}

impl PartialOrd for PermissionKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if *self == *other {
            return Some(Ordering::Equal);
        }
        match (self, other) {
            (PermissionKind::Shared, PermissionKind::Exclusive)
            | (PermissionKind::Uninit, PermissionKind::Exclusive) => Some(Ordering::Less),
            (PermissionKind::Exclusive, PermissionKind::Shared)
            | (PermissionKind::Exclusive, PermissionKind::Uninit) => Some(Ordering::Greater),
            (PermissionKind::Shared, PermissionKind::Uninit)
            | (PermissionKind::Uninit, PermissionKind::Shared) => None,
            _ => unreachable!(),
        }
    }
}

impl PermissionKind {
    pub fn is_shared(self) -> bool {
        self == PermissionKind::Shared
    }
    pub fn is_exclusive(self) -> bool {
        self == PermissionKind::Exclusive
    }
    pub fn is_uninit(self) -> bool {
        self == PermissionKind::Uninit
    }
    pub fn minimum(self, other: Self) -> Option<Self> {
        match self.partial_cmp(&other)? {
            Ordering::Greater => Some(other),
            _ => Some(self),
        }
    }
}
