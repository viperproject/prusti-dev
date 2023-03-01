// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cmp::Ordering;

use derive_more::{Deref, DerefMut};

use prusti_rustc_interface::{
    data_structures::fx::FxHashMap,
    index::vec::IndexVec,
    middle::mir::{Local, Place},
};

use crate::PlaceRepacker;

pub type FreeStateUpdate<'tcx> = LocalsState<LocalUpdate<'tcx>>;
#[derive(Clone, Debug, PartialEq, Eq, Deref, DerefMut, Default)]
pub struct LocalUpdate<'tcx>((Option<PermissionLocal<'tcx>>, Option<PermissionLocal<'tcx>>));

impl<'tcx> LocalUpdate<'tcx> {
    pub(crate) fn requires_unalloc(&mut self) {
        Self::unalloc(&mut self.0 .0);
    }
    pub(crate) fn ensures_unalloc(&mut self) {
        Self::unalloc(&mut self.0 .1);
    }
    fn unalloc(local: &mut Option<PermissionLocal<'tcx>>) {
        if let Some(pre) = local {
            assert_eq!(*pre, PermissionLocal::Unallocated);
        } else {
            *local = Some(PermissionLocal::Unallocated);
        }
    }
    pub(crate) fn requires_alloc(&mut self, place: Place<'tcx>, perm: PermissionKind) {
        Self::alloc(&mut self.0 .0, place, perm);
    }
    pub(crate) fn ensures_alloc(&mut self, place: Place<'tcx>, perm: PermissionKind) {
        Self::alloc(&mut self.0 .1, place, perm);
    }
    fn alloc(local: &mut Option<PermissionLocal<'tcx>>, place: Place<'tcx>, perm: PermissionKind) {
        if let Some(pre) = local {
            let old = pre.get_allocated_mut().insert(place, perm);
            assert!(old.is_none());
        } else {
            *local = Some(PermissionLocal::Allocated(
                PermissionProjections::new_update(place, perm),
            ));
        }
    }
    pub(crate) fn get_pre(&self) -> &Option<PermissionLocal<'tcx>> {
        &self.0 .0
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
    pub(crate) fn consistency_check(&self) {
        for p in self.iter() {
            p.consistency_check();
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
        for (local, LocalUpdate((pre, post))) in self.0.clone().into_iter_enumerated() {
            if cfg!(debug_assertions) {
                if let Some(pre) = pre {
                    match (&state[local], pre) {
                        (PermissionLocal::Unallocated, PermissionLocal::Unallocated) => {}
                        (PermissionLocal::Allocated(local_state), PermissionLocal::Allocated(pre)) => {
                            for (place, required_perm) in pre.iter() {
                                let perm = local_state.get(place).unwrap();
                                let is_read = required_perm.is_shared() && perm.is_exclusive();
                                assert!(perm == required_perm || is_read, "Req\n{self:#?}\n, have\n{state:#?}\n{place:#?}\n{perm:#?}\n{required_perm:#?}\n");
                            }
                        }
                        _ => unreachable!(),
                    }
                }
            }
            if let Some(post) = post {
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

#[derive(Clone, Debug, PartialEq, Eq)]
/// The permissions of a local
pub enum PermissionLocal<'tcx> {
    Unallocated,
    Allocated(PermissionProjections<'tcx>),
}

impl<'tcx> PermissionLocal<'tcx> {
    pub fn get_allocated_mut(&mut self) -> &mut PermissionProjections<'tcx> {
        match self {
            PermissionLocal::Allocated(places) => places,
            _ => panic!(),
        }
    }

    fn consistency_check(&self) {
        match self {
            PermissionLocal::Unallocated => {}
            PermissionLocal::Allocated(places) => {
                places.consistency_check();
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Deref, DerefMut)]
/// The permissions for all the projections of a place
// We only need the projection part of the place
pub struct PermissionProjections<'tcx>(FxHashMap<Place<'tcx>, PermissionKind>);

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
    pub fn find_all_related(
        &self,
        place: Place<'tcx>,
    ) -> impl Iterator<Item = (Ordering, Place<'tcx>, PermissionKind)> + '_ {
        self.iter().filter_map(move |(other, perm)| {
            PlaceRepacker::partial_cmp(*other, place).map(|ord| (ord, *other, *perm))
        })
    }
    pub(crate) fn unpack(
        &mut self,
        to: Place<'tcx>,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<Place<'tcx>> {
        // Inefficient to do the work here when not needed
        debug_assert!(!self.contains_key(&to));
        let (ord, other, perm) = {
            let mut related = self.find_all_related(to);
            let r = related.next().unwrap();
            debug_assert!(
                related.next().is_none(),
                "{:?} ({to:?})",
                self.find_all_related(to).collect::<Vec<_>>()
            );
            r
        };
        assert!(ord == Ordering::Less);
        let (expanded, others) = rp.expand(other, to);
        self.remove(&other);
        self.extend(others.into_iter().map(|p| (p, perm)));
        self.insert(to, perm);
        expanded
    }
    pub(crate) fn pack(
        &mut self,
        to: Place<'tcx>,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<Place<'tcx>> {
        // Inefficient to do the work here when not needed
        debug_assert!(!self.contains_key(&to));
        let related: Vec<_> = self.find_all_related(to).collect();
        debug_assert!(related.len() > 0);
        debug_assert!(related.iter().all(|(ord, _, _)| *ord == Ordering::Greater));
        debug_assert!(related.iter().all(|(_, _, perm)| *perm == related[0].2));
        let mut related_set = related.iter().map(|(_, p, _)| *p).collect();
        let collapsed = rp.collapse(to, &mut related_set);
        assert!(related_set.is_empty());
        for (_, p, _) in &related {
            self.remove(p);
        }
        self.insert(to, related[0].2);
        collapsed
    }

    pub(crate) fn join(&self, other: &mut Self, rp: PlaceRepacker<'_, 'tcx>) {
        for (place, kind) in &**self {
            let mut place = *place;
            let mut expand: Vec<_>;
            while {
                expand = other
                    .iter()
                    .filter_map(|(&p, &k)| {
                        PlaceRepacker::expandable_no_enum(place, p).map(|o| (o, p, k))
                    })
                    .collect();
                expand.is_empty()
            } {
                place = rp.pop_till_enum(place);
            }
            debug_assert!(expand.iter().all(|o| o.0 == expand[0].0));
            for (_, other_place, perm) in &expand {
                let cmp = kind.partial_cmp(&perm).unwrap();
                if cmp.is_lt() {
                    other.insert(*other_place, *kind);
                }
            }
            match expand[0].0 {
                // Current place has already been expanded in `other`
                Ok(Ordering::Less) => (),
                Ok(Ordering::Equal) => assert_eq!(expand.len(), 1),
                Ok(Ordering::Greater) => {
                    assert_eq!(expand.len(), 1);
                    // Do expand
                    // TODO: remove duplicate code with above
                    let to_expand = expand[0].1;
                    let (_, others) = rp.expand(to_expand, place);
                    let perm = other.remove(&to_expand).unwrap();
                    other.extend(others.into_iter().map(|p| (p, perm)));
                    other.insert(place, perm);
                }
                Err(Ordering::Less) => {
                    // Do collapse
                    // TODO: remove duplicate code with above
                    for (_, p, _) in &expand {
                        other.remove(p);
                    }
                    other.insert(place, *kind);
                }
                Err(Ordering::Equal) => unreachable!(),
                // Current place has already been collapsed in `other`
                Err(Ordering::Greater) => (),
            }
        }
    }

    fn consistency_check(&self) {
        let keys = self.keys().copied().collect::<Vec<_>>();
        for (i, p1) in keys.iter().enumerate() {
            for p2 in keys[i + 1..].iter() {
                assert!(
                    PlaceRepacker::partial_cmp(*p1, *p2).is_none(),
                    "{p1:?} {p2:?}",
                );
            }
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PermissionKind {
    Shared,
    Exclusive,
    Uninit,
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
}
