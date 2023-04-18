// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use derive_more::{Deref, DerefMut};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::mir::Local,
};

use crate::{utils::PlaceRepacker, CapabilityKind, Place, PlaceOrdering, RelatedSet};

#[derive(Clone, PartialEq, Eq)]
/// The permissions of a local, each key in the hashmap is a "root" projection of the local
/// Examples of root projections are: `_1`, `*_1.f`, `*(*_.f).g` (i.e. either a local or a deref)
pub enum CapabilityLocal<'tcx> {
    Unallocated,
    Allocated(CapabilityProjections<'tcx>),
}

impl Debug for CapabilityLocal<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Unallocated => write!(f, "U"),
            Self::Allocated(cps) => write!(f, "{cps:?}"),
        }
    }
}

impl<'tcx> CapabilityLocal<'tcx> {
    pub fn get_allocated_mut(&mut self) -> &mut CapabilityProjections<'tcx> {
        let Self::Allocated(cps) = self else { panic!("Expected allocated local") };
        cps
    }
    pub fn new(local: Local, perm: CapabilityKind) -> Self {
        Self::Allocated(CapabilityProjections::new(local, perm))
    }
    pub fn is_unallocated(&self) -> bool {
        matches!(self, Self::Unallocated)
    }
}

#[derive(Clone, PartialEq, Eq, Deref, DerefMut)]
/// The permissions for all the projections of a place
// We only need the projection part of the place
pub struct CapabilityProjections<'tcx>(FxHashMap<Place<'tcx>, CapabilityKind>);

impl<'tcx> Debug for CapabilityProjections<'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.0.fmt(f)
    }
}

impl<'tcx> CapabilityProjections<'tcx> {
    pub fn new(local: Local, perm: CapabilityKind) -> Self {
        Self([(local.into(), perm)].into_iter().collect())
    }
    pub fn new_uninit(local: Local) -> Self {
        Self::new(local, CapabilityKind::Write)
    }
    /// Should only be called when creating an update within `ModifiesFreeState`
    pub(crate) fn empty() -> Self {
        Self(FxHashMap::default())
    }

    pub(crate) fn get_local(&self) -> Local {
        self.iter().next().unwrap().0.local
    }

    /// Returns all related projections of the given place that are contained in this map.
    /// A `Ordering::Less` means that the given `place` is a prefix of the iterator place.
    /// For example: find_all_related(x.f.g) = [(Less, x.f.g.h), (Greater, x.f)]
    /// It also checks that the ordering conforms to the expected ordering (the above would
    /// fail in any situation since all orderings need to be the same)
    #[tracing::instrument(level = "debug", skip(self))]
    pub(crate) fn find_all_related(
        &self,
        to: Place<'tcx>,
        mut expected: Option<PlaceOrdering>,
    ) -> RelatedSet<'tcx> {
        let mut minimum = None::<CapabilityKind>;
        let mut related = Vec::new();
        for (&from, &cap) in &**self {
            if let Some(ord) = from.partial_cmp(to) {
                minimum = if let Some(min) = minimum {
                    Some(min.minimum(cap).unwrap())
                } else {
                    Some(cap)
                };
                if let Some(expected) = expected {
                    assert_eq!(ord, expected);
                } else {
                    expected = Some(ord);
                }
                related.push((from, cap));
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

    #[tracing::instrument(
        name = "CapabilityProjections::unpack",
        level = "trace",
        skip(repacker),
        ret
    )]
    pub(crate) fn unpack(
        &mut self,
        from: Place<'tcx>,
        to: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<(Place<'tcx>, Place<'tcx>)> {
        debug_assert!(!self.contains_key(&to));
        let (expanded, others) = from.expand(to, repacker);
        let perm = self.remove(&from).unwrap();
        self.extend(others.into_iter().map(|p| (p, perm)));
        self.insert(to, perm);
        expanded
    }

    // TODO: this could be implemented more efficiently, by assuming that a valid
    // state can always be packed up to the root
    #[tracing::instrument(
        name = "CapabilityProjections::pack",
        level = "trace",
        skip(repacker),
        ret
    )]
    pub(crate) fn pack(
        &mut self,
        mut from: FxHashSet<Place<'tcx>>,
        to: Place<'tcx>,
        perm: CapabilityKind,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<(Place<'tcx>, Place<'tcx>)> {
        debug_assert!(!self.contains_key(&to), "{to:?} already exists in {self:?}");
        for place in &from {
            let p = self.remove(place).unwrap();
            assert_eq!(p, perm, "Cannot pack {place:?} with {p:?} into {to:?}");
        }
        let collapsed = to.collapse(&mut from, repacker);
        assert!(from.is_empty());
        self.insert(to, perm);
        collapsed
    }
}
