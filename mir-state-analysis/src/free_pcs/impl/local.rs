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

use crate::{
    free_pcs::{CapabilityKind, RelatedSet, RepackOp},
    utils::{Place, PlaceOrdering, PlaceRepacker},
};

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

impl Default for CapabilityLocal<'_> {
    fn default() -> Self {
        Self::Unallocated
    }
}

impl<'tcx> CapabilityLocal<'tcx> {
    pub fn get_allocated_mut(&mut self) -> &mut CapabilityProjections<'tcx> {
        let Self::Allocated(cps) = self else {
            panic!("Expected allocated local")
        };
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

    pub(crate) fn update_cap(&mut self, place: Place<'tcx>, cap: CapabilityKind) {
        let old = self.insert(place, cap);
        assert!(old.is_some());
    }

    /// Returns all related projections of the given place that are contained in this map.
    /// A `Ordering::Less` means that the given `place` is a prefix of the iterator place.
    /// For example: find_all_related(x.f.g) = [(Less, x.f.g.h), (Greater, x.f)]
    /// It also checks that the ordering conforms to the expected ordering (the above would
    /// fail in any situation since all orderings need to be the same)
    #[tracing::instrument(level = "debug", ret)]
    pub(crate) fn find_all_related(
        &self,
        to: Place<'tcx>,
        mut expected: Option<PlaceOrdering>,
    ) -> RelatedSet<'tcx> {
        // let mut minimum = None::<CapabilityKind>;
        let mut related = Vec::new();
        for (&from, &cap) in &**self {
            if let Some(ord) = from.partial_cmp(to) {
                // let cap_no_read = cap.read_as_exclusive();
                // minimum = if let Some(min) = minimum {
                //     Some(min.minimum(cap_no_read).unwrap())
                // } else {
                //     Some(cap_no_read)
                // };
                if let Some(expected) = expected {
                    assert_eq!(ord, expected, "({self:?}) {from:?} {to:?}");
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
            // minimum: minimum.unwrap(),
            relation,
        }
    }

    #[tracing::instrument(
        name = "CapabilityProjections::unpack",
        level = "trace",
        skip(repacker),
        ret
    )]
    pub(crate) fn expand(
        &mut self,
        from: Place<'tcx>,
        to: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<RepackOp<'tcx>> {
        debug_assert!(!self.contains_key(&to));
        let (expanded, mut others) = from.expand(to, repacker);
        let mut perm = self.remove(&from).unwrap();
        others.push(to);
        let mut ops = Vec::new();
        for (from, to, kind) in expanded {
            let others = others.extract_if(|other| !to.is_prefix(*other));
            self.extend(others.map(|p| (p, perm)));
            if kind.is_box() && perm.is_shallow_exclusive() {
                ops.push(RepackOp::DerefShallowInit(from, to));
                perm = CapabilityKind::Write;
            } else {
                ops.push(RepackOp::Expand(from, to, perm));
            }
        }
        self.extend(others.into_iter().map(|p| (p, perm)));
        // assert!(self.contains_key(&to), "{self:?}\n{to:?}");
        ops
    }

    // TODO: this could be implemented more efficiently, by assuming that a valid
    // state can always be packed up to the root
    #[tracing::instrument(
        name = "CapabilityProjections::pack",
        level = "trace",
        skip(repacker),
        ret
    )]
    pub(crate) fn collapse(
        &mut self,
        mut from: FxHashSet<Place<'tcx>>,
        to: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<RepackOp<'tcx>> {
        debug_assert!(!self.contains_key(&to), "{to:?} already exists in {self:?}");
        let mut old_caps: FxHashMap<_, _> = from
            .iter()
            .map(|&p| (p, self.remove(&p).unwrap()))
            .collect();
        let collapsed = to.collapse(&mut from, repacker);
        assert!(from.is_empty(), "{from:?} ({collapsed:?}) {to:?}");
        let mut exclusive_at = Vec::new();
        if !to.projects_shared_ref(repacker) {
            for (to, _, kind) in &collapsed {
                if kind.is_shared_ref() {
                    let mut is_prefixed = false;
                    exclusive_at
                        .extract_if(|old| {
                            let cmp = to.either_prefix(*old);
                            if matches!(cmp, Some(false)) {
                                is_prefixed = true;
                            }
                            cmp.unwrap_or_default()
                        })
                        .for_each(drop);
                    if !is_prefixed {
                        exclusive_at.push(*to);
                    }
                }
            }
        }
        let mut ops = Vec::new();
        for (to, from, _) in collapsed {
            let removed_perms: Vec<_> = old_caps.extract_if(|old, _| to.is_prefix(*old)).collect();
            let perm = removed_perms
                .iter()
                .fold(CapabilityKind::Exclusive, |acc, (_, p)| {
                    acc.minimum(*p).unwrap()
                });
            for (from, from_perm) in removed_perms {
                if perm != from_perm {
                    assert!(from_perm > perm);
                    ops.push(RepackOp::Weaken(from, from_perm, perm));
                }
            }
            old_caps.insert(to, perm);
            ops.push(RepackOp::Collapse(to, from, perm));
        }
        self.insert(to, old_caps[&to]);
        ops
    }
}
