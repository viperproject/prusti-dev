// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    cmp::Ordering,
    fmt::{Debug, Formatter, Result},
};

use prusti_rustc_interface::data_structures::fx::FxHashSet;

use crate::utils::{Place, PlaceOrdering};

#[derive(Debug)]
pub(crate) struct RelatedSet<'tcx> {
    pub(crate) from: Vec<(Place<'tcx>, CapabilityKind)>,
    pub(crate) to: Place<'tcx>,
    // pub(crate) minimum: CapabilityKind,
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
    pub fn get_only_from(&self) -> Place<'tcx> {
        assert_eq!(self.from.len(), 1);
        self.from[0].0
    }
    pub fn common_prefix(&self, to: Place<'tcx>) -> Place<'tcx> {
        self.from[0].0.common_prefix(to)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum CapabilityKind {
    Write,
    Exclusive,
    /// [`CapabilityKind::Exclusive`] for everything not through a dereference,
    /// [`CapabilityKind::Write`] for everything through a dereference.
    ShallowExclusive,
}
impl Debug for CapabilityKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            CapabilityKind::Write => write!(f, "W"),
            CapabilityKind::Exclusive => write!(f, "E"),
            CapabilityKind::ShallowExclusive => write!(f, "e"),
        }
    }
}

impl PartialOrd for CapabilityKind {
    #[tracing::instrument(name = "CapabilityKind::partial_cmp", level = "trace", ret)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if *self == *other {
            return Some(Ordering::Equal);
        }
        match (self, other) {
            // W < E, W < e
            (CapabilityKind::Write, CapabilityKind::Exclusive)
            | (CapabilityKind::ShallowExclusive, CapabilityKind::Exclusive)
            | (CapabilityKind::Write, CapabilityKind::ShallowExclusive) => Some(Ordering::Less),
            // E > W, e > W
            (CapabilityKind::Exclusive, CapabilityKind::Write)
            | (CapabilityKind::Exclusive, CapabilityKind::ShallowExclusive)
            | (CapabilityKind::ShallowExclusive, CapabilityKind::Write) => Some(Ordering::Greater),
            _ => None,
        }
    }
}

impl CapabilityKind {
    pub fn is_exclusive(self) -> bool {
        matches!(self, CapabilityKind::Exclusive)
    }
    pub fn is_write(self) -> bool {
        matches!(self, CapabilityKind::Write)
    }
    pub fn is_shallow_exclusive(self) -> bool {
        matches!(self, CapabilityKind::ShallowExclusive)
    }
    pub fn minimum(self, other: Self) -> Option<Self> {
        match self.partial_cmp(&other)? {
            Ordering::Greater => Some(other),
            _ => Some(self),
        }
    }
}
