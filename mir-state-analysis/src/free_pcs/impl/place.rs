// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    cmp::Ordering,
    fmt::{Debug, Formatter, Result},
    ops::Sub,
};

use prusti_rustc_interface::data_structures::fx::FxHashSet;

use crate::{Place, PlaceOrdering};

#[derive(Debug)]
pub(crate) struct RelatedSet<'tcx> {
    pub(crate) from: Vec<(Place<'tcx>, CapabilityKind)>,
    pub(crate) to: Place<'tcx>,
    pub(crate) minimum: CapabilityKind,
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

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum CapabilityKind {
    Read,
    Write,
    Exclusive,
}
impl Debug for CapabilityKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            CapabilityKind::Read => write!(f, "R"),
            CapabilityKind::Write => write!(f, "W"),
            CapabilityKind::Exclusive => write!(f, "E"),
        }
    }
}

impl PartialOrd for CapabilityKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if *self == *other {
            return Some(Ordering::Equal);
        }
        match (self, other) {
            (CapabilityKind::Read, CapabilityKind::Exclusive)
            | (CapabilityKind::Write, CapabilityKind::Exclusive) => Some(Ordering::Less),
            (CapabilityKind::Exclusive, CapabilityKind::Read)
            | (CapabilityKind::Exclusive, CapabilityKind::Write) => Some(Ordering::Greater),
            _ => None,
        }
    }
}

impl Sub for CapabilityKind {
    type Output = Option<Self>;
    fn sub(self, other: Self) -> Self::Output {
        match (self, other) {
            (CapabilityKind::Exclusive, CapabilityKind::Read) => Some(CapabilityKind::Write),
            (CapabilityKind::Exclusive, CapabilityKind::Write) => Some(CapabilityKind::Read),
            _ => None,
        }
    }
}

impl CapabilityKind {
    pub fn is_read(self) -> bool {
        matches!(self, CapabilityKind::Read)
    }
    pub fn is_exclusive(self) -> bool {
        matches!(self, CapabilityKind::Exclusive)
    }
    pub fn is_write(self) -> bool {
        matches!(self, CapabilityKind::Write)
    }
    pub fn minimum(self, other: Self) -> Option<Self> {
        match self.partial_cmp(&other)? {
            Ordering::Greater => Some(other),
            _ => Some(self),
        }
    }
}
