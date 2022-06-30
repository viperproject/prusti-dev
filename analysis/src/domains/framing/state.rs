// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    domains::DefinitelyAccessibleState,
    mir_utils::{is_prefix, Place},
};
use prusti_rustc_interface::data_structures::fx::FxHashSet;
use serde::{ser::SerializeMap, Serialize, Serializer};
use std::fmt;

#[derive(Clone, Default, Eq, PartialEq)]
pub struct FramingState<'tcx> {
    /// Places of `definitely_accessible` that can be framed across the *next* statement.
    pub(super) framed_accessible: FxHashSet<Place<'tcx>>,
    /// Places of `definitely_owned` that can be framed across the *next* statement.
    pub(super) framed_owned: FxHashSet<Place<'tcx>>,
}

impl<'tcx> FramingState<'tcx> {
    pub fn get_framed_accessible(&self) -> &FxHashSet<Place<'tcx>> {
        &self.framed_accessible
    }

    pub fn get_framed_owned(&self) -> &FxHashSet<Place<'tcx>> {
        &self.framed_owned
    }

    pub fn check_invariant(
        &self,
        accessibility: &DefinitelyAccessibleState<'tcx>,
        location: impl fmt::Debug,
    ) {
        for &owned_place in self.framed_owned.iter() {
            debug_assert!(
                self.framed_accessible
                    .iter()
                    .any(|&place| place == owned_place || is_prefix(owned_place, place)),
                "In the state before {:?} the framed place {:?} is owned but not accessible",
                location,
                owned_place
            );
        }
        for &owned_place in self.framed_accessible.iter() {
            debug_assert!(
                accessibility.get_definitely_accessible()
                    .iter()
                    .any(|&place| place == owned_place || is_prefix(owned_place, place)),
                "In the state before {:?} the place {:?} is not accessible, but it is framed as accessible",
                location,
                owned_place
            );
        }
        for &owned_place in self.framed_owned.iter() {
            debug_assert!(
                accessibility
                    .get_definitely_owned()
                    .iter()
                    .any(|&place| place == owned_place || is_prefix(owned_place, place)),
                "In the state before {:?} the place {:?} is not owned, but it is framed as owned",
                location,
                owned_place
            );
        }
    }
}

impl<'tcx> Serialize for FramingState<'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut seq = serializer.serialize_map(Some(2))?;
        let mut definitely_accessible_set: Vec<_> = self.framed_accessible.iter().collect();
        definitely_accessible_set.sort();
        let mut definitely_accessible_strings = vec![];
        for &place in definitely_accessible_set {
            definitely_accessible_strings.push(format!("{:?}", place));
        }
        seq.serialize_entry("frame_accessible", &definitely_accessible_strings)?;
        let mut definitely_owned_set: Vec<_> = self.framed_owned.iter().collect();
        definitely_owned_set.sort();
        let mut definitely_owned_strings = vec![];
        for &place in definitely_owned_set {
            definitely_owned_strings.push(format!("{:?}", place));
        }
        seq.serialize_entry("frame_owned", &definitely_owned_strings)?;
        seq.end()
    }
}

impl fmt::Debug for FramingState<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", serde_json::to_string_pretty(&self).unwrap())
    }
}
