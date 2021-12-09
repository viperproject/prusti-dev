// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::mir_utils::DisplayPlaceRef;
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir;
use serde::{ser::SerializeMap, Serialize, Serializer};

#[derive(Clone, Default, Eq, PartialEq)]
pub struct DefinitelyAccessibleState<'tcx> {
    /// Places that are definitely not moved-out nor blocked by a *mutable* reference.
    pub(super) definitely_accessible: FxHashSet<mir::PlaceRef<'tcx>>,
    /// Places that are definitely not moved-out nor blocked by a *mutable or shared* reference.
    /// This should always be a subset of `definitely_accessible`.
    pub(super) definitely_owned: FxHashSet<mir::PlaceRef<'tcx>>,
}

impl<'tcx> Serialize for DefinitelyAccessibleState<'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut seq = serializer.serialize_map(Some(2))?;
        let mut definitely_accessible_set: Vec<_> = self.definitely_accessible.iter().collect();
        definitely_accessible_set.sort();
        let mut definitely_accessible_strings = vec![];
        for &place in definitely_accessible_set {
            definitely_accessible_strings.push(format!("{}", DisplayPlaceRef(place)));
        }
        seq.serialize_entry("accessible", &definitely_accessible_strings)?;
        let mut definitely_owned_set: Vec<_> = self.definitely_owned.iter().collect();
        definitely_owned_set.sort();
        let mut definitely_owned_strings = vec![];
        for &place in definitely_owned_set {
            definitely_owned_strings.push(format!("{}", DisplayPlaceRef(place)));
        }
        seq.serialize_entry("owned", &definitely_owned_strings)?;
        seq.end()
    }
}
