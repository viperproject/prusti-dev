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
pub struct MaybeBorrowedState<'tcx> {
    pub(super) maybe_shared_borrowed: FxHashSet<mir::PlaceRef<'tcx>>,
    pub(super) maybe_mut_borrowed: FxHashSet<mir::PlaceRef<'tcx>>,
}

impl<'tcx> Serialize for MaybeBorrowedState<'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut seq = serializer.serialize_map(Some(2))?;
        let mut maybe_shared_borrowed_set: Vec<_> = self.maybe_shared_borrowed.iter().collect();
        maybe_shared_borrowed_set.sort();
        let mut maybe_shared_borrowed_strings = vec![];
        for &place in maybe_shared_borrowed_set {
            maybe_shared_borrowed_strings.push(format!("{}", DisplayPlaceRef(place)));
        }
        seq.serialize_entry("frozen", &maybe_shared_borrowed_strings)?;
        let mut maybe_mut_borrowed_set: Vec<_> = self.maybe_mut_borrowed.iter().collect();
        maybe_mut_borrowed_set.sort();
        let mut maybe_mut_borrowed_strings = vec![];
        for &place in maybe_mut_borrowed_set {
            maybe_mut_borrowed_strings.push(format!("{}", DisplayPlaceRef(place)));
        }
        seq.serialize_entry("blocked", &maybe_mut_borrowed_strings)?;
        seq.end()
    }
}
