// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::hash_map::Entry;

use prusti_rustc_interface::dataflow::JoinSemiLattice;

use crate::{
    free_pcs::{
        CapabilityKind, CapabilityLocal, CapabilityProjections, CapabilitySummary, Fpcs, RepackOp,
    },
    utils::{PlaceOrdering, PlaceRepacker},
};

use super::cg::Cg;

impl JoinSemiLattice for Cg<'_, '_> {
    fn join(&mut self, other: &Self) -> bool {
        if self.done == 2 {
            return false;
        }
        self.done += 1;
        let mut changed = self.live.union(&other.live);
        for (idx, data) in other.regions.borrows.iter() {
            match self.regions.borrows.entry(*idx) {
                Entry::Occupied(mut o) => {
                    let (a, b) = o.get_mut();
                    for r in &data.0 {
                        if !a.contains(r) {
                            changed = true;
                            a.push(*r);
                        }
                    }
                    for r in &data.1 {
                        if !b.contains(r) {
                            changed = true;
                            b.push(*r);
                        }
                    }
                }
                Entry::Vacant(v) => {
                    changed = true;
                    v.insert(data.clone());
                }
            }
        }
        for s in &other.regions.subset {
            if !self.regions.subset.contains(s) {
                changed = true;
                self.regions.subset.push(*s);
            }
        }
        if self.regions.graph != other.regions.graph {
            changed = true;
            self.regions.graph = other.regions.graph.clone();
        }
        changed
    }
}
