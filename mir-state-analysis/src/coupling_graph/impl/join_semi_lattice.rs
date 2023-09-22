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

use super::cg::{Cg, Graph};

impl JoinSemiLattice for Cg<'_, '_> {
    fn join(&mut self, other: &Self) -> bool {
        // if self.done == 20 {
        //     panic!();
        //     // return false;
        // }
        // self.done += 1;
        let actually_changed = self.regions.graph.join(&other.regions.graph);
        return actually_changed;
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
        // if self.regions.graph != other.regions.graph {
        //     changed = true;
        //     self.regions.graph = other.regions.graph.clone();
        // }
        actually_changed
    }
}

impl JoinSemiLattice for Graph<'_, '_> {
    fn join(&mut self, other: &Self) -> bool {
        // println!("Joining graphs:\n{:?}: {:?}\n{:?}: {:?}", self.id, self.nodes, other.id, other.nodes);
        let mut changed = false;
        for node in other.nodes.iter().flat_map(|n| n) {
            let rep = node.regions.iter().next().unwrap();
            for r in node.regions.iter().skip(1) {
                changed = changed || self.equate_regions(*rep, *r);
            }
            for (to, reasons) in node.blocks.iter() {
                let (from, to) = other.edge_to_regions(node.id, *to);
                let was_new = self.outlives_many(to, from, reasons);
                changed = changed || was_new;
                // if was_new {
                //     println!("New edge: {:?} -> {:?} ({:?})", from, to, reasons);
                // }
            }
        }
        if changed {
            self.version += 1;
            assert!(self.version < 1000);
        }
        changed
    }
}
