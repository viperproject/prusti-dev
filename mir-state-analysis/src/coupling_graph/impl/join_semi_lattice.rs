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

use super::{triple::Cg, graph::Graph};

impl JoinSemiLattice for Cg<'_, '_> {
    #[tracing::instrument(name = "Cg::join", level = "debug", ret)]
    fn join(&mut self, other: &Self) -> bool {
        self.graph.join(&other.graph)
    }
}

impl JoinSemiLattice for Graph<'_> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (from, node) in other.all_nodes() {
            for (&to, reasons) in node.blocks.iter() {
                for &reason in reasons {
                    let was_new = self.outlives_inner(to, from, reason);
                    changed = changed || was_new;
                }
            }
        }
        changed
    }
}
