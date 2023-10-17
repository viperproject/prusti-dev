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
    utils::{PlaceOrdering, PlaceRepacker}, coupling_graph::{coupling::{CouplingOp, Block}, consistency::CouplingConsistency},
};

use super::{graph::Graph, triple::Cg};

impl JoinSemiLattice for Cg<'_, '_> {
    #[tracing::instrument(name = "Cg::join", level = "debug", ret)]
    fn join(&mut self, other: &Self) -> bool {
        let version = self.version.entry(other.id.unwrap().block).or_default();
        *version += 1;
        assert!(*version < 10);
        self.graph.join(&other.graph)
    }
}

impl JoinSemiLattice for Graph<'_> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (_, node) in other.all_nodes() {
            for (_, reasons) in node.blocks.iter() {
                for reason in reasons.clone() {
                    let was_new = self.outlives_inner(reason);
                    changed = changed || was_new.is_some();
                }
            }
        }
        changed
    }
}


impl Cg<'_, '_> {
    #[tracing::instrument(name = "Cg::bridge", level = "debug", ret)]
    pub fn bridge(&self, other: &Self) -> Vec<CouplingOp> {
        other.graph.all_nodes().flat_map(|(sub, node)|
            node.blocks
                .keys()
                .filter(move |sup| !self.graph.nodes[sub].blocks.contains_key(*sup))
                .copied()
                .flat_map(move |sup| self.outlives_to_block((sup, sub)))
                .map(|block| CouplingOp::Add(block))
        ).collect()
    }
}
