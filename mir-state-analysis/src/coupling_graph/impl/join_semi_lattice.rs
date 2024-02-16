// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::hash_map::Entry;

use prusti_rustc_interface::{dataflow::JoinSemiLattice, middle::mir::Location};

use crate::{
    coupling_graph::{
        consistency::CouplingConsistency,
        coupling::{Block, CouplingOp},
        outlives_info::edge::{Edge, EdgeInfo, EdgeOrigin},
    },
    free_pcs::{
        CapabilityKind, CapabilityLocal, CapabilityProjections, CapabilitySummary, RepackOp,
    },
    utils::{PlaceOrdering, PlaceRepacker},
};

use super::{graph::Graph, triple::CouplingGraph};

impl JoinSemiLattice for CouplingGraph<'_, '_> {
    #[tracing::instrument(name = "CouplingGraph::join", level = "debug", ret)]
    fn join(&mut self, other: &Self) -> bool {
        let version = self.version.entry(other.location.block).or_default();
        *version += 1;
        assert!(*version < 20, "{:?} -> {:?}", other.location, self.location);

        let loop_head = self.cgx.loops.loop_head_of(self.location.block);
        let top = |sup, sub| {
            EdgeInfo::no_reason(sup, sub, Some(self.location), EdgeOrigin::Opaque).to_edge(&self.cgx)
        };
        let needs_widening = |loc: Location| {
            loop_head
                .map(|l| self.cgx.loops.in_loop(loc.block, l))
                .unwrap_or_default()
        };
        // Are we looping back into the loop head from within the loop?
        let loop_into = loop_head.map(|l| self.cgx.loops.in_loop(other.location.block, l));
        let mut changed = false;
        for (_, node) in other.after.all_nodes() {
            for (_, edges) in node.blocks.iter() {
                for edge in edges {
                    let edge = Edge::widen(edge, top, needs_widening);
                    let was_new = self.after.outlives_join(edge);
                    changed = changed || was_new.is_some();
                }
            }
        }
        let old_len = self.after.inactive_loans.len();
        self.after
            .inactive_loans
            .extend(other.after.inactive_loans.iter().copied());
        changed = changed || old_len != self.after.inactive_loans.len();
        changed
    }
}

impl CouplingGraph<'_, '_> {
    #[tracing::instrument(name = "CouplingGraph::bridge", level = "debug", fields(self.after = ?self.after, other.after = ?self.after), ret)]
    pub fn bridge(&self, other: &Self) -> Vec<CouplingOp> {
        other
            .after
            .all_nodes()
            .flat_map(|(sub, node)| {
                node.true_edges()
                    .into_iter()
                    .filter(move |sup| !self.after.nodes[sub].blocks.contains_key(sup))
                    .map(move |sup| self.outlives_to_block((sup, sub, true)).unwrap())
                    .map(|block| CouplingOp::Add(block))
            })
            .collect()
    }
}
