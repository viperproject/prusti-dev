// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::coupling_graph::{graph::Graph, triple::CouplingGraph, CgContext};

pub trait CouplingConsistency<'tcx> {
    fn consistency_check(&self, cgx: &CgContext<'_, 'tcx>) -> Option<String>;
}

impl<'tcx> CouplingConsistency<'tcx> for CouplingGraph<'_, 'tcx> {
    #[tracing::instrument(name = "Graph::consistency_check", level = "trace", skip(self, cgx))]
    fn consistency_check(&self, cgx: &CgContext<'_, 'tcx>) -> Option<String> {
        for (sub, node) in self.after.all_nodes() {
            for (sup, edge) in node.blocks.iter() {
                let sup_info = cgx.region_info.map.get(*sup);
                let sub_info = cgx.region_info.map.get(sub);

                if sup_info.is_borrow() && self.after.static_regions.contains(&sup) {
                    return Some(format!("Borrow is static: {sup:?}"));
                }
            }
        }
        None
    }
}
