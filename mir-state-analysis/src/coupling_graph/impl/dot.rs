// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::borrow::Cow;

use prusti_rustc_interface::{
    borrowck::consumers::BorrowIndex,
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::fmt::DebugWithContext,
    index::{bit_set::BitSet, IndexVec},
    middle::{
        mir::{BorrowKind, ConstraintCategory, Local, BasicBlock},
        ty::{RegionVid, TyKind},
    },
};

use crate::coupling_graph::outlives_info::edge::{EdgeInfo, Edge as CgEdge};

use super::{triple::Cg};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edge<'tcx> {
    pub from: RegionVid,
    pub to: RegionVid,
    pub reasons: FxHashSet<Vec<CgEdge<'tcx>>>,
}

impl<'tcx> Edge<'tcx> {
    pub(crate) fn new(from: RegionVid, to: RegionVid, reasons: FxHashSet<Vec<CgEdge<'tcx>>>) -> Self {
        Self { from, to, reasons }
    }
}

impl<'a, 'tcx> Cg<'a, 'tcx> {
    fn get_id(&self) -> String {
        if self.location.block == BasicBlock::MAX {
            "start".to_string()
        } else {
            let pre = if self.is_pre { "_pre" } else { "" };
            format!("{:?}{pre}", self.location).replace('[', "_").replace(']', "")
        }
    }
}
impl<'a, 'tcx> Cg<'a, 'tcx> {
    fn non_empty_edges(
        &self,
        sub: RegionVid,
        start: RegionVid,
        mut reasons: FxHashSet<Vec<CgEdge<'tcx>>>,
        visited: &mut FxHashSet<RegionVid>,
    ) -> Vec<Edge<'tcx>> {
        let mut edges = Vec::new();
        if !visited.insert(sub) {
            return edges;
        }
        let sub_info = self.cgx.region_info.map.get(sub);
        if (self.dot_node_filter)(sub_info) {
            // Remove empty reasons
            // reasons.retain(|reason| reason.iter().any(|r| r.creation.is_some()) || reason.reason.is_some());
            return vec![Edge::new(start, sub, reasons)];
        }
        for (&sup, edge) in &self.graph.nodes[sub].blocks {
            let sup_info = self.cgx.region_info.map.get(sup);
            if !(self.dot_edge_filter)(sup_info, sub_info) {
                continue;
            }
            let mut reasons = reasons.clone();
            reasons.extend(edge.clone());
            edges.extend(self.non_empty_edges(sup, start, reasons, visited));
        }
        visited.remove(&sub);
        edges
    }
}

impl<'a, 'b, 'tcx> dot::Labeller<'a, RegionVid, Edge<'tcx>> for Cg<'b, 'tcx> {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new(self.get_id()).unwrap()
    }

    fn node_id(&'a self, r: &RegionVid) -> dot::Id<'a> {
        let r = format!("{r:?}").replace("'?", "N");
        let id = format!("{r}_{}", self.get_id());
        dot::Id::new(id).unwrap()
    }

    fn edge_style(&'a self, e: &Edge<'tcx>) -> dot::Style {
        let is_blocking = e.reasons.iter().any(|e| CgEdge::is_blocking(e));
        if is_blocking {
            dot::Style::Solid
        } else {
            dot::Style::Dotted
        }
    }
    fn edge_label(&'a self, e: &Edge<'tcx>) -> dot::LabelText<'a> {
        let mut label = e
            .reasons
            .iter()
            .map(|s| {
                let line = s.into_iter().map(|s| format!("{s}, ")).collect::<String>();
                format!("{}\n", &line[..line.len() - 2]) // `s.len() > 0`
            })
            .collect::<String>();
        if label.len() > 0 {
            label = label[..label.len() - 1].to_string();
        }
        dot::LabelText::LabelStr(Cow::Owned(label))
    }
    fn node_color(&'a self, r: &RegionVid) -> Option<dot::LabelText<'a>> {
        let kind = self.get_kind(*r);
        if kind.universal() {
            Some(dot::LabelText::LabelStr(Cow::Borrowed("red")))
        } else if self.graph.inactive_loans.contains(r) {
            Some(dot::LabelText::LabelStr(Cow::Borrowed("blue")))
        } else {
            None
        }
    }
    fn node_shape(&'a self, r: &RegionVid) -> Option<dot::LabelText<'a>> {
        if self.graph.static_regions.contains(&r) {
            return Some(dot::LabelText::LabelStr(Cow::Borrowed("house")));
        }
        // For regions created by `... = &'r ...`, find the kind of borrow.
        self.cgx
            .region_info
            .map
            .get(*r)
            .get_borrow()
            .map(|data| match data.kind {
                BorrowKind::Shared => dot::LabelText::LabelStr(Cow::Borrowed("box")),
                BorrowKind::Shallow => dot::LabelText::LabelStr(Cow::Borrowed("triangle")),
                BorrowKind::Mut { kind } => dot::LabelText::LabelStr(Cow::Borrowed("polygon")),
            })
    }
    fn node_label(&'a self, r: &RegionVid) -> dot::LabelText<'a> {
        if *r == RegionVid::MAX {
            // return dot::LabelText::LabelStr(Cow::Owned());
            unimplemented!();
        }
        let mut label = format!("{r:?}\n{}", self.get_kind(*r).to_string(&self.cgx));
        // Not super useful: the `origin` is always NLL.
        // if let Some(region_info) = self.facts2.region_inference_context.var_infos.get(*r) {
        //     label += &format!("\n{:?}, {:?}", region_info.origin, region_info.universe);
        // }
        dot::LabelText::LabelStr(Cow::Owned(label))
    }
}

impl<'a, 'b, 'tcx> dot::GraphWalk<'a, RegionVid, Edge<'tcx>> for Cg<'b, 'tcx> {
    fn nodes(&self) -> dot::Nodes<'a, RegionVid> {
        let mut nodes: Vec<_> = self
            .graph
            .all_nodes()
            .filter(|(r, _)| (self.dot_node_filter)(self.cgx.region_info.map.get(*r)))
            .map(|(r, _)| r)
            .collect();
        // if self.static_regions.len() > 1 {
        //     nodes.push(usize::MAX);
        // }
        Cow::Owned(nodes)
    }

    fn edges(&'a self) -> dot::Edges<'a, Edge<'tcx>> {
        let mut edges = Vec::new();
        for (sub, n) in self.graph.all_nodes() {
            let sub_info = self.cgx.region_info.map.get(sub);
            if !(self.dot_node_filter)(sub_info) {
                continue;
            }
            let visited = &mut FxHashSet::from_iter([sub]);
            for (&sup, edge) in &n.blocks {
                let sup_info = self.cgx.region_info.map.get(sup);
                if !(self.dot_edge_filter)(sup_info, sub_info) {
                    continue;
                }
                edges.extend(self.non_empty_edges(sup, sub, edge.clone(), visited));
            }
        }
        Cow::Owned(edges)
    }

    fn source(&self, e: &Edge<'tcx>) -> RegionVid {
        e.from
    }

    fn target(&self, e: &Edge<'tcx>) -> RegionVid {
        e.to
    }
}
