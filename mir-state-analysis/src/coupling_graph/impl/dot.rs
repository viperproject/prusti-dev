// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::borrow::Cow;

use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    index::bit_set::BitSet,
    dataflow::fmt::DebugWithContext, index::IndexVec, middle::mir::Local,
    borrowck::consumers::BorrowIndex,
    middle::{mir::{BorrowKind, ConstraintCategory}, ty::{RegionVid, TyKind}},
};

use crate::utils::Place;

use super::{cg::{Graph, EdgeInfo}, region_place::Perms};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edge<'tcx> {
    pub from: RegionVid,
    pub to: RegionVid,
    pub reasons: FxHashSet<EdgeInfo<'tcx>>,
}

impl<'tcx> Edge<'tcx> {
    pub(crate) fn new(from: RegionVid, to: RegionVid, reasons: FxHashSet<EdgeInfo<'tcx>>) -> Self {
        Self { from, to, reasons }
    }
}

impl<'a, 'tcx> Graph<'a, 'tcx> {
    fn get_id(&self) -> String {
        if let Some(id) = &self.id {
            id.replace('[', "_").replace(']', "")
        } else {
            "unnamed".to_string()
        }
    }
}
impl<'a, 'tcx> Graph<'a, 'tcx> {
    // pub(crate) fn is_empty_node(&self, n: NodeId) -> bool {
    //     self.get_corresponding_places(n).is_none()
    // }
    // fn get_corresponding_places(&self, n: NodeId) -> Option<&Perms<'tcx>> {
    //     let node = self.get_node(n);
    //     self.cgx.region_map.get(&node.region)
    // }
    /// For regions created by `... = &'r ...`, find the kind of borrow.
    pub(crate) fn borrow_kind(&self, r: RegionVid) -> Option<BorrowKind> {
        // TODO: we could put this into a `FxHashMap<RegionVid, BorrowData>` in `cgx`.
        self.facts2.borrow_set.location_map.iter()
            .chain(&self.cgx.sbs.location_map)
            .find(|(_, data)| data.region == r)
            .map(|(_, data)| data.kind)
    }
    fn non_empty_edges(&self, r: RegionVid, start: RegionVid, reasons: FxHashSet<EdgeInfo<'tcx>>, visited: &mut FxHashSet<RegionVid>) -> Vec<Edge<'tcx>> {
        let mut edges = Vec::new();
        if !visited.insert(r) {
            return edges;
        }
        if !self.skip_empty_nodes || self.has_associated_place(r) {
            return vec![Edge::new(start, r, reasons)];
        }
        for (&b, edge) in &self.nodes[r].blocks {
            let mut reasons = reasons.clone();
            reasons.extend(edge);
            edges.extend(self.non_empty_edges(b, start, reasons, visited));
        }
        visited.remove(&r);
        edges
    }
}

impl<'a, 'b, 'tcx> dot::Labeller<'a, RegionVid, Edge<'tcx>> for Graph<'b, 'tcx> {
    fn graph_id(&'a self) -> dot::Id<'a> { dot::Id::new(self.get_id()).unwrap() }

    fn node_id(&'a self, r: &RegionVid) -> dot::Id<'a> {
        let r = format!("{r:?}").replace("'?", "N");
        let id = format!("{r}_{}", self.get_id());
        dot::Id::new(id).unwrap()
    }

    // fn edge_end_arrow(&'a self, e: &Edge) -> dot::Arrow {
    //     if self.borrow_kind(e.from).is_some() {
    //         dot::Arrow::from_arrow(dot::ArrowShape::Dot(dot::Fill::Filled))
    //     } else {
    //         dot::Arrow::default()
    //     }
    // }
    fn edge_style(&'a self, e: &Edge<'tcx>) -> dot::Style {
        if self.borrow_kind(e.from).is_some() {
            dot::Style::Dotted
        } else {
            dot::Style::Solid
        }
    }
    fn edge_label(&'a self, e: &Edge<'tcx>) -> dot::LabelText<'a> {
        let mut label = e.reasons.iter().map(|s| format!("{s}\n")).collect::<String>();
        label = label[..label.len() - 1].to_string();
        dot::LabelText::LabelStr(Cow::Owned(label))
    }
    fn node_shape(&'a self, r: &RegionVid) -> Option<dot::LabelText<'a>> {
        if self.static_regions.contains(&r) {
            return Some(dot::LabelText::LabelStr(Cow::Borrowed("house")));
        }
        self.borrow_kind(*r).map(|kind| match kind {
            BorrowKind::Shared =>
                dot::LabelText::LabelStr(Cow::Borrowed("box")),
            BorrowKind::Shallow =>
                dot::LabelText::LabelStr(Cow::Borrowed("triangle")),
            BorrowKind::Mut { kind } =>
                dot::LabelText::LabelStr(Cow::Borrowed("ellipse")),
        })
    }
    fn node_label(&'a self, r: &RegionVid) -> dot::LabelText<'a> {
        if *r == RegionVid::MAX {
            // return dot::LabelText::LabelStr(Cow::Owned());
            unimplemented!();
        }
        let mut label = format!("{r:?}");
        if let Some(place) = self.get_associated_place(*r) {
            label += &format!("\n{place:?}");
        } else {
            label += "\n???";
        }
        if let Some(region_info) = self.facts2.region_inference_context.var_infos.get(*r) {
            label += &format!("\n{:?}, {:?}", region_info.origin, region_info.universe);
        }
        dot::LabelText::LabelStr(Cow::Owned(label))
    }
}

impl<'a, 'b, 'tcx> dot::GraphWalk<'a, RegionVid, Edge<'tcx>> for Graph<'b, 'tcx> {
    fn nodes(&self) -> dot::Nodes<'a, RegionVid> {
        let mut nodes: Vec<_> = self.all_nodes()
            .filter(|(r, _)| !self.skip_empty_nodes || self.has_associated_place(*r))
            .map(|(r, _)| r)
            .collect();
        // if self.static_regions.len() > 1 {
        //     nodes.push(usize::MAX);
        // }
        Cow::Owned(nodes)
    }

    fn edges(&'a self) -> dot::Edges<'a, Edge<'tcx>> {
        let mut edges = Vec::new();
        for (r, n) in self.all_nodes() {
            if self.skip_empty_nodes && !self.has_associated_place(r) {
                continue;
            }
            // if n.borrows_from_static {
            //     edges.push(Edge::new(c, usize::MAX, FxHashSet::default()));
            // }
            let visited = &mut FxHashSet::from_iter([r]);
            for (&b, edge) in &n.blocks {
                edges.extend(self.non_empty_edges(b, r, edge.clone(), visited));
            }
        }
        Cow::Owned(edges)
    }

    fn source(&self, e: &Edge<'tcx>) -> RegionVid { e.from }

    fn target(&self, e: &Edge<'tcx>) -> RegionVid { e.to }
}
