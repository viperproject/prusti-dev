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

use super::{cg::{NodeId, Edge, Graph, Regions, EdgeInfo}, region_place::Perms};

impl<'a, 'tcx> Graph<'a, 'tcx> {
    fn get_id(&self) -> &str {
        self.id.as_deref().unwrap_or("unnamed")
    }
}
impl<'a, 'tcx> Regions<'a, 'tcx> {
    pub(crate) fn is_empty_node(&self, n: NodeId) -> bool {
        self.get_corresponding_places(n).is_none()
    }
    // fn get_corresponding_places<'s>(&'s self, n: NodeId) -> impl Iterator<Item = &Perms<'tcx>> + 's {
    //     let node = self.graph.get_node(n);
    //     node.regions.iter().map(|r| &self.graph.cgx.region_map[r])
    // }
    fn get_corresponding_places(&self, n: NodeId) -> Option<&Perms<'tcx>> {
        let node = self.graph.get_node(n);
        // assert!(node.regions.len() == 1);
        // self.graph.cgx.region_map.get(node.regions.iter().next().unwrap())
        self.graph.cgx.region_map.get(&node.region)
    }
    pub(crate) fn is_borrow_only(&self, n: NodeId) -> Option<BorrowKind> {
        let node = self.graph.get_node(n);
        let input_facts = self.graph.facts.input_facts.borrow();
        for &(_, r) in &input_facts.as_ref().unwrap().use_of_var_derefs_origin {
            if node.region == r {
                return None;
            }
        }
        let mut is_borrow = None;
        for (_, data) in &self.graph.facts2.borrow_set.location_map {
            if node.region == data.region {
                if is_borrow.is_some() {
                    return None;
                }
                is_borrow = Some(data.kind);
            }
        }
        for (_, data) in &self.graph.cgx.sbs.location_map {
            if node.region == data.region {
                if is_borrow.is_some() {
                    return None;
                }
                is_borrow = Some(data.kind);
            }
        }
        is_borrow
    }
    fn non_empty_edges(&self, n: NodeId, start: NodeId, reasons: FxHashSet<EdgeInfo<'tcx>>) -> Vec<Edge<'tcx>> {
        if !(self.graph.skip_empty_nodes && self.is_empty_node(n)) {
            return vec![Edge::new(start, n, reasons)];
        }
        let mut edges = Vec::new();
        let node = self.graph.get_node(n);
        for (&b, edge) in &node.blocks {
            let mut reasons = reasons.clone();
            reasons.extend(edge);
            edges.extend(self.non_empty_edges(b, start, reasons));
        }
        edges
    }
}

impl<'a, 'b, 'tcx> dot::Labeller<'a, NodeId, Edge<'tcx>> for Regions<'b, 'tcx> {
    fn graph_id(&'a self) -> dot::Id<'a> { dot::Id::new(self.graph.get_id()).unwrap() }

    fn node_id(&'a self, n: &NodeId) -> dot::Id<'a> {
        dot::Id::new(format!("N_{n:?}_{}", self.graph.get_id())).unwrap()
    }

    fn edge_end_arrow(&'a self, e: &Edge) -> dot::Arrow {
        if self.is_borrow_only(e.from).is_some() {
            dot::Arrow::from_arrow(dot::ArrowShape::Dot(dot::Fill::Filled))
        } else {
            dot::Arrow::default()
        }
    }
    fn edge_style(&'a self, e: &Edge<'tcx>) -> dot::Style {
        if self.is_borrow_only(e.from).is_some() {
            dot::Style::Dashed
        } else {
            dot::Style::Solid
        }
    }
    fn edge_label(&'a self, e: &Edge<'tcx>) -> dot::LabelText<'a> {
        if e.to == usize::MAX {
            return dot::LabelText::LabelStr(Cow::Borrowed("static"));
        }
        let mut label = e.reasons.iter().map(|r| {
            let reason = match r.reason {
                ConstraintCategory::Return(_) => "return",
                ConstraintCategory::Yield => "yield",
                ConstraintCategory::UseAsConst => "const",
                ConstraintCategory::UseAsStatic => "static",
                ConstraintCategory::TypeAnnotation => "type",
                ConstraintCategory::Cast => "cast",
                ConstraintCategory::ClosureBounds => "closure",
                ConstraintCategory::CallArgument(_) => "arg",
                ConstraintCategory::CopyBound => "copy",
                ConstraintCategory::SizedBound => "sized",
                ConstraintCategory::Assignment => "assign",
                ConstraintCategory::Usage => "use",
                ConstraintCategory::OpaqueType => "opaque",
                ConstraintCategory::ClosureUpvar(_) => "upvar",
                ConstraintCategory::Predicate(_) => "pred",
                ConstraintCategory::Boring => "boring",
                ConstraintCategory::BoringNoLocation => "boring_nl",
                ConstraintCategory::Internal => "internal",
            };
            format!("{:?} ({reason})", r.creation)
        }).map(|s| format!("{s}\n")).collect::<String>();
        label = label[..label.len() - 1].to_string();
        dot::LabelText::LabelStr(Cow::Owned(label))
    }
    fn node_shape(&'a self, n: &NodeId) -> Option<dot::LabelText<'a>> {
        if *n == usize::MAX {
            return Some(dot::LabelText::LabelStr(Cow::Borrowed("house")));
        }
        self.is_borrow_only(*n).map(|kind| match kind {
            BorrowKind::Shared =>
                dot::LabelText::LabelStr(Cow::Borrowed("box")),
            BorrowKind::Shallow =>
                dot::LabelText::LabelStr(Cow::Borrowed("triangle")),
            BorrowKind::Mut { kind } =>
                dot::LabelText::LabelStr(Cow::Borrowed("ellipse")),
        })
    }
    fn node_label(&'a self, n: &NodeId) -> dot::LabelText<'a> {
        if *n == usize::MAX {
            let regions = &self.graph.static_regions;
            let places: Vec<_> = regions.iter().flat_map(|r| self.graph.cgx.region_map.get(r)).collect();
            return dot::LabelText::LabelStr(Cow::Owned(format!("'static\n{regions:?}\n{places:?}")));
        }
        let contained_by = self.get_corresponding_places(*n);
        let contained_by = contained_by.map(|c| format!("{c:?}")).unwrap_or_else(|| "???".to_string());
        // let process_place = |p: Place<'tcx>| p;
        // let contained_by = contained_by.collect::<Vec<_>>();
        let node = self.graph.get_node(*n);
        // assert!(node.regions.len() == 1);
        let label = format!("{:?}\n{contained_by}", node.region);
        dot::LabelText::LabelStr(Cow::Owned(label))
    }
}

impl<'a, 'b, 'tcx> dot::GraphWalk<'a, NodeId, Edge<'tcx>> for Regions<'b, 'tcx> {
    fn nodes(&self) -> dot::Nodes<'a, NodeId> {
        let mut nodes: Vec<_> = self.graph.nodes
            .iter()
            .enumerate()
            .filter_map(|(idx, n)| n.as_ref().map(|_| idx))
            .filter(|&idx| !self.graph.skip_empty_nodes || !self.is_empty_node(idx))
            .collect();
        if self.graph.static_regions.len() > 1 {
            nodes.push(usize::MAX);
        }
        Cow::Owned(nodes)
    }

    fn edges(&'a self) -> dot::Edges<'a, Edge<'tcx>> {
        let mut edges = Vec::new();
        for (c, n) in self.graph.nodes.iter().enumerate() {
            if let Some(n) = n {
                if self.graph.skip_empty_nodes && self.is_empty_node(c) {
                    continue;
                }
                if n.borrows_from_static {
                    edges.push(Edge::new(c, usize::MAX, FxHashSet::default()));
                }
                for (&b, edge) in &n.blocks {
                    edges.extend(self.non_empty_edges(b, c, edge.clone()));
                }
            }
        }
        Cow::Owned(edges)
    }

    fn source(&self, e: &Edge<'tcx>) -> NodeId { e.from }

    fn target(&self, e: &Edge<'tcx>) -> NodeId { e.to }
}
