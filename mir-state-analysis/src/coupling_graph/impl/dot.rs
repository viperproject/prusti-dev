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

use super::cg::{NodeId, Edge, Graph};

impl<'a, 'tcx> Graph<'a, 'tcx> {
    fn get_id(&self) -> &str {
        self.id.as_deref().unwrap_or("unnamed")
    }
    fn get_corresponding_places(&self, n: NodeId) -> Vec<Perms<Place<'tcx>>> {
        let node = self.get_node(n);
        let mut contained_by: Vec<Perms<Place>> = Vec::new();
        let input_facts = self.facts.input_facts.borrow();
        for &(l, r) in &input_facts.as_ref().unwrap().use_of_var_derefs_origin {
            if node.regions.contains(&r) {
                contained_by.push(Perms::AllIn(r, l.into()));
            }
        }
        for (_, data) in &self.facts2.borrow_set.location_map {
            if node.regions.contains(&data.region) {
                contained_by.push(Perms::Exact(data.borrowed_place.into()));
            }
        }
        for data in &self.shared_borrows {
            if node.regions.contains(&data.region) {
                contained_by.push(Perms::Exact(data.borrowed_place.into()));
            }
        }
        contained_by
    }
    pub(crate) fn is_empty_node(&self, n: NodeId) -> bool {
        self.get_corresponding_places(n).is_empty()
    }
    fn non_empty_edges(&self, n: NodeId, start: NodeId, reasons: FxHashSet<ConstraintCategory<'tcx>>) -> Vec<Edge<'tcx>> {
        if !(self.skip_empty_nodes && self.is_empty_node(n)) {
            return vec![Edge::new(start, n, reasons)];
        }
        let mut edges = Vec::new();
        let node = self.get_node(n);
        for (&b, edge) in &node.blocks {
            let mut reasons = reasons.clone();
            reasons.extend(edge);
            edges.extend(self.non_empty_edges(b, start, reasons));
        }
        edges
    }
    pub(crate) fn is_borrow_only(&self, n: NodeId) -> Option<BorrowKind> {
        let node = self.get_node(n);
        let input_facts = self.facts.input_facts.borrow();
        for &(_, r) in &input_facts.as_ref().unwrap().use_of_var_derefs_origin {
            if node.regions.contains(&r) {
                return None;
            }
        }
        let mut is_borrow = None;
        for (_, data) in &self.facts2.borrow_set.location_map {
            if node.regions.contains(&data.region) {
                if is_borrow.is_some() {
                    return None;
                }
                is_borrow = Some(data.kind);
            }
        }
        for data in &self.shared_borrows {
            if node.regions.contains(&data.region) {
                if is_borrow.is_some() {
                    return None;
                }
                is_borrow = Some(data.kind);
            }
        }
        is_borrow
    }
}

#[derive(Debug, Copy, Clone)]
enum Perms<T> {
    Exact(T),
    AllIn(RegionVid, T),
}

impl<'a, 'b, 'tcx> dot::Labeller<'a, NodeId, Edge<'tcx>> for Graph<'b, 'tcx> {
    fn graph_id(&'a self) -> dot::Id<'a> { dot::Id::new(self.get_id()).unwrap() }

    fn node_id(&'a self, n: &NodeId) -> dot::Id<'a> {
        dot::Id::new(format!("N_{n:?}_{}", self.get_id())).unwrap()
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
        let mut label = e.reasons.iter().map(|r| match r {
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
        }).map(|s| format!("{s}, ")).collect::<String>();
        label = label[..label.len() - 2].to_string();
        dot::LabelText::LabelStr(Cow::Owned(label))
    }
    fn node_shape(&'a self, n: &NodeId) -> Option<dot::LabelText<'a>> {
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
        let process_place = |p: Place<'tcx>| p.to_string(self.rp);
        let contained_by = self.get_corresponding_places(*n);
        // let process_place = |p: Place<'tcx>| p;
        let contained_by = contained_by.iter().map(|&l| {
            match l {
                Perms::Exact(p) => Perms::Exact(process_place(p)),
                Perms::AllIn(r, mut p) => {
                    let mut ty = p.ty(self.rp).ty;
                    let mut made_precise = false;
                    while let TyKind::Ref(rr, inner_ty, _) = *ty.kind() {
                        ty = inner_ty;
                        p = p.mk_deref(self.rp);
                        if rr.is_var() && rr.as_var() == r {
                            made_precise = true;
                            break;
                        }
                    }
                    if made_precise {
                        Perms::Exact(process_place(p))
                    } else {
                        Perms::AllIn(r, process_place(p))
                    }
                }
            }
        }).collect::<Vec<_>>();
        let node = self.get_node(*n);
        let label = format!("{:?}\n{:?}", node.regions, contained_by);
        dot::LabelText::LabelStr(Cow::Owned(label))
    }
}

impl<'a, 'b, 'tcx> dot::GraphWalk<'a, NodeId, Edge<'tcx>> for Graph<'b, 'tcx> {
    fn nodes(&self) -> dot::Nodes<'a, NodeId> {
        let nodes: Vec<_> = self.nodes
            .iter()
            .enumerate()
            .filter_map(|(idx, n)| n.as_ref().map(|_| idx))
            .filter(|&idx| !self.skip_empty_nodes || !self.is_empty_node(idx))
            .collect();
        Cow::Owned(nodes)
    }

    fn edges(&'a self) -> dot::Edges<'a, Edge<'tcx>> {
        let mut edges = Vec::new();
        for (c, n) in self.nodes.iter().enumerate() {
            if let Some(n) = n {
                if self.skip_empty_nodes && self.is_empty_node(c) {
                    continue;
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
