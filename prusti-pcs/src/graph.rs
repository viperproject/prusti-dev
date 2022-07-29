// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::io;

use analysis::mir_utils::{self, PlaceImpl};
use prusti_interface::environment::borrowck::facts;
use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{mir, ty::TyCtxt},
};

pub trait GraphOps<'tcx> {
    fn mutable_borrow(
        &mut self,
        from: GraphNode<'tcx>,
        loan: facts::Loan,
        to: GraphNode<'tcx>,
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    );
    fn package(&mut self, from: GraphNode<'tcx>, to: GraphNode<'tcx>) -> Vec<Annotation<'tcx>>;
    fn unwind(&mut self, killed_loans: FxHashSet<facts::Loan>) -> GraphResult<'tcx>;
}

pub struct Graph<'tcx> {
    edges: Vec<GraphEdge<'tcx>>,
    pub leaves: FxHashSet<GraphNode<'tcx>>,
}

impl<'tcx> GraphOps<'tcx> for Graph<'tcx> {
    // TODO: if edges were a set then we could ignore duplicates, maybe a bit easier
    fn mutable_borrow(
        &mut self,
        from: GraphNode<'tcx>,
        loan: facts::Loan,
        to: GraphNode<'tcx>,
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) {
        let place = to.place;
        for i in 0..place.projection.len() {
            let node = GraphNode {
                place: mir::Place {
                    local: place.local,
                    projection: tcx.intern_place_elems(&place.projection[..i]),
                },
                location: to.location,
            };

            if !self.edges.iter().any(|edge| edge.to() == &node) {
                self.unpack(node, mir, tcx);
            }
        }

        self.leaves.remove(&to);
        self.leaves.insert(from);

        self.edges.push(GraphEdge::Borrow {
            from,
            loans: vec![loan],
            to,
        });
    }

    fn package(&mut self, from: GraphNode<'tcx>, to: GraphNode<'tcx>) -> Vec<Annotation<'tcx>> {
        let mut curr_node = from;
        let mut final_loans = Vec::new();
        let mut final_annotations = Vec::new();

        while curr_node != to {
            let curr_edge = self.take_edge(|edge| edge.comes_from(&curr_node));
            curr_node = *curr_edge.to();

            match curr_edge {
                GraphEdge::Borrow { loans, .. } => final_loans.extend(loans),
                GraphEdge::Pack { to, .. } => final_annotations.push(Annotation::Pack(to)),
                GraphEdge::Abstract { from, loans, to } => {
                    final_loans.extend(loans);
                    final_annotations.push(Annotation::Restore { from, to });
                }
                GraphEdge::Collapsed {
                    loans, annotations, ..
                } => {
                    final_loans.extend(loans);
                    final_annotations.extend(annotations);
                }
            }
        }

        self.edges.push(GraphEdge::Abstract {
            from,
            loans: final_loans,
            to,
        });
        final_annotations
    }

    fn unwind(&mut self, killed_loans: FxHashSet<facts::Loan>) -> GraphResult<'tcx> {
        self.collapse_killed(killed_loans);

        let leaves_before = self.leaves.clone();
        let annotations = leaves_before
            .iter()
            .flat_map(|leaf| self.unwind_path(*leaf))
            .collect();

        GraphResult {
            annotations,
            removed: &leaves_before - &self.leaves,
            added: &self.leaves - &leaves_before,
        }
    }
}

impl<'tcx> Graph<'tcx> {
    pub fn new() -> Self {
        Self {
            edges: Vec::new(),
            leaves: FxHashSet::default(),
        }
    }

    fn unpack(&mut self, node: GraphNode<'tcx>, mir: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) {
        let places = mir_utils::expand_struct_place(node.place, mir, tcx, None)
            .iter()
            .map(|p| GraphNode {
                place: p.to_mir_place(),
                location: node.location,
            })
            .collect::<Vec<_>>();

        self.leaves.remove(&node);
        for place in places.iter() {
            self.leaves.insert(*place);
        }

        self.edges.push(GraphEdge::Pack {
            from: places,
            to: node,
        });
    }

    fn collapse_killed(&mut self, killed_loans: FxHashSet<facts::Loan>) {
        for edge in &mut self.edges {
            match edge {
                GraphEdge::Borrow { loans, .. }
                | GraphEdge::Abstract { loans, .. }
                | GraphEdge::Collapsed { loans, .. } => {
                    loans.retain(|loan| !killed_loans.contains(loan));
                }
                GraphEdge::Pack { .. } => {}
            }
        }

        let mut collapsed_nodes = Vec::new();
        for edge in &self.edges {
            match edge {
                GraphEdge::Borrow { loans, to, .. }
                | GraphEdge::Abstract { loans, to, .. }
                | GraphEdge::Collapsed { loans, to, .. } => {
                    if loans.is_empty()
                        && self.edges.iter().any(|edge| {
                            !matches!(edge, GraphEdge::Pack { .. }) && edge.comes_from(to)
                        })
                    {
                        collapsed_nodes.push(*to);
                    }
                }
                GraphEdge::Pack { .. } => {}
            }
        }

        for node in collapsed_nodes {
            self.collapse(node);
        }
    }

    fn collapse(&mut self, node: GraphNode<'tcx>) {
        let mut final_loans = Vec::new();
        let mut final_annotations = Vec::new();

        let from_edge = self.take_edge(|edge| edge.to() == &node);
        let from = match from_edge {
            GraphEdge::Borrow { from, .. }
            | GraphEdge::Abstract { from, .. }
            | GraphEdge::Collapsed { from, .. } => from,
            GraphEdge::Pack { .. } => panic!("collapsing a pack edge is unsupported"),
        };

        let to_edge = self.take_edge(|edge| edge.comes_from(&node));
        let to = *to_edge.to();

        for edge in [from_edge, to_edge] {
            match edge {
                GraphEdge::Borrow { loans, .. } => final_loans.extend(loans),
                GraphEdge::Pack { .. } => panic!("collapsing a pack edge is unsupported"),
                GraphEdge::Abstract { from, loans, to } => {
                    final_loans.extend(loans);
                    final_annotations.push(Annotation::Restore { from, to });
                }
                GraphEdge::Collapsed {
                    loans, annotations, ..
                } => {
                    final_loans.extend(loans);
                    final_annotations.extend(annotations);
                }
            }
        }

        self.edges.push(GraphEdge::Collapsed {
            from,
            loans: final_loans,
            annotations: final_annotations,
            to,
        });
    }

    fn unwind_path(&mut self, start: GraphNode<'tcx>) -> Vec<Annotation<'tcx>> {
        let mut final_annotations = Vec::new();
        let mut curr = start;

        while let Some((idx, edge)) = self
            .edges
            .iter()
            .enumerate()
            .find(|(_, edge)| edge.comes_from(&curr))
        {
            curr = *edge.to();

            match edge {
                GraphEdge::Borrow { from, loans, to } if loans.is_empty() => {
                    self.leaves.remove(from);
                    self.leaves.insert(*to);

                    self.edges.remove(idx);
                }
                GraphEdge::Pack { from, to }
                    if !self.edges.iter().any(|edge| from.contains(edge.to())) =>
                {
                    self.leaves.insert(*to);
                    for place in from.iter() {
                        self.leaves.remove(place);
                    }

                    final_annotations.push(Annotation::Pack(*to));

                    self.edges.remove(idx);
                }
                GraphEdge::Abstract { from, loans, to } if loans.is_empty() => {
                    self.leaves.insert(*to);
                    self.leaves.remove(from);

                    final_annotations.push(Annotation::Restore {
                        from: *from,
                        to: *to,
                    });

                    self.edges.remove(idx);
                }
                GraphEdge::Collapsed {
                    from,
                    loans,
                    annotations,
                    to,
                } if loans.is_empty() => {
                    self.leaves.remove(from);
                    self.leaves.insert(*to);

                    final_annotations.extend(annotations);

                    self.edges.remove(idx);
                }
                _ => break,
            }
        }

        final_annotations
    }

    fn take_edge<F>(&mut self, pred: F) -> GraphEdge<'tcx>
    where
        F: FnMut(&mut GraphEdge<'tcx>) -> bool,
    {
        self.edges
            .drain_filter(pred)
            .next()
            .expect("target node to be found")
    }

    pub fn to_graphviz(&self, writer: &mut dyn io::Write) -> io::Result<()> {
        writeln!(writer, "digraph ReborrowingGraph {{")?;
        writeln!(writer, "rankdir=LR;")?;
        writeln!(writer, "graph [fontname=monospace];")?;
        writeln!(writer, "node [fontname=monospace];")?;
        writeln!(writer, "edge [fontname=monospace];")?;

        for edge in &self.edges {
            match edge {
                GraphEdge::Borrow { from, loans, to } => writeln!(
                    writer,
                    "\"{:?}\" -> \"{:?}\" [label={:?}];",
                    from,
                    to,
                    format!("loans: {:?}", loans)
                )?,
                GraphEdge::Pack { from, to } => {
                    for field in from {
                        writeln!(writer, "\"{:?}\" -> \"{:?}\" [color=blue];", field, to)?;
                    }
                }
                GraphEdge::Abstract { from, loans, to } => writeln!(
                    writer,
                    "\"{:?}\" -> \"{:?}\" [color=red,label={:?}];",
                    from,
                    to,
                    format!("loans: {:?}", loans)
                )?,
                GraphEdge::Collapsed {
                    from,
                    loans,
                    annotations,
                    to,
                } => writeln!(
                    writer,
                    "\"{:?}\" -> \"{:?}\" [color=green,label={:?}];",
                    from,
                    to,
                    format!("loans: {:?}\nannotations: {:?}", loans, annotations)
                )?,
            }
        }

        writeln!(writer, "}}")
    }
}

#[derive(Debug, Eq, Hash, PartialEq)]
enum GraphEdge<'tcx> {
    Borrow {
        from: GraphNode<'tcx>,
        loans: Vec<facts::Loan>,
        to: GraphNode<'tcx>,
    },
    Pack {
        from: Vec<GraphNode<'tcx>>, // TODO: this should be a known size since its the fields, maybe something like a smallvec instead
        to: GraphNode<'tcx>,
    },
    Abstract {
        from: GraphNode<'tcx>,
        loans: Vec<facts::Loan>,
        to: GraphNode<'tcx>,
    },
    Collapsed {
        from: GraphNode<'tcx>,
        loans: Vec<facts::Loan>,
        annotations: Vec<Annotation<'tcx>>,
        to: GraphNode<'tcx>,
    },
}

impl<'tcx> GraphEdge<'tcx> {
    fn comes_from(&self, node: &GraphNode<'tcx>) -> bool {
        match self {
            GraphEdge::Borrow { from, .. }
            | GraphEdge::Abstract { from, .. }
            | GraphEdge::Collapsed { from, .. } => from == node,
            GraphEdge::Pack { from, .. } => from.contains(node),
        }
    }

    fn to(&self) -> &GraphNode<'tcx> {
        match self {
            GraphEdge::Borrow { to, .. }
            | GraphEdge::Abstract { to, .. }
            | GraphEdge::Collapsed { to, .. }
            | GraphEdge::Pack { to, .. } => to,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
pub enum Annotation<'tcx> {
    Pack(GraphNode<'tcx>),
    Restore {
        from: GraphNode<'tcx>,
        to: GraphNode<'tcx>,
    },
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct GraphNode<'tcx> {
    pub place: mir::Place<'tcx>,
    pub location: mir::Location,
}

impl<'tcx> std::fmt::Debug for GraphNode<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}@{:?}", self.place, self.location)
    }
}

pub struct GraphResult<'tcx> {
    annotations: Vec<Annotation<'tcx>>,
    removed: FxHashSet<GraphNode<'tcx>>,
    added: FxHashSet<GraphNode<'tcx>>,
}
