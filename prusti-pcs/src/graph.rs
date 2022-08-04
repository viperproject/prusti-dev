// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::io;

use analysis::mir_utils::{self, PlaceImpl};
use prusti_interface::environment::borrowck::facts;
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{mir, ty::TyCtxt},
};

pub trait ConditionalOps<'tcx>: Sized {
    // TODO: probably better to not clone here and use something like a cow/rc pointer
    fn branch(&self, condition: ConditionValue, start: mir::BasicBlock) -> Self;
    fn join(graphs: Vec<Self>) -> Self;
}

pub trait CoreOps<'tcx> {
    fn r#move(&mut self, new: GraphNode<'tcx>, old: GraphNode<'tcx>);
    fn mutable_borrow(
        &mut self,
        from: GraphNode<'tcx>,
        loan: facts::Loan,
        to: GraphNode<'tcx>,
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    );
    fn package(&mut self, from: GraphNode<'tcx>, to: GraphNode<'tcx>) -> Vec<Annotation<'tcx>>;
    fn unwind(&mut self, killed_loans: &FxHashSet<facts::Loan>) -> GraphResult<'tcx>;
}

pub trait ToGraphviz {
    fn to_graphviz(&self, writer: &mut dyn io::Write) -> io::Result<()>;
}

#[derive(Debug, Clone)]
pub enum ReborrowingGraph<'tcx> {
    Single(Graph<'tcx>),
    Branch {
        condition: ConditionId,
        graph: Box<ReborrowingGraph<'tcx>>,
    },
    Conditional {
        shared: Box<ReborrowingGraph<'tcx>>,
        start: mir::BasicBlock,
        graphs: FxHashMap<ConditionValue, ReborrowingGraph<'tcx>>,
    },
}

impl<'tcx> ConditionalOps<'tcx> for ReborrowingGraph<'tcx> {
    fn branch(&self, condition: ConditionValue, start: mir::BasicBlock) -> Self {
        Self::Branch {
            condition: ConditionId {
                value: condition,
                start,
            },
            graph: Box::new(self.clone()),
        }
    }

    fn join(graphs: Vec<Self>) -> Self {
        let mut graph_iter = graphs.into_iter();
        let first = graph_iter
            .next()
            .expect("join to be on at least two graphs");
        let start = if let ReborrowingGraph::Branch {
            condition: ConditionId { start, .. },
            ..
        } = first
        {
            start
        } else {
            panic!("join graphs should all be branches");
        };

        let (shared, unshared_graphs) = graph_iter.fold(
            (first, FxHashMap::default()),
            |(acc, mut unshared_graphs), item| {
                if let ReborrowingGraph::Branch {
                    condition,
                    mut graph,
                } = item
                {
                    let shared_graph = graph.intersection(&acc);
                    unshared_graphs.insert(condition.value, *graph);
                    (shared_graph, unshared_graphs)
                } else {
                    panic!("join graphs should all be branches");
                }
            },
        );

        Self::Conditional {
            shared: Box::new(shared),
            start,
            graphs: unshared_graphs,
        }
    }
}

impl<'tcx> CoreOps<'tcx> for ReborrowingGraph<'tcx> {
    // TODO: maybe a visitor for the core ops?
    fn r#move(&mut self, new: GraphNode<'tcx>, old: GraphNode<'tcx>) {
        match self {
            ReborrowingGraph::Single(graph) => graph.r#move(new, old),
            ReborrowingGraph::Branch { graph, .. } => graph.r#move(new, old),
            ReborrowingGraph::Conditional { shared, graphs, .. } => {
                if shared.any_edge_comes_from(&old) {
                    shared.r#move(new, old);
                } else {
                    for graph in graphs.values_mut() {
                        graph.r#move(new, old);
                    }
                }
            }
        }
    }

    fn mutable_borrow(
        &mut self,
        from: GraphNode<'tcx>,
        loan: facts::Loan,
        to: GraphNode<'tcx>,
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) {
        match self {
            ReborrowingGraph::Single(graph) => graph.mutable_borrow(from, loan, to, mir, tcx),
            ReborrowingGraph::Branch { graph, .. } => {
                graph.mutable_borrow(from, loan, to, mir, tcx)
            }
            ReborrowingGraph::Conditional { shared, graphs, .. } => {
                if shared.any_edge_goes_to(&to) {
                    shared.mutable_borrow(from, loan, to, mir, tcx)
                } else {
                    for graph in graphs.values_mut() {
                        graph.mutable_borrow(from, loan, to, mir, tcx)
                    }
                }
            }
        }
    }

    fn package(&mut self, from: GraphNode<'tcx>, to: GraphNode<'tcx>) -> Vec<Annotation<'tcx>> {
        match self {
            ReborrowingGraph::Single(graph) => graph.package(from, to),
            ReborrowingGraph::Branch { condition, graph } => {
                condition.apply_to(graph.package(from, to))
            }
            ReborrowingGraph::Conditional {
                shared,
                start,
                graphs,
            } => {
                if shared.any_edge_goes_to(&to) {
                    shared.package(from, to)
                } else {
                    graphs
                        .iter_mut()
                        .flat_map(|(condition_value, graph)| {
                            let condition = ConditionId {
                                value: *condition_value,
                                start: *start,
                            };

                            condition.apply_to(graph.package(from, to))
                        })
                        .collect()
                }
            }
        }
    }

    fn unwind(&mut self, killed_loans: &FxHashSet<facts::Loan>) -> GraphResult<'tcx> {
        match self {
            ReborrowingGraph::Single(graph) => graph.unwind(killed_loans),
            ReborrowingGraph::Branch { condition, graph } => {
                let result = graph.unwind(killed_loans);

                GraphResult {
                    annotations: condition.apply_to(result.annotations),
                    removed: result.removed,
                    added: result.added,
                }
            }
            ReborrowingGraph::Conditional {
                shared,
                start,
                graphs,
            } => {
                graphs.iter_mut().fold(
                    shared.unwind(killed_loans),
                    |acc, (condition_value, graph)| {
                        let mut result = graph.unwind(killed_loans);
                        let condition = ConditionId {
                            value: *condition_value,
                            start: *start,
                        };

                        result
                            .annotations
                            .append(&mut condition.apply_to(acc.annotations));
                        result.removed.extend(acc.removed); // TODO: under condition too?
                        result.added.extend(acc.added);

                        result
                    },
                )
            }
        }
    }
}

impl<'tcx> ReborrowingGraph<'tcx> {
    fn intersection(&mut self, other: &ReborrowingGraph<'tcx>) -> ReborrowingGraph<'tcx> {
        match (self, other) {
            (ReborrowingGraph::Single(self_graph), ReborrowingGraph::Single(other_graph)) => {
                let shared_edges = &self_graph.edges & &other_graph.edges;
                for edge in &shared_edges {
                    self_graph.edges.remove(edge);
                }

                let shared_leaves = &self_graph.leaves & &other_graph.leaves;
                for leaf in &shared_leaves {
                    self_graph.leaves.remove(leaf);
                }

                ReborrowingGraph::Single(Graph {
                    edges: shared_edges,
                    leaves: shared_leaves,
                })
            }
            (
                ReborrowingGraph::Branch {
                    condition,
                    graph: self_graph,
                },
                ReborrowingGraph::Branch {
                    graph: other_graph, ..
                },
            ) => ReborrowingGraph::Branch {
                condition: *condition,
                graph: Box::new(self_graph.intersection(other_graph)),
            },
            _ => Self::Single(Graph::new()),
        }
    }

    // TODO: can these two be abstracted by taking a closure?
    fn any_edge_comes_from(&self, node: &GraphNode<'tcx>) -> bool {
        match self {
            ReborrowingGraph::Single(graph) => graph.edges.iter().any(|edge| edge.comes_from(node)),
            ReborrowingGraph::Branch { graph, .. } => graph.any_edge_comes_from(node),
            ReborrowingGraph::Conditional { shared, graphs, .. } => {
                shared.any_edge_comes_from(node)
                    || graphs.values().any(|graph| graph.any_edge_comes_from(node))
            }
        }
    }

    fn any_edge_goes_to(&self, node: &GraphNode<'tcx>) -> bool {
        match self {
            ReborrowingGraph::Single(graph) => graph.edges.iter().any(|edge| edge.to() == node),
            ReborrowingGraph::Branch { graph, .. } => graph.any_edge_goes_to(node),
            ReborrowingGraph::Conditional { shared, graphs, .. } => {
                shared.any_edge_goes_to(node)
                    || graphs.values().any(|graph| graph.any_edge_goes_to(node))
            }
        }
    }
}

impl<'tcx> ToGraphviz for ReborrowingGraph<'tcx> {
    fn to_graphviz(&self, writer: &mut dyn io::Write) -> io::Result<()> {
        writeln!(writer, "digraph ReborrowingGraph {{")?;
        writeln!(writer, "rankdir=LR;")?;
        writeln!(writer, "graph [fontname=monospace];")?;
        writeln!(writer, "node [fontname=monospace];")?;
        writeln!(writer, "edge [fontname=monospace];")?;

        match self {
            ReborrowingGraph::Single(graph) => graph.edges_to_graphviz(writer)?,
            ReborrowingGraph::Branch { condition, graph } => {
                writeln!(writer, "subgraph \"cluster_{:?}\" {{", condition)?;
                writeln!(writer, "style=filled;")?;
                writeln!(writer, "color=lightgrey;")?;
                writeln!(writer, "node [style=filled,color=white];")?;
                graph.to_graphviz(writer)?;
                writeln!(
                    writer,
                    "label={:?};",
                    format!("condition value: {:?}", condition.value)
                )?;
                writeln!(writer, "}}")?;
            }
            ReborrowingGraph::Conditional {
                shared,
                start,
                graphs,
            } => {
                shared.to_graphviz(writer)?;

                writeln!(writer, "subgraph \"cluster_{:?}\" {{", start)?;
                writeln!(writer, "label={:?};", format!("condition at {:?}", start))?;
                writeln!(writer, "graph [style=dotted];")?;

                // TODO: duplicated with branch case
                for (condition_value, graph) in graphs {
                    let condition = ConditionId {
                        value: *condition_value,
                        start: *start,
                    };
                    writeln!(writer, "subgraph \"cluster_{:?}\" {{", condition)?;
                    writeln!(writer, "style=filled;")?;
                    writeln!(writer, "color=lightgrey;")?;
                    writeln!(writer, "node [style=filled,color=white];")?;
                    graph.to_graphviz(writer)?;
                    writeln!(
                        writer,
                        "label={:?};",
                        format!("condition value: {:?}", condition.value)
                    )?;
                    writeln!(writer, "}}")?;
                }

                writeln!(writer, "}}")?;
            }
        }

        writeln!(writer, "}}")
    }
}

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
pub struct ConditionId {
    value: ConditionValue,
    start: mir::BasicBlock,
}

impl ConditionId {
    fn apply_to<'tcx>(&self, annotations: Vec<Annotation<'tcx>>) -> Vec<Annotation<'tcx>> {
        annotations
            .into_iter()
            .map(|annotation| Annotation::Conditional {
                condition: *self,
                annotation: Box::new(annotation),
            })
            .collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConditionValue(u128);

#[derive(Debug, Clone)]
pub struct Graph<'tcx> {
    edges: FxHashSet<GraphEdge<'tcx>>,
    pub leaves: FxHashSet<GraphNode<'tcx>>,
}

impl<'tcx> CoreOps<'tcx> for Graph<'tcx> {
    fn r#move(&mut self, new: GraphNode<'tcx>, old: GraphNode<'tcx>) {
        let mut edge = self
            .take_edge(|edge| edge.comes_from(&old))
            .expect("old node to be found");

        match &mut edge {
            GraphEdge::Borrow { from, .. }
            | GraphEdge::Abstract { from, .. }
            | GraphEdge::Collapsed { from, .. } => {
                *from = new;
                self.edges.insert(edge);

                self.leaves.remove(&old);
                self.leaves.insert(new);
            }
            GraphEdge::Pack { .. } => panic!("moving a pack edge is unsupported"),
        }
    }

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

        self.edges.insert(GraphEdge::Borrow {
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
            let curr_edge = self
                .take_edge(|edge| edge.comes_from(&curr_node))
                .expect("node to be found");
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

        self.edges.insert(GraphEdge::Abstract {
            from,
            loans: final_loans,
            to,
        });
        final_annotations
    }

    fn unwind(&mut self, killed_loans: &FxHashSet<facts::Loan>) -> GraphResult<'tcx> {
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
            edges: FxHashSet::default(),
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

        self.edges.insert(GraphEdge::Pack {
            from: places,
            to: node,
        });
    }

    fn collapse_killed(&mut self, killed_loans: &FxHashSet<facts::Loan>) {
        // TODO: bit of a work around since you can't mutate set elements but we want sets for intersection
        //       maybe we could keep a separate list for the killed loans or a map from edges to loans
        self.edges
            .drain()
            .collect::<Vec<_>>()
            .into_iter()
            .for_each(|mut edge| {
                match &mut edge {
                    GraphEdge::Borrow { loans, .. }
                    | GraphEdge::Abstract { loans, .. }
                    | GraphEdge::Collapsed { loans, .. } => {
                        loans.retain(|loan| !killed_loans.contains(loan));
                    }
                    GraphEdge::Pack { .. } => {}
                }

                self.edges.insert(edge);
            });

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

        let from_edge = self
            .take_edge(|edge| edge.to() == &node)
            .expect("target node to be found");
        let from = match from_edge {
            GraphEdge::Borrow { from, .. }
            | GraphEdge::Abstract { from, .. }
            | GraphEdge::Collapsed { from, .. } => from,
            GraphEdge::Pack { .. } => panic!("collapsing a pack edge is unsupported"),
        };

        let to_edge = self
            .take_edge(|edge| edge.comes_from(&node))
            .expect("from node to be found");
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

        self.edges.insert(GraphEdge::Collapsed {
            from,
            loans: final_loans,
            annotations: final_annotations,
            to,
        });
    }

    fn unwind_path(&mut self, start: GraphNode<'tcx>) -> Vec<Annotation<'tcx>> {
        let mut final_annotations = Vec::new();
        let mut curr = start;

        while let Some(edge) = self.take_edge(|edge| edge.comes_from(&curr)) {
            curr = *edge.to();

            match edge {
                GraphEdge::Borrow { from, loans, to } if loans.is_empty() => {
                    self.leaves.remove(&from);
                    self.leaves.insert(to);
                }
                GraphEdge::Pack { from, to }
                    if !self.edges.iter().any(|edge| from.contains(edge.to())) =>
                {
                    self.leaves.insert(to);
                    for place in from.iter() {
                        self.leaves.remove(place);
                    }

                    final_annotations.push(Annotation::Pack(to));
                }
                GraphEdge::Abstract { from, loans, to } if loans.is_empty() => {
                    self.leaves.insert(to);
                    self.leaves.remove(&from);

                    final_annotations.push(Annotation::Restore { from, to });
                }
                GraphEdge::Collapsed {
                    from,
                    loans,
                    annotations,
                    to,
                } if loans.is_empty() => {
                    self.leaves.remove(&from);
                    self.leaves.insert(to);

                    final_annotations.extend(annotations);
                }
                _ => {
                    self.edges.insert(edge);
                    break;
                }
            }
        }

        final_annotations
    }

    fn take_edge<F>(&mut self, pred: F) -> Option<GraphEdge<'tcx>>
    where
        F: FnMut(&GraphEdge<'tcx>) -> bool,
    {
        self.edges.drain_filter(pred).next()
    }

    fn edges_to_graphviz(&self, writer: &mut dyn io::Write) -> io::Result<()> {
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

        Ok(())
    }
}

impl<'tcx> ToGraphviz for Graph<'tcx> {
    fn to_graphviz(&self, writer: &mut dyn io::Write) -> io::Result<()> {
        writeln!(writer, "digraph ReborrowingGraph {{")?;
        writeln!(writer, "rankdir=LR;")?;
        writeln!(writer, "graph [fontname=monospace];")?;
        writeln!(writer, "node [fontname=monospace];")?;
        writeln!(writer, "edge [fontname=monospace];")?;

        self.edges_to_graphviz(writer)?;

        writeln!(writer, "}}")
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
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

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum Annotation<'tcx> {
    Pack(GraphNode<'tcx>),
    Restore {
        from: GraphNode<'tcx>,
        to: GraphNode<'tcx>,
    },
    Conditional {
        condition: ConditionId,
        annotation: Box<Annotation<'tcx>>,
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
