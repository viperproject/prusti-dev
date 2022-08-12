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

/// The additional operations that can be performed to construct a conditional graph.
pub trait ConditionalOps<'tcx>: Sized {
    // TODO: probably better to not clone here and use something like a cow/rc pointer
    /// Creates a new branch graph under the given condition.
    fn branch(&self, condition: ConditionValue, start: mir::BasicBlock) -> Self;

    /// Given `n` different branch graphs starting at the same basic block, join them into one conditional graph.
    fn join(graphs: Vec<Self>) -> Self;
}

/// The operations that can be performed on a single graph without conditionals.
pub trait CoreOps<'tcx> {
    /// Changes the `old` node to `new`, potentially tagging `old` with `location` it is already present.
    fn r#move(&mut self, new: mir::Place<'tcx>, old: mir::Place<'tcx>, location: mir::Location);

    /// Creates a borrow edge starting at `from` and ending at `to` that is live for the given `loan`.
    /// If `to` has projections, it will generate the necessary unpack annotations.
    fn mutable_borrow(
        &mut self,
        from: mir::Place<'tcx>,
        loan: facts::Loan,
        to: mir::Place<'tcx>,
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Vec<Annotation<'tcx>>;

    /// Creates an abstract edge starting at `from` and ending at `to` and outputs the necessary
    /// annotations to be packaged.
    fn package(&mut self, from: mir::Place<'tcx>, to: mir::Place<'tcx>) -> Vec<Annotation<'tcx>>;

    /// Unrolls the graph starting at the leaves, keeping the loans that are still alive, and
    /// outputting the annotations needed to restore the newly added capabilities.
    fn unwind(&mut self, live_loans: &FxHashSet<facts::Loan>) -> GraphResult<'tcx>;
}

pub trait ToGraphviz {
    fn to_graphviz(&self, writer: &mut dyn io::Write) -> io::Result<()> {
        writeln!(writer, "digraph ReborrowingGraph {{")?;
        writeln!(writer, "rankdir=LR;")?;
        writeln!(writer, "graph [fontname=monospace];")?;
        writeln!(writer, "node [fontname=monospace];")?;
        writeln!(writer, "edge [fontname=monospace];")?;

        self.edges_to_graphviz(writer)?;

        writeln!(writer, "}}")
    }

    fn edges_to_graphviz(&self, writer: &mut dyn io::Write) -> io::Result<()>;
}

#[derive(Debug, Clone, PartialEq)]
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
            condition: ConditionId::new(condition, start),
            graph: Box::new(self.clone()),
        }
    }

    fn join(graphs: Vec<Self>) -> Self {
        let start = if let ReborrowingGraph::Branch { condition, .. } = graphs[0] {
            condition.start
        } else {
            panic!("join graphs should all be branches");
        };
        // TODO: not the nicest, should be a better way
        let shared: Graph = graphs
            .iter()
            .map(|graph| graph.shared_part())
            .cloned()
            .reduce(|acc, item| Graph {
                edges: &acc.edges & &item.edges,
            })
            .expect("join to be on at least two graphs");
        let unshared_graphs = graphs
            .into_iter()
            .map(|graph| {
                if let ReborrowingGraph::Branch {
                    condition,
                    mut graph,
                } = graph
                {
                    graph.subtract(&shared);
                    (condition.value, *graph)
                } else {
                    panic!("join graphs should all be branches")
                }
            })
            .collect::<FxHashMap<_, _>>();

        Self::Conditional {
            shared: Box::new(ReborrowingGraph::Single(shared)),
            start,
            graphs: unshared_graphs,
        }
    }
}

impl<'tcx> CoreOps<'tcx> for ReborrowingGraph<'tcx> {
    // TODO: maybe a visitor for the core ops?
    fn r#move(&mut self, new: mir::Place<'tcx>, old: mir::Place<'tcx>, location: mir::Location) {
        match self {
            Self::Single(graph) => graph.r#move(new, old, location),
            Self::Branch { graph, .. } => graph.r#move(new, old, location),
            Self::Conditional { shared, graphs, .. } => {
                if shared.any_edge(&mut |edge| edge.comes_from(&old)) {
                    shared.r#move(new, old, location);
                } else {
                    for graph in graphs.values_mut() {
                        graph.r#move(new, old, location);
                    }
                }
            }
        }
    }

    fn mutable_borrow(
        &mut self,
        from: mir::Place<'tcx>,
        loan: facts::Loan,
        to: mir::Place<'tcx>,
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Vec<Annotation<'tcx>> {
        match self {
            Self::Single(graph) => graph.mutable_borrow(from, loan, to, mir, tcx),
            Self::Branch { graph, .. } => graph.mutable_borrow(from, loan, to, mir, tcx),
            Self::Conditional {
                shared,
                start,
                graphs,
            } => {
                if shared.any_edge(&mut |edge| edge.goes_to(&to)) {
                    shared.mutable_borrow(from, loan, to, mir, tcx)
                } else {
                    graphs
                        .iter_mut()
                        .flat_map(|(condition_value, graph)| {
                            let condition = ConditionId {
                                value: *condition_value,
                                start: *start,
                            };

                            condition.apply_to(graph.mutable_borrow(from, loan, to, mir, tcx))
                        })
                        .collect()
                }
            }
        }
    }

    fn package(&mut self, from: mir::Place<'tcx>, to: mir::Place<'tcx>) -> Vec<Annotation<'tcx>> {
        match self {
            Self::Single(graph) => graph.package(from, to),
            Self::Branch { condition, graph } => condition.apply_to(graph.package(from, to)),
            Self::Conditional {
                shared,
                start,
                graphs,
            } => {
                if shared.any_edge(&mut |edge| edge.goes_to(&to)) {
                    shared.package(from, to)
                } else {
                    graphs
                        .iter_mut()
                        .flat_map(|(condition_value, graph)| {
                            ConditionId::new(*condition_value, *start)
                                .apply_to(graph.package(from, to))
                        })
                        .collect()
                }
            }
        }
    }

    fn unwind(&mut self, live_loans: &FxHashSet<facts::Loan>) -> GraphResult<'tcx> {
        match self {
            Self::Single(graph) => graph.unwind(live_loans),
            Self::Branch { condition, graph } => {
                let result = graph.unwind(live_loans);

                GraphResult {
                    annotations: condition.apply_to(result.annotations),
                    removed: result.removed,
                    added: result.added,
                }
            }
            Self::Conditional {
                shared,
                start,
                graphs,
            } => {
                let graphs_result = graphs.iter_mut().fold(
                    GraphResult::default(),
                    |acc, (condition_value, graph)| {
                        let mut result = graph.unwind(live_loans);
                        let condition = ConditionId::new(*condition_value, *start);

                        result.annotations = condition.apply_to(result.annotations);
                        result.annotations.extend(acc.annotations);
                        result.added = &result.added & &acc.added;
                        result.removed = &result.removed & &acc.removed;

                        result
                    },
                );
                let shared_result = shared.unwind(live_loans);

                shared_result.combine(graphs_result)
            }
        }
    }
}

impl<'tcx> ReborrowingGraph<'tcx> {
    pub fn unconditionally_accessible(&self) -> FxHashSet<mir::Place<'tcx>> {
        match self {
            ReborrowingGraph::Single(graph) => {
                // TODO: leaves should all be untagged?
                graph.leaves().into_iter().map(|node| node.place).collect()
            }
            ReborrowingGraph::Branch { graph, .. } => graph.unconditionally_accessible(),
            ReborrowingGraph::Conditional { shared, graphs, .. } => {
                let mut common = graphs
                    .values()
                    .map(|graph| graph.unconditionally_accessible())
                    .reduce(|acc, item| &acc & &item)
                    .unwrap();

                common.extend(shared.unconditionally_accessible());
                common
            }
        }
    }

    fn subtract(&mut self, other: &Graph<'tcx>) {
        match self {
            Self::Single(graph) => {
                for edge in &other.edges {
                    graph.edges.remove(edge);
                }
            }
            Self::Branch { graph, .. } => graph.subtract(other),
            Self::Conditional { shared, graphs, .. } => {
                shared.subtract(other);
                for graph in graphs.values_mut() {
                    graph.subtract(other);
                }
            }
        }
    }

    fn any_edge(&self, pred: &mut impl FnMut(&GraphEdge<'tcx>) -> bool) -> bool {
        match self {
            Self::Single(graph) => graph.edges.iter().any(pred),
            Self::Branch { graph, .. } => graph.any_edge(pred),
            Self::Conditional { shared, graphs, .. } => {
                shared.any_edge(pred) || graphs.values().any(|graph| graph.any_edge(pred))
            }
        }
    }

    /// The part of the graph that could be shared among conditionals.
    fn shared_part(&self) -> &Graph<'tcx> {
        match self {
            Self::Single(graph) => graph,
            Self::Branch { graph, .. } => graph.shared_part(),
            Self::Conditional { shared, .. } => shared.shared_part(),
        }
    }
}

impl<'tcx> ToGraphviz for ReborrowingGraph<'tcx> {
    fn edges_to_graphviz(&self, writer: &mut dyn io::Write) -> io::Result<()> {
        fn branch_to_graphviz<'tcx>(
            writer: &mut dyn io::Write,
            condition: &ConditionId,
            graph: &ReborrowingGraph<'tcx>,
        ) -> io::Result<()> {
            writeln!(writer, "subgraph \"cluster_{:?}\" {{", condition)?;
            writeln!(writer, "style=filled;")?;
            writeln!(writer, "color=lightgrey;")?;
            graph.edges_to_graphviz(writer)?;
            writeln!(writer, "label=\"{:?}\";", condition.value)?;
            writeln!(writer, "}}")
        }

        match self {
            Self::Single(graph) => graph.edges_to_graphviz(writer),
            Self::Branch { condition, graph } => branch_to_graphviz(writer, condition, graph),
            Self::Conditional {
                shared,
                start,
                graphs,
            } => {
                shared.edges_to_graphviz(writer)?;

                writeln!(writer, "subgraph \"cluster_{:?}\" {{", start)?;
                writeln!(writer, "label={:?};", format!("conditional at {:?}", start))?;
                writeln!(writer, "graph [style=dotted];")?;

                for (condition_value, graph) in graphs {
                    let condition = ConditionId::new(*condition_value, *start);
                    branch_to_graphviz(writer, &condition, graph)?;
                }

                writeln!(writer, "}}")
            }
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
pub struct ConditionId {
    value: ConditionValue,
    start: mir::BasicBlock,
}

impl ConditionId {
    pub fn new(value: ConditionValue, start: mir::BasicBlock) -> Self {
        Self { value, start }
    }

    // TODO: maybe this should just generate one annotation
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
pub struct ConditionValue(pub u128);

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Graph<'tcx> {
    edges: FxHashSet<GraphEdge<'tcx>>,
}

impl<'tcx> CoreOps<'tcx> for Graph<'tcx> {
    fn r#move(&mut self, new: mir::Place<'tcx>, old: mir::Place<'tcx>, location: mir::Location) {
        if self.edges.iter().any(|edge| edge.goes_to(&old)) {
            self.version(&old, location)
        }

        let mut edge = self
            .take_edge(|edge| edge.comes_from(&old))
            .expect("old node to be found");

        match &mut edge {
            GraphEdge::Borrow { from, .. }
            | GraphEdge::Abstract { from, .. }
            | GraphEdge::Collapsed { from, .. } => {
                *from = GraphNode::new(new);
                self.edges.insert(edge);
            }
            GraphEdge::Pack { .. } => panic!("moving a pack edge is unsupported"),
        }
    }

    fn mutable_borrow(
        &mut self,
        from: mir::Place<'tcx>,
        loan: facts::Loan,
        to: mir::Place<'tcx>,
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Vec<Annotation<'tcx>> {
        let mut unpacks = Vec::new();
        for i in 0..to.projection.len() {
            let to = mir::Place {
                local: to.local,
                projection: tcx.intern_place_elems(&to.projection[..i]),
            };

            if !self.edges.iter().any(|edge| edge.goes_to(&to)) {
                self.unpack(to, mir, tcx);
                unpacks.push(Annotation::Unpack(to));
            }
        }

        self.edges.insert(GraphEdge::Borrow {
            from: GraphNode::new(from),
            loans: vec![loan],
            to: GraphNode::new(to),
        });

        unpacks.into_iter().rev().collect()
    }

    fn package(&mut self, from: mir::Place<'tcx>, to: mir::Place<'tcx>) -> Vec<Annotation<'tcx>> {
        let from = GraphNode::new(from);
        let to = GraphNode::new(to);

        let mut curr_node = from;
        let mut final_loans = Vec::new();
        let mut final_annotations = Vec::new();

        while curr_node != to {
            let curr_edge = self
                .take_edge(|edge| edge.comes_from_node(&curr_node))
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

    fn unwind(&mut self, live_loans: &FxHashSet<facts::Loan>) -> GraphResult<'tcx> {
        self.collapse_killed(live_loans);

        let leaves_before = self.leaves();
        let mut leaves_after = leaves_before.clone();
        let annotations = leaves_before
            .iter()
            .flat_map(|leaf| self.unwind_path(*leaf, &mut leaves_after))
            .collect();

        GraphResult {
            annotations,
            removed: &leaves_before - &leaves_after,
            added: &leaves_after - &leaves_before,
        }
    }
}

impl<'tcx> Graph<'tcx> {
    fn unpack(&mut self, place: mir::Place<'tcx>, mir: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) {
        let places = mir_utils::expand_struct_place(place, mir, tcx, None)
            .iter()
            .map(|p| GraphNode::new(p.to_mir_place()))
            .collect::<Vec<_>>();

        self.edges.insert(GraphEdge::Pack {
            from: places,
            to: GraphNode::new(place),
        });
    }

    /// Remove the non-live loans from the graph and collapse nodes where possible.
    fn collapse_killed(&mut self, live_loans: &FxHashSet<facts::Loan>) {
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
                        loans.retain(|loan| live_loans.contains(loan));
                    }
                    GraphEdge::Pack { .. } => {}
                }

                self.edges.insert(edge);
            });

        self.nodes().into_iter().for_each(|node| {
            if node.is_collapsible(self) {
                self.collapse(node);
            }
        });
    }

    /// Create a collapsed edge from the edges that come from and go to a node.
    fn collapse(&mut self, node: GraphNode<'tcx>) {
        let mut final_loans = Vec::new();
        let mut final_annotations = Vec::new();

        let from_edge = self
            .take_edge(|edge| edge.goes_to_node(&node))
            .expect("target node to be found");
        let from = match from_edge {
            GraphEdge::Borrow { from, .. }
            | GraphEdge::Abstract { from, .. }
            | GraphEdge::Collapsed { from, .. } => from,
            GraphEdge::Pack { .. } => panic!("collapsing a pack edge is unsupported"),
        };

        let to_edge = self
            .take_edge(|edge| edge.comes_from_node(&node))
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

    /// Unwind as far as possible by following the path from `start`.
    /// Unwinds edges with no live loans on them and eagerly unwinds pack edges.
    fn unwind_path(
        &mut self,
        start: GraphNode<'tcx>,
        leaves: &mut FxHashSet<GraphNode<'tcx>>,
    ) -> Vec<Annotation<'tcx>> {
        let mut final_annotations = Vec::new();
        let mut curr = start;

        while let Some(edge) = self.take_edge(|edge| edge.comes_from_node(&curr)) {
            curr = *edge.to();

            match &edge {
                GraphEdge::Borrow { from, to, .. }
                | GraphEdge::Abstract { from, to, .. }
                | GraphEdge::Collapsed { from, to, .. } => {
                    leaves.remove(from);
                    leaves.insert(*to);
                }
                GraphEdge::Pack { from, to } => {
                    for field in from {
                        leaves.remove(field);
                    }
                    leaves.insert(*to);
                }
            }

            match edge {
                GraphEdge::Borrow { loans, .. } if loans.is_empty() => {}
                GraphEdge::Pack { from, to }
                    if !self.edges.iter().any(|edge| from.contains(edge.to())) =>
                {
                    final_annotations.push(Annotation::Pack(to));
                }
                GraphEdge::Abstract { from, loans, to } if loans.is_empty() => {
                    final_annotations.push(Annotation::Restore { from, to });
                }
                GraphEdge::Collapsed {
                    loans, annotations, ..
                } if loans.is_empty() => {
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

    /// Creates a version of all nodes and annotations of `place` in the graph that is tagged with the given `location`.
    fn version(&mut self, place: &mir::Place<'tcx>, location: mir::Location) {
        self.edges
            .drain()
            .collect::<Vec<_>>()
            .into_iter()
            .for_each(|mut edge| {
                match &mut edge {
                    GraphEdge::Borrow { from, to, .. } | GraphEdge::Abstract { from, to, .. } => {
                        from.version(place, location);
                        to.version(place, location);
                    }
                    GraphEdge::Pack { from, to } => {
                        for field in from {
                            field.version(place, location);
                        }
                        to.version(place, location);
                    }
                    GraphEdge::Collapsed {
                        from,
                        annotations,
                        to,
                        ..
                    } => {
                        from.version(place, location);
                        to.version(place, location);
                        for annotation in annotations {
                            annotation.version(place, location);
                        }
                    }
                }

                self.edges.insert(edge);
            });
    }

    fn take_edge(&mut self, pred: impl FnMut(&GraphEdge<'tcx>) -> bool) -> Option<GraphEdge<'tcx>> {
        self.edges.drain_filter(pred).next()
    }

    // TODO: this could probably be cached in a field
    fn leaves(&self) -> FxHashSet<GraphNode<'tcx>> {
        self.edges
            .iter()
            .fold(
                FxHashMap::default(),
                |mut degrees, edge| -> FxHashMap<GraphNode<'tcx>, usize> {
                    match edge {
                        GraphEdge::Borrow { from, to, .. }
                        | GraphEdge::Abstract { from, to, .. }
                        | GraphEdge::Collapsed { from, to, .. } => {
                            *degrees.entry(*from).or_default() += 1;
                            *degrees.entry(*to).or_default() += 1;
                        }
                        GraphEdge::Pack { from, to } => {
                            for field in from {
                                *degrees.entry(*field).or_default() += 1;
                            }
                            *degrees.entry(*to).or_default() += 1;
                        }
                    }

                    degrees
                },
            )
            .into_iter()
            .filter_map(|(node, count)| (count == 1).then_some(node))
            .collect()
    }

    fn nodes(&self) -> FxHashSet<GraphNode<'tcx>> {
        self.edges
            .iter()
            .fold(FxHashSet::default(), |mut nodes, edge| {
                match edge {
                    GraphEdge::Borrow { from, to, .. }
                    | GraphEdge::Abstract { from, to, .. }
                    | GraphEdge::Collapsed { from, to, .. } => {
                        nodes.insert(*from);
                        nodes.insert(*to);
                    }
                    GraphEdge::Pack { from, to } => {
                        nodes.extend(from);
                        nodes.insert(*to);
                    }
                }

                nodes
            })
    }
}

impl<'tcx> ToGraphviz for Graph<'tcx> {
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
    fn comes_from(&self, place: &mir::Place<'tcx>) -> bool {
        self.comes_from_node(&GraphNode::new(*place))
    }

    fn goes_to(&self, place: &mir::Place<'tcx>) -> bool {
        self.goes_to_node(&GraphNode::new(*place))
    }

    fn comes_from_node(&self, node: &GraphNode<'tcx>) -> bool {
        match self {
            Self::Borrow { from, .. }
            | Self::Abstract { from, .. }
            | Self::Collapsed { from, .. } => from == node,
            Self::Pack { from, .. } => from.contains(node),
        }
    }

    fn goes_to_node(&self, node: &GraphNode<'tcx>) -> bool {
        self.to() == node
    }

    fn to(&self) -> &GraphNode<'tcx> {
        match self {
            Self::Borrow { to, .. }
            | Self::Abstract { to, .. }
            | Self::Collapsed { to, .. }
            | Self::Pack { to, .. } => to,
        }
    }

    fn is_collapsible(&self) -> bool {
        match self {
            Self::Borrow { loans, .. }
            | Self::Abstract { loans, .. }
            | Self::Collapsed { loans, .. } => loans.is_empty(),
            Self::Pack { .. } => false,
        }
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum Annotation<'tcx> {
    Unpack(mir::Place<'tcx>),
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

impl<'tcx> Annotation<'tcx> {
    fn version(&mut self, place: &mir::Place<'tcx>, location: mir::Location) {
        match self {
            Annotation::Unpack(_) => {}
            Annotation::Pack(node) => node.version(place, location),
            Annotation::Restore { from, to } => {
                from.version(place, location);
                to.version(place, location);
            }
            Annotation::Conditional { annotation, .. } => {
                annotation.version(place, location);
            }
        }
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct GraphNode<'tcx> {
    place: mir::Place<'tcx>,
    tag: Option<mir::Location>,
}

impl<'tcx> std::fmt::Debug for GraphNode<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.tag {
            Some(tag) => write!(f, "{:?}@{:?}", self.place, tag),
            None => write!(f, "{:?}", self.place),
        }
    }
}

impl<'tcx> GraphNode<'tcx> {
    pub fn new(place: mir::Place<'tcx>) -> Self {
        Self { place, tag: None }
    }

    fn version(&mut self, place: &mir::Place<'tcx>, location: mir::Location) {
        if self.place == *place && self.tag.is_none() {
            self.tag = Some(location);
        }
    }

    fn is_collapsible(&self, graph: &Graph<'tcx>) -> bool {
        let from_edge = graph.edges.iter().find(|edge| edge.goes_to_node(self));
        let to_edge = graph.edges.iter().find(|edge| edge.comes_from_node(self));

        match (from_edge, to_edge) {
            (Some(from_edge), Some(to_edge)) => {
                from_edge.is_collapsible() && to_edge.is_collapsible()
            }
            _ => false,
        }
    }
}

#[derive(Debug, Default)]
pub struct GraphResult<'tcx> {
    annotations: Vec<Annotation<'tcx>>,
    removed: FxHashSet<GraphNode<'tcx>>,
    added: FxHashSet<GraphNode<'tcx>>,
}

impl<'tcx> GraphResult<'tcx> {
    fn combine(mut self, other: Self) -> Self {
        self.annotations.extend(other.annotations);
        self.removed.extend(other.removed);
        self.added.extend(other.added);
        self
    }
}
