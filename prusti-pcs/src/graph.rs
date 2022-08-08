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
                leaves: &acc.leaves & &item.leaves,
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
    fn r#move(&mut self, new: GraphNode<'tcx>, old: GraphNode<'tcx>) {
        match self {
            Self::Single(graph) => graph.r#move(new, old),
            Self::Branch { graph, .. } => graph.r#move(new, old),
            Self::Conditional { shared, graphs, .. } => {
                if shared.any_edge(&mut |edge| edge.comes_from(&old)) {
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
            Self::Single(graph) => graph.mutable_borrow(from, loan, to, mir, tcx),
            Self::Branch { graph, .. } => graph.mutable_borrow(from, loan, to, mir, tcx),
            Self::Conditional { shared, graphs, .. } => {
                if shared.any_edge(&mut |edge| edge.goes_to(&to)) {
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

    fn unwind(&mut self, killed_loans: &FxHashSet<facts::Loan>) -> GraphResult<'tcx> {
        match self {
            Self::Single(graph) => graph.unwind(killed_loans),
            Self::Branch { condition, graph } => {
                let result = graph.unwind(killed_loans);

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
                        let mut result = graph.unwind(killed_loans);
                        let condition = ConditionId::new(*condition_value, *start);

                        result.annotations = condition.apply_to(result.annotations);

                        acc.combine(result)
                    },
                );
                let shared_result = shared.unwind(killed_loans);

                shared_result.combine(graphs_result)
            }
        }
    }
}

impl<'tcx> ReborrowingGraph<'tcx> {
    fn subtract(&mut self, other: &Graph<'tcx>) {
        match self {
            Self::Single(graph) => {
                for edge in &other.edges {
                    graph.edges.remove(edge);
                }
                for leaf in &other.leaves {
                    graph.leaves.remove(leaf);
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

#[derive(Debug, Clone, Default)]
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
        let place = to;
        for i in 0..place.projection.len() {
            let node = mir::Place {
                local: place.local,
                projection: tcx.intern_place_elems(&place.projection[..i]),
            };

            if !self.edges.iter().any(|edge| edge.goes_to(&node)) {
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
    fn unpack(&mut self, node: GraphNode<'tcx>, mir: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) {
        let places = mir_utils::expand_struct_place(node, mir, tcx, None)
            .iter()
            .map(|p| p.to_mir_place())
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
            .take_edge(|edge| edge.goes_to(&node))
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

    fn take_edge(&mut self, pred: impl FnMut(&GraphEdge<'tcx>) -> bool) -> Option<GraphEdge<'tcx>> {
        self.edges.drain_filter(pred).next()
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
    fn comes_from(&self, node: &GraphNode<'tcx>) -> bool {
        match self {
            Self::Borrow { from, .. }
            | Self::Abstract { from, .. }
            | Self::Collapsed { from, .. } => from == node,
            Self::Pack { from, .. } => from.contains(node),
        }
    }

    fn goes_to(&self, node: &GraphNode<'tcx>) -> bool {
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

pub type GraphNode<'tcx> = mir::Place<'tcx>;

#[derive(Default)]
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
