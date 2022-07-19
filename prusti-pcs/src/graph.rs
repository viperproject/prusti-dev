// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use analysis::mir_utils::{self, PlaceImpl};
use prusti_interface::environment::borrowck::facts;
use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{mir, ty::TyCtxt},
};

struct Graph<'tcx> {
    edges: FxHashSet<GraphEdge<'tcx>>,
    leaves: FxHashSet<GraphNode<'tcx>>,
}

impl<'tcx> Graph<'tcx> {
    pub fn new() -> Self {
        Self {
            edges: FxHashSet::default(),
            leaves: FxHashSet::default(),
        }
    }

    pub fn unpack(
        &mut self,
        node: GraphNode<'tcx>, // TODO: maybe place instead (same for pack too)?
        mir: &mir::Body<'tcx>, // TODO: should these be parameters?
        tcx: TyCtxt<'tcx>,
    ) {
        let places = mir_utils::expand_struct_place(node.0.place, mir, tcx, None)
            .iter()
            .map(|p| {
                GraphNode(TaggedPlace {
                    place: p.to_mir_place(),
                    location: node.0.location,
                })
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

    pub fn pack(&mut self, node: GraphNode<'tcx>) -> GraphResult<'tcx> {
        let edge = self
            .edges
            .drain_filter(|edge| matches!(edge, GraphEdge::Pack { to, .. } if to == &node))
            .next()
            .expect("target node to be found");

        if let GraphEdge::Pack { from: places, .. } = edge {
            self.leaves.insert(node);
            for place in places.iter() {
                self.leaves.remove(place);
            }

            // TODO: probably not a good idea to clone each time
            (Annotation::Pack(node.0), self.leaves.clone())
        } else {
            panic!("should have found a pack edge")
        }
    }

    fn mutable_borrow(&mut self, from: GraphNode<'tcx>, loan: facts::Loan, to: GraphNode<'tcx>) {
        self.leaves.remove(&to);
        self.leaves.insert(from);

        self.edges.insert(GraphEdge::Borrow { from, loan, to });
    }

    fn package(&mut self, from: GraphNode<'tcx>, to: GraphNode<'tcx>) -> GraphResult<'tcx> {
        let mut curr = from;

        while curr != to {
            // TODO: helper for finding a node?
            let found = self
                .edges
                .iter()
                .find(|edge| match edge {
                    GraphEdge::Borrow { from, .. }
                    | GraphEdge::Abstract { from, .. }
                    | GraphEdge::Collapsed { from, .. } => from == &curr,
                    GraphEdge::Pack { from, .. } => from.contains(&curr),
                })
                .expect("target node to be found");
            // TODO: remove edge
            curr = match found {
                GraphEdge::Borrow { to, .. }
                | GraphEdge::Abstract { to, .. }
                | GraphEdge::Collapsed { to, .. }
                | GraphEdge::Pack { to, .. } => *to,
            }
        }

        todo!()
    }
}

#[derive(Eq, Hash, PartialEq)]
enum GraphEdge<'tcx> {
    Borrow {
        from: GraphNode<'tcx>,
        loan: facts::Loan,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct GraphNode<'tcx>(TaggedPlace<'tcx>);

#[derive(Eq, Hash, PartialEq)]
enum Annotation<'tcx> {
    Pack(TaggedPlace<'tcx>),
    Restore {
        from: GraphNode<'tcx>,
        to: GraphNode<'tcx>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct TaggedPlace<'tcx> {
    place: mir::Place<'tcx>,
    location: mir::Location,
}

type GraphResult<'tcx> = (Annotation<'tcx>, FxHashSet<GraphNode<'tcx>>);
