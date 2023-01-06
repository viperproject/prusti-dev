// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use crate::{
    hyperdigraph::{Bijection, DHEdge, Hyperdigraph},
    pcs::{debug_print_scc, BorrowMove, LoanSCC},
};
use analysis::mir_utils::{self, PlaceImpl};
use prusti_interface::{
    environment::borrowck::facts::{Loan, PointIndex},
    utils::is_prefix,
};
use rustc_middle::{mir, ty::TyCtxt};
use std::{cmp::Ordering, collections::BTreeSet, fmt::Debug, iter::zip};

// Custom wrapper for MIR places, used to implement
//  1. ordering
//  2. tagging

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct CPlace<'tcx> {
    pub place: mir::Place<'tcx>,
    pub tag: Option<PointIndex>,
}

impl<'tcx> CPlace<'tcx> {
    pub fn cmp_local(&self, x: &CPlace<'tcx>) -> bool {
        self.place.local == x.place.local
    }

    /// Measure the lexicographic similarity between two place's projections
    pub fn cmp_lex(&self, x: &CPlace<'tcx>) -> u32 {
        let mut r: u32 = 0;
        for (p0, p1) in zip(self.place.iter_projections(), x.place.iter_projections()) {
            if p0 != p1 {
                break;
            }
            r += 1;
        }
        return r;
    }

    pub fn unpack(&self, mir: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> BTreeSet<Self> {
        mir_utils::expand_struct_place(self.place, mir, tcx, None)
            .iter()
            .map(|p| Self {
                place: p.to_mir_place(),
                tag: self.tag,
            })
            .collect()
    }
}

impl<'tcx> PartialOrd for CPlace<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'tcx> Ord for CPlace<'tcx> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.place.local.cmp(&other.place.local) {
            Ordering::Equal => self.place.projection.cmp(other.place.projection),
            r @ (Ordering::Less | Ordering::Greater) => r,
        }
    }
}

/// A Coupling DAG is a HyperDAG of places, with edges annotated by
/// families of loans of which there exists (dynamically, at runtime)
/// a sequence of Viper statements to consume the LHS and produce the RHS.

#[derive(Default, Clone)]
pub struct CouplingDigraph<'tcx> {
    graph: Hyperdigraph<CPlace<'tcx>>,
    annotations: Bijection<DHEdge<CPlace<'tcx>>, BTreeSet<Loan>>,
}

/// Finds the place in a set with the same local, and most similar projections (lex).
fn closest_node_to<'a, 'tcx>(
    target: &CPlace<'tcx>,
    space: &'a BTreeSet<CPlace<'tcx>>,
) -> Option<&'a CPlace<'tcx>> {
    space
        .iter()
        .filter(|p| target.cmp_local(p))
        .map(|p| (p, target.cmp_lex(p)))
        .max_by(|(_, m), (_, n)| m.cmp(n))
        .map(|r| r.0)
}

impl<'tcx> CouplingDigraph<'tcx> {
    /// Instead of adding a repack edge,
    ///     1. Remove the node p from the list of nodes
    ///     2. Replace LHS/RHS in any edge which include p with unpack(p)
    ///     3. Return a collection of the newly unpacked nodes
    /// As written this action possibly changes the signature of every edge
    ///     (but not the footprint). In practice I think it changes at most one edge,
    ///     and I also think this edge isn't internal. I'll have to rethink this.
    fn unpack_node_mut<'mir>(
        &mut self,
        mir: &'mir mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        node: &CPlace<'tcx>,
    ) -> BTreeSet<CPlace<'tcx>> {
        let unpacking = node.unpack(mir, tcx);
        let from = BTreeSet::from([(*node).clone()]);
        // Not sure yet that I want to replace in *all* nodes... revisit this.
        self.graph
            .replace_in_all_nodes(&from, &unpacking, &mut self.annotations);
        unpacking
    }

    #[allow(unused)]
    /// Add repack edge, returns a collection of the new nodes
    fn unpack_node<'mir>(
        &mut self,
        mir: &'mir mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        node: &CPlace<'tcx>,
    ) -> BTreeSet<CPlace<'tcx>> {
        let unpacking = node.unpack(mir, tcx);
        self.graph.include_edge(DHEdge {
            lhs: unpacking.clone(),
            rhs: BTreeSet::from([(*node).clone()]),
        });
        unpacking
    }

    /// Inserts repack edges into the graph so that "target" is reachable.
    /// Returns false if impossible (no places in the graph with the same base local)
    pub fn unpack_to_include<'mir>(
        &mut self,
        mir: &'mir mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        target: &CPlace<'tcx>,
    ) -> bool {
        let mut space: BTreeSet<CPlace<'tcx>> = (*self.graph.nodes()).clone();
        loop {
            let Some(closest) = closest_node_to(target, &space) else {
                return false;
            };
            if closest == target {
                return true;
            }
            space = self.unpack_node_mut(mir, tcx, closest);
        }
    }

    pub fn new_loan<'mir>(
        &mut self,
        mir: &'mir mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        lhs: BTreeSet<CPlace<'tcx>>,
        rhs: BTreeSet<CPlace<'tcx>>,
        loan: Loan,
    ) {
        println!("\tissuing loan {:?}", loan);
        println!("\t\t lhs {:?}", lhs);
        println!("\t\t rhs {:?}", rhs);
        for l in rhs.iter() {
            // If possible, unpack existing nodes to include
            //  It's no problem if this can't be done under the eager packing condition,
            //  fixme: To be robust, we should use the general repacker here so that the
            //      eager packing condition is not needed.
            //  (example: coupled loans x.f -> _ and x.g -> _. Then an edge has LHS {x.f, x.g} -> _,
            //      which violates the eager packing condition and this algorithm
            //      unnecessarily fails if we reborrow from x. Not sure if this comes up
            //     until borrow in structs though.)
            let _ = self.unpack_to_include(mir, tcx, l);
        }
        let edge = DHEdge { lhs, rhs };
        self.graph.include_edge(edge.clone());
        self.annotations.insert(edge, BTreeSet::from([loan]))
    }

    /// Core coupling method
    #[allow(unused)]
    fn couple_edges(&mut self, edges: &BTreeSet<DHEdge<CPlace<'tcx>>>) {
        // I'm not sure this works in general, this function
        // 1. Doesn't support repack edges (need to find an affine path first)
        // 2. Breaks on cyclic borrows
        let mut all_loans: BTreeSet<Loan> = BTreeSet::default();
        for e in edges.iter() {
            all_loans = all_loans
                .union(self.annotations.get_fwd(e).unwrap())
                .cloned()
                .collect();
            self.graph.remove_edge(e);
            self.annotations.remove_a(e);
        }

        let new_edge = self.graph.collapse_acyclic_affine_path(edges);
        self.graph.include_edge(new_edge.clone());
        self.annotations.insert(new_edge, all_loans);
    }

    /// Only retain loans in live origins
    /// fixme: should loans be killed when they're not live, or when they're not propagated?
    /// are these the same? implemented: the latter.
    pub fn update_cdg_with_expiries(&mut self, scc: &Option<LoanSCC>) {
        // For now, just remove from CDG
        // IRL: This emits a squence of coupled borrows to expire
        if let Some(scc_v) = scc {
            let live_loan_sets = &scc_v
                .0
                .nodes
                .iter()
                .cloned()
                .map(|ls| ls.into_iter().collect::<BTreeSet<_>>())
                .flatten()
                .collect::<BTreeSet<_>>();

            let mut edges_to_remove: BTreeSet<DHEdge<CPlace<'tcx>>> = Default::default();
            for e in self.graph.edges().iter() {
                if !live_loan_sets.is_superset(self.annotations.get_fwd(e).unwrap()) {
                    edges_to_remove.insert(e.clone());
                }
            }
            // println!("\t[expiring]: {:?}", edges_to_remove);
            for e in edges_to_remove.iter() {
                self.annotations.remove_a(e);
                self.graph.remove_edge(e);
            }
        } else {
            // Expire all loans in graph
            if !self.graph.is_empty() {
                self.graph = Default::default();
                self.annotations = Default::default();
            }
        }

        // todo (fixme) this is a hack
        self.graph.cleanup_nodes();
    }

    /// This is going to be implemented slightly ad-hoc.
    /// After computing some examples I'll have a better idea of
    /// a general algorithm here.
    ///
    /// REQUIRES: the nodes of the LoanSCC to be sets of nodes in the
    /// hypergraph (kills and new loans are applied)
    /// NOTE: Possibly less live loans than edges in CDG
    pub fn constrain_by_scc(&mut self, scc: &LoanSCC) {
        // If all origins either contain or do not contain a K-path,
        // quotient the graph by that K-path ("collapse" them).

        print!("\t[scc]");
        debug_print_scc(&scc);

        // "before" relation: ensure that
        println!("\tenter constraint algorithm");
        let distinguising_loans = scc.distinguishing_loans();
        for df in distinguising_loans.iter() {
            print!("\t\t[partition]: ");
            print_btree_inline(df);
        }

        // 1. Condense node constraints together
        for df in distinguising_loans.iter() {
            // 1.1 Using the reverse direction of the "annotation" bijection, assign each
            //      partite set to a family of nodes

            let existing_edges = self
                .annotations
                .fwd
                .iter()
                .filter(|(_, v)| v.is_subset(df))
                .collect::<BTreeSet<_>>();

            if existing_edges.len() > 1 {
                // let to_couple = existing_edges.iter().map(|x| x.0).cloned().collect();
                // self.couple_edges(&to_couple);
            }
        }

        // 2. Do we need to do anything with the arrows in the SCC graph?

        println!("\texit constraint algorithm");
    }

    pub fn pprint(&self) {
        self.graph.pprint_with_annotations(&self.annotations);
    }

    pub fn apply_borrow_move(&mut self, bm: BorrowMove<'tcx>, pt: PointIndex) {
        // Change all LHS which have "from" permission to the "to" permission.
        // The borrow checker enforces that
        //      > let mut s0 = S {x: 0, y: 0};
        //      > let bx = &mut s0.x;
        //      > let s1 = s0;
        //      > let bx1 = bx;
        // does not compile.

        // assert!(self.graph.nodes().contains(&CPlace {
        //     place: bm.to,
        //     tag: None
        // }));

        // MARKUS: I need to reorganize this

        println!("BEFORE KILLS: {:?}", self.graph.nodes());

        assert!(!self.graph.nodes().contains(&CPlace {
            place: bm.to,
            tag: Some(pt.clone())
        }));

        if self.graph.nodes().contains(&CPlace {
            place: bm.to,
            tag: None,
        }) {
            // 1. kill the "to" place
            self.graph.replace_nodes(
                CPlace {
                    place: bm.to,
                    tag: None,
                },
                CPlace {
                    place: bm.to,
                    tag: Some(pt),
                },
                &mut self.annotations,
            );
        }
        println!("AFTER KILLS: {:?}", self.graph.nodes());

        // 2. Now without conflicts, move the place
        assert!(self.graph.nodes().contains(&CPlace {
            place: bm.from,
            tag: None
        }));
        assert!(!self.graph.nodes().contains(&CPlace {
            place: bm.to,
            tag: None
        }));

        self.graph.replace_nodes(
            CPlace {
                place: bm.from,
                tag: None,
            },
            CPlace {
                place: bm.to,
                tag: None,
            },
            &mut self.annotations,
        );

        println!("AFTER MOVES: {:?}", self.graph.nodes());
    }

    // pub fn apply_kill(&mut self, p: mir::Place<'tcx>, l: PointIndex) {
    //     // Replace all nodes which are not tagged and whose place is a suffix of p, to be tagged at l.
    //     let to_kill = self
    //         .graph
    //         .nodes()
    //         .iter()
    //         .filter(|k| is_prefix(k.place, p))
    //         .filter(|k| k.tag.is_none())
    //         .cloned()
    //         .collect::<Vec<_>>();
    //     for k in to_kill.iter() {
    //         self.graph.replace_nodes(
    //             k.clone(),
    //             CPlace {
    //                 place: k.place,
    //                 tag: Some(l),
    //             },
    //             &mut self.annotations,
    //             false,
    //         )
    //     }
    //     todo!();
    // }
}

fn print_btree_inline<T>(set: &BTreeSet<T>)
where
    T: Debug,
{
    print!("{{");
    for s in set.iter() {
        print!("{:?}, ", s);
    }
    println!("}}");
}
