// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{fmt::{Debug, Formatter, Result, Display}, borrow::Cow};

use derive_more::{Deref, DerefMut};
use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet},
    index::bit_set::BitSet,
    dataflow::fmt::DebugWithContext, index::IndexVec, middle::mir::Local,
    borrowck::{borrow_set::BorrowData, consumers::{BorrowIndex, RichLocation, OutlivesConstraint}},
    middle::{mir::{BasicBlock, ConstraintCategory, Place as MirPlace, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, RETURN_PLACE, Location, Operand, visit::Visitor}, ty::{RegionVid, TyKind}},
};

use crate::{
    free_pcs::{
        engine::FreePlaceCapabilitySummary, CapabilityLocal, CapabilityProjections, RepackOp,
    },
    utils::{PlaceRepacker, Place}, coupling_graph::{CgContext, region_place::Perms},
};

use super::{engine::{CoupligGraph, BorrowDelta}, graph::{Graph, Node}};


#[derive(Clone)]
pub struct Cg<'a, 'tcx> {
    pub id: Option<String>,
    pub cgx: &'a CgContext<'a, 'tcx>,

    pub(crate) live: BitSet<BorrowIndex>,
    pub version: usize,
    pub skip_empty_nodes: bool,
    pub top_crates: bool,

    pub graph: Graph<'tcx>,
}

impl Debug for Cg<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_struct("Graph")
            .field("id", &self.id)
            .field("nodes", &self.graph)
            .finish()
    }
}

impl PartialEq for Cg<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.graph == other.graph
    }
}
impl Eq for Cg<'_, '_> {}

impl<'a, 'tcx> DebugWithContext<CoupligGraph<'a, 'tcx>> for Cg<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        old: &Self,
        _ctxt: &CoupligGraph<'a, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> Result {
        Ok(())
    }
}

impl<'a, 'tcx: 'a> Cg<'a, 'tcx> {
    pub fn new(cgx: &'a CgContext<'a, 'tcx>, top_crates: bool) -> Self {
        let graph = Graph {
            nodes: IndexVec::from_elem_n(Node::new(), cgx.facts2.region_inference_context.var_infos.len()),
            static_regions: FxHashSet::from_iter([Graph::static_region()]),
        };
        let live = BitSet::new_empty(cgx.facts2.borrow_set.location_map.len());
        let mut result = Self {
            id: None,
            cgx,
            live,
            version: 0,
            skip_empty_nodes: false,
            top_crates,
            graph,
        };
        // let input_facts = facts.input_facts.borrow();
        // for &(r1, r2) in &input_facts.as_ref().unwrap().known_placeholder_subset {
        //     result.outlives(r1, r2);
        // }

        ////// Ignore all global outlives constraints for now to have a nice graph (i.e. result is not in the same node as args)
        let input_facts = cgx.facts.input_facts.borrow();
        let input_facts = input_facts.as_ref().unwrap();
        let constraints: Vec<_> = cgx.facts2.region_inference_context.outlives_constraints().collect();
        let constraints_no_loc: Vec<_> = constraints.iter().filter(|c| c.locations.from_location().is_none()).copied().collect();

        // Make one single `'static` node
        // let n = result.region_to_node(Self::static_region());
        // let node = result.get_node_mut(n);
        // let mut to_make_static = vec![Self::static_region()];
        // while let Some(r) = to_make_static.pop() {
        //     for c in constraints.iter().filter(|c| c.sub == r) {
        //         if node.regions.insert(c.sup) {
        //             to_make_static.push(c.sup);
        //         }
        //     }
        // }
        // println!("Static node: {node:?}");
        // let mut to_make_static = vec![Self::static_region()];
        // while let Some(r) = to_make_static.pop() {
        //     for &c in constraints_no_loc.iter().filter(|c| c.sub == r) {
        //         if result.outlives(c) {
        //             to_make_static.push(c.sup);
        //         }
        //     }
        // }

        result
    }
    pub(crate) fn get_associated_place(&self, r: RegionVid) -> Option<&Perms<'tcx>> {
        self.cgx.region_map.get(&r)
    }
    pub(crate) fn has_associated_place(&self, r: RegionVid) -> bool {
        self.cgx.region_map.contains_key(&r)
    }


    #[tracing::instrument(name = "handle_kills", level = "debug", skip(self))]
    pub fn handle_kills(&mut self, delta: &BorrowDelta, oos: Option<&Vec<BorrowIndex>>, location: Location) {
        let input_facts = self.cgx.facts.input_facts.borrow();
        let input_facts = input_facts.as_ref().unwrap();
        let location_table = self.cgx.facts.location_table.borrow();
        let location_table = location_table.as_ref().unwrap();

        // let input_facts = self.facts2.region_inference_context.borrow();

        for bi in delta.cleared.iter() {
            let data = &self.cgx.facts2.borrow_set[bi];
            // TODO: remove if the asserts below pass:
            let (r, _, l) = input_facts.loan_issued_at.iter().find(
                |(_, b, _)| bi == *b
            ).copied().unwrap();
            let l = rich_to_loc(location_table.to_location(l));
            assert_eq!(r, data.region);
            assert_eq!(l, data.reserve_location);

            // println!("killed: {r:?} {killed:?} {l:?}");
            if oos.map(|oos| oos.contains(&bi)).unwrap_or_default() {
                self.graph.kill_borrow(data);
            } else {
                self.graph.remove(data.region, location);
            }

            // // TODO: is this necessary?
            // let local = data.borrowed_place.local;
            // for region in input_facts.use_of_var_derefs_origin.iter().filter(|(l, _)| *l == local).map(|(_, r)| *r) {
            //     // println!("killed region: {region:?}");
            //     state.output_to_dot("log/coupling/kill.dot");
            //     let removed = state.remove(region, location, true, false);
            //     // assert!(!removed, "killed region: {region:?} at {location:?} (local: {local:?})");
            // }
        }

        if let Some(oos) = oos {
            for &bi in oos {
                // What is the difference between the two (oos)? It's that `delta.cleared` may kill it earlier than `oos`
                // imo we want to completely disregard `oos`. (TODO)
                // assert!(delta.cleared.contains(bi), "Cleared borrow not in out of scope: {:?} vs {:?} (@ {location:?})", delta.cleared, oos);
                if delta.cleared.contains(bi) {
                    continue;
                }

                let data = &self.cgx.facts2.borrow_set[bi];
                // TODO: remove if the asserts below pass:
                let (r, _, l) = input_facts.loan_issued_at.iter().find(
                    |(_, b, _)| bi == *b
                ).copied().unwrap();
                let l = rich_to_loc(location_table.to_location(l));
                assert_eq!(r, data.region);
                assert_eq!(l, data.reserve_location);

                self.graph.kill_borrow(data);

                // // TODO: is this necessary?
                // let local = data.assigned_place.local;
                // for region in input_facts.use_of_var_derefs_origin.iter().filter(|(l, _)| *l == local).map(|(_, r)| *r) {
                //     // println!("IHUBJ local: {local:?} region: {region:?}");
                //     let removed = state.remove(region, location, true, false);
                //     assert!(!removed);
                // }
            }
        }
    }

    #[tracing::instrument(name = "handle_outlives", level = "debug", skip(self))]
    pub fn handle_outlives(&mut self, delta: &BorrowDelta, location: Location) {
        for c in self.cgx.get_constraints_for_loc(Some(location)) {
            self.graph.outlives(c);
        }
    }

    #[tracing::instrument(name = "kill_shared_borrows_on_place", level = "debug", skip(self))]
    fn kill_shared_borrows_on_place(&mut self, location: Location, place: MirPlace<'tcx>) {
        let Some(local) = place.as_local() else {
            // Only remove nodes if assigned to the entire local (this is what rustc allows too)
            return
        };
        for (&region, _) in self.cgx.region_map.iter().filter(|(_, p)| p.place.local == local) {
            self.graph.remove(region, location);
        }
    }
}

impl<'tcx> Visitor<'tcx> for Cg<'_, 'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        match *operand {
            Operand::Copy(_) => (),
            Operand::Move(place) => {
                // TODO: check that this is ok (maybe issue if we move out of ref typed arg)
                // self.kill_shared_borrows_on_place(location, *place);
            }
            Operand::Constant(..) => {
                // TODO: anything here?
            }
        }
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        use StatementKind::*;
        match &statement.kind {
            Assign(box (place, _)) => {
                self.kill_shared_borrows_on_place(location, *place);
            }
            &StorageDead(local) => {
                self.kill_shared_borrows_on_place(location, local.into());
            }
            _ => (),
        };
        self.super_statement(statement, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.super_terminator(terminator, location);
        use TerminatorKind::*;
        match &terminator.kind {
            Goto { .. }
            | SwitchInt { .. }
            | UnwindResume
            | UnwindTerminate(_)
            | Unreachable
            | Assert { .. }
            | GeneratorDrop
            | FalseEdge { .. }
            | FalseUnwind { .. } => (),
            Return => {
                if cfg!(debug_assertions) && !self.cgx.rp.body().basic_blocks[location.block].is_cleanup {
                    let l = format!("{location:?}").replace('[', "_").replace(']', "");
                    self.output_to_dot(format!("log/coupling/individual/{l}_v{}_pre.dot", self.version));
                }

                // Pretend we have a storage dead for all `always_live_locals` other than the args/return
                for l in self.cgx.rp.always_live_locals_non_args().iter() {
                    self.kill_shared_borrows_on_place(location, l.into());
                }
                // Kill all the intermediate borrows, i.e. turn `return -> x.0 -> x` into `return -> x`
                for r in self.cgx.facts2.borrow_set.location_map.values().chain(self.cgx.sbs.location_map.values()) {
                    self.graph.remove(r.region, location);
                }

                let input_facts = self.cgx.facts.input_facts.borrow();
                let input_facts = input_facts.as_ref().unwrap();
                // TODO: use this
                let known_placeholder_subset = &input_facts.known_placeholder_subset;
                for c in self.cgx.get_constraints_for_loc(None).filter(|c| !self.cgx.ignore_outlives(*c)) {
                    self.graph.outlives(c);
                }
                self.merge_for_return();
            }
            &Drop { place, .. } => {
                
            }
            &Call { destination, .. } => {
                
            }
            &Yield { resume_arg, .. } => {
                
            }
            InlineAsm { .. } => todo!("{terminator:?}"),
        };
    }
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location:Location) {
        match rvalue {
            Rvalue::Use(Operand::Constant(_)) => {
                // TODO: this is a hack, find a better way to do things
                for c in self.cgx.get_constraints_for_loc(Some(location)) {
                    self.graph.outlives_static(c.sub, location);
                }
            }
            _ => (),
        }
        self.super_rvalue(rvalue, location);
    }
}

impl<'tcx> Cg<'_, 'tcx> {
    #[tracing::instrument(name = "Regions::merge_for_return", level = "trace")]
    pub fn merge_for_return(&self) {
        let outlives: Vec<_> = self.cgx.facts2.region_inference_context.outlives_constraints().filter(|c| c.locations.from_location().is_none()).collect();
        let in_facts = self.cgx.facts.input_facts.borrow();
        let universal_region = &in_facts.as_ref().unwrap().universal_region;

        for (r, node) in self.graph.all_nodes() {
            // Skip unknown empty nodes, we may want to figure out how to deal with them in the future
            if !self.has_associated_place(r) {
                continue;
            }

            if self.borrow_kind(r).is_some() {
                self.output_to_dot("log/coupling/error.dot");
                panic!("{node:?}");
            } else {
                // let r = *node.regions.iter().next().unwrap();
                if universal_region.contains(&r) {
                    continue;
                }

                let proof = outlives.iter().find(|c| {
                    universal_region.contains(&c.sub) && c.sup == r
                    // let r = c.sub.as_u32(); // The thing that lives shorter
                    // r == 0 || r == 1 // `0` means that it's static, `1` means that it's the function region
                });
                // If None then we have something left which doesn't outlive the function region!
                // if proof.is_none() {
                //     let in_facts = self.facts.input_facts.borrow();
                //     let r = &in_facts.as_ref().unwrap().universal_region;
                //     let outlives: Vec<_> = self.facts2.region_inference_context.outlives_constraints().collect();
                //     println!("Dumping graph to `log/coupling/error.dot`. Error: {outlives:?} (ur: {r:?})");
                //     // std::fs::remove_dir_all("log/coupling").ok();
                //     // std::fs::create_dir_all("log/coupling/individual").unwrap();
                //     let mut f = std::fs::File::create("log/coupling/error.dot").unwrap();
                //     dot::render(self, &mut f).unwrap();
                // }
                // println!("Found proof: {proof:?}");
                if proof.is_none() {
                    self.output_to_dot("log/coupling/error.dot");
                    panic!("Found a region which does not outlive the function region: {r:?} {node:?} ({universal_region:?})");
                }
            }
        }
        for &r in &self.graph.static_regions {
            if universal_region.contains(&r) {
                continue;
            }
            // It's possible that we get some random unnamed regions in the static set
            if !self.has_associated_place(r) {
                continue;
            }
            let proof = outlives.iter().find(|c| {
                universal_region.contains(&c.sub) && c.sup == r
            });
            if proof.is_none() {
                self.output_to_dot("log/coupling/error.dot");
                panic!("Found a region which does not outlive the function region: {r:?} ({universal_region:?})");
            }
        }
    }
    pub fn output_to_dot<P: AsRef<std::path::Path>>(&self, path: P) {
        if !self.top_crates {
            let mut f = std::fs::File::create(path).unwrap();
            dot::render(self, &mut f).unwrap();
        }
    }
}



fn rich_to_loc(l: RichLocation) -> Location {
    match l {
        RichLocation::Start(l) => l,
        RichLocation::Mid(l) => l,
    }
}

