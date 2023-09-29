// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cell::RefCell;

use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    data_structures::fx::{FxIndexMap, FxHashSet},
    borrowck::{
        borrow_set::{BorrowData, TwoPhaseActivation},
        consumers::{Borrows, BorrowIndex, RichLocation, OutlivesConstraint, PlaceConflictBias, places_conflict, calculate_borrows_out_of_scope_at_location},
    },
    dataflow::{Analysis, AnalysisDomain, ResultsCursor},
    index::{bit_set::{BitSet, HybridBitSet}, Idx},
    middle::{
        mir::{
            TerminatorKind, Operand, ConstantKind, StatementKind, Rvalue,
            visit::Visitor, BasicBlock, Body, CallReturnPlaces, Local, Place, Location, Statement, Terminator, TerminatorEdges, RETURN_PLACE,
        },
        ty::{RegionVid, TyCtxt},
    },
};

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, Fpcs},
    utils::PlaceRepacker, coupling_graph::{graph::{Graph, Node}, CgContext},
};

use super::triple::Cg;

#[tracing::instrument(name = "draw_dots", level = "debug", skip(c))]
pub(crate) fn draw_dots<'tcx, 'a>(mut c: ResultsCursor<'_, 'tcx, CoupligGraph<'a, 'tcx>>) {
    let mut graph = Vec::new();
    let body = c.body();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        if data.is_cleanup {
            continue;
        }
        c.seek_to_block_start(block);
        let mut g = c.get().clone();
        g.id = Some(format!("{block:?}_pre"));
        dot::render(&g, &mut graph).unwrap();
        for statement_index in 0..body.terminator_loc(block).statement_index+1 {
            c.seek_after_primary_effect(Location { block, statement_index });
            g = c.get().clone();
            g.id = Some(format!("{block:?}_{statement_index}"));
            dot::render(&g, &mut graph).unwrap();
        }
        if let TerminatorKind::Return = data.terminator().kind {
            g.skip_empty_nodes = true;
            g.id = Some(format!("{block:?}_ret"));
            dot::render(&g, &mut graph).unwrap();
        }
    }
    let combined = std::str::from_utf8(graph.as_slice()).unwrap().to_string();

    let regex = regex::Regex::new(r"digraph (([^ ])+) \{").unwrap();
    let combined = regex.replace_all(&combined, "subgraph cluster_$1 {\n    label = \"$1\"");

    std::fs::write("log/coupling/all.dot", format!("digraph root {{\n{combined}}}")).expect("Unable to write file");
}

pub(crate) struct CoupligGraph<'a, 'tcx> {
    cgx: &'a CgContext<'a, 'tcx>,
    out_of_scope: FxIndexMap<Location, Vec<BorrowIndex>>,
    flow_borrows: RefCell<ResultsCursor<'a, 'tcx, Borrows<'a, 'tcx>>>,
    top_crates: bool,
}

impl<'a, 'tcx> CoupligGraph<'a, 'tcx> {
    pub(crate) fn new(cgx: &'a CgContext<'a, 'tcx>, top_crates: bool) -> Self {
        if cfg!(debug_assertions) {
            std::fs::remove_dir_all("log/coupling").ok();
            std::fs::create_dir_all("log/coupling/individual").unwrap();
        }

        let borrow_set = &cgx.facts2.borrow_set;
        let regioncx = &*cgx.facts2.region_inference_context;
        let out_of_scope = calculate_borrows_out_of_scope_at_location(cgx.rp.body(), regioncx, borrow_set);
        let flow_borrows = Borrows::new(cgx.rp.tcx(), cgx.rp.body(), regioncx, borrow_set)
            .into_engine(cgx.rp.tcx(), cgx.rp.body())
            .pass_name("borrowck")
            .iterate_to_fixpoint()
            .into_results_cursor(cgx.rp.body());

        Self {
            cgx,
            out_of_scope,
            flow_borrows: RefCell::new(flow_borrows),
            top_crates
        }
    }
}

impl<'a, 'tcx> AnalysisDomain<'tcx> for CoupligGraph<'a, 'tcx> {
    type Domain = Cg<'a, 'tcx>;
    const NAME: &'static str = "coupling_graph";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        Cg::new(self.cgx, self.top_crates)
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        // // Sanity check (already done when creating region to place map)
        // if cfg!(debug_assertions) {
        //     let input_facts = self.facts.input_facts.borrow();
        //     let use_of_var_derefs_origin = &input_facts.as_ref().unwrap().use_of_var_derefs_origin;
        //     // Each region should only have a single associated local
        //     for (_, r) in use_of_var_derefs_origin {
        //         assert!(use_of_var_derefs_origin.iter().filter(|(_, ro)| r == ro).count() <= 1, "{use_of_var_derefs_origin:?}");
        //     }
        // }

        if !self.top_crates {
            println!("body: {body:#?}");
            println!("\ninput_facts: {:?}", self.cgx.facts.input_facts);
            println!("output_facts: {:#?}\n", self.cgx.facts.output_facts);
            println!("location_map: {:#?}\n", self.cgx.facts2.borrow_set.location_map);
            println!("activation_map: {:#?}\n", self.cgx.facts2.borrow_set.activation_map);
            println!("local_map: {:#?}\n", self.cgx.facts2.borrow_set.local_map);
            println!("region_inference_context: {:#?}\n", self.cgx.facts2.region_inference_context.outlives_constraints().collect::<Vec<_>>());
            // println!("locals_state_at_exit: {:#?}\n", self.facts2.borrow_set.locals_state_at_exit);
            let lt = self.cgx.facts.location_table.borrow();
            let lt = lt.as_ref().unwrap();
            for pt in lt.all_points() {
                println!("{pt:?} -> {:?} ({:?})", lt.to_location(pt), ""); //, self.facts.output_facts.origins_live_at(pt));
            }
            println!("out_of_scope: {:?}", self.out_of_scope);
            println!("region_map: {:#?}\n", self.cgx.region_map);
        }
    }
}

impl<'a, 'tcx> Analysis<'tcx> for CoupligGraph<'a, 'tcx> {
    #[tracing::instrument(name = "apply_statement_effect", level = "debug", skip(self))]
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        let l = format!("{:?}", location).replace('[', "_").replace(']', "");
        // println!("Location: {l}");
        state.id = Some(l.clone());

        if location.statement_index == 0 {
            state.version += 1;
            assert!(state.version < 10);

            // println!("\nblock: {:?}", location.block);
            if cfg!(debug_assertions) && !self.cgx.rp.body().basic_blocks[location.block].is_cleanup {
                state.output_to_dot(format!("log/coupling/individual/{l}_v{}_start.dot", state.version));
            }
            self.flow_borrows.borrow_mut().seek_to_block_start(location.block);
            state.live = self.flow_borrows.borrow().get().clone();
        }
        self.flow_borrows.borrow_mut().seek_after_primary_effect(location);
        let other = self.flow_borrows.borrow().get().clone();
        let delta = calculate_diff(&other, &state.live);

        let oos = self.out_of_scope.get(&location);
        state.handle_kills(&delta, oos, location);
        state.visit_statement(statement, location);
        state.handle_outlives(&delta, location);
        state.live = other;

        if cfg!(debug_assertions) && !self.cgx.rp.body().basic_blocks[location.block].is_cleanup {
            state.output_to_dot(format!("log/coupling/individual/{l}_v{}.dot", state.version));
        }
    }

    #[tracing::instrument(name = "apply_statement_effect", level = "debug", skip(self))]
    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        let l = format!("{:?}", location).replace('[', "_").replace(']', "");
        // println!("Location: {l}");
        state.id = Some(l.clone());

        if location.statement_index == 0 {
            state.version += 1;
            assert!(state.version < 10);

            // println!("\nblock: {:?}", location.block);
            if cfg!(debug_assertions) && !self.cgx.rp.body().basic_blocks[location.block].is_cleanup {
                state.output_to_dot(format!("log/coupling/individual/{l}_v{}_start.dot", state.version));
            }
            self.flow_borrows.borrow_mut().seek_to_block_start(location.block);
            state.live = self.flow_borrows.borrow().get().clone();
        }
        self.flow_borrows.borrow_mut().seek_after_primary_effect(location);
        let other = self.flow_borrows.borrow().get().clone();

        let delta = calculate_diff(&other, &state.live);
        let oos = self.out_of_scope.get(&location);
        state.handle_kills(&delta, oos, location);
        state.visit_terminator(terminator, location);
        state.handle_outlives(&delta, location);
        state.live = other;

        if cfg!(debug_assertions) && !self.cgx.rp.body().basic_blocks[location.block].is_cleanup {
            state.output_to_dot(format!("log/coupling/individual/{l}_v{}.dot", state.version));
        }
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing to do here
    }
}

#[derive(Debug)]
pub struct BorrowDelta {
    set: HybridBitSet<BorrowIndex>,
    pub cleared: HybridBitSet<BorrowIndex>,
}

fn calculate_diff(curr: &BitSet<BorrowIndex>, old: &BitSet<BorrowIndex>) -> BorrowDelta {
    let size = curr.domain_size();
    assert_eq!(size, old.domain_size());

    let mut set_in_curr = HybridBitSet::new_empty(size);
    let mut cleared_in_curr = HybridBitSet::new_empty(size);

    for i in (0..size).map(BorrowIndex::new) {
        match (curr.contains(i), old.contains(i)) {
            (true, false) => set_in_curr.insert(i),
            (false, true) => cleared_in_curr.insert(i),
            _ => continue,
        };
    }
    BorrowDelta {
        set: set_in_curr,
        cleared: cleared_in_curr,
    }
}
