// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use prusti_rustc_interface::{
    borrowck::{
        borrow_set::{BorrowData, TwoPhaseActivation},
        consumers::{
            calculate_borrows_out_of_scope_at_location, places_conflict, BorrowIndex, Borrows,
            OutlivesConstraint, PlaceConflictBias, RichLocation,
        },
    },
    data_structures::fx::{FxHashSet, FxIndexMap},
    dataflow::{Analysis, AnalysisDomain, ResultsCursor},
    index::{
        bit_set::{BitSet, HybridBitSet},
        Idx,
    },
    middle::{
        mir::{
            visit::Visitor, BasicBlock, Body, CallReturnPlaces, ConstantKind, Local, Location,
            Operand, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorEdges,
            TerminatorKind, RETURN_PLACE, START_BLOCK,
        },
        ty::{RegionVid, TyCtxt},
    },
};

use crate::{
    coupling_graph::{
        consistency::CouplingConsistency,
        graph::{Graph, Node},
        outlives_info::AssignsToPlace,
        CgContext,
    },
    free_pcs::{CapabilityKind, CapabilityLocal},
    utils::PlaceRepacker,
};

use super::triple::CouplingGraph;

#[tracing::instrument(name = "draw_dots", level = "debug", skip(c))]
pub(crate) fn draw_dots<'tcx, 'a>(c: &mut ResultsCursor<'_, 'tcx, CgEngine<'a, 'tcx>>) {
    let mut graph = Vec::new();
    let body = c.body();
    c.seek_to_block_start(START_BLOCK);
    let mut g = c.get().clone();
    g.location.block = BasicBlock::MAX;
    dot::render(&g, &mut graph).unwrap();

    for (block, data) in body.basic_blocks.iter_enumerated() {
        if data.is_cleanup {
            continue;
        }
        c.seek_to_block_start(block);
        let mut g = c.get().clone();
        g.dot_node_filter = |k| k.local();
        g.dot_edge_filter = |sup, sub| !(sup.local() && sub.universal());
        dot::render(&g, &mut graph).unwrap();
        drop(g);
        for statement_index in 0..body.terminator_loc(block).statement_index {
            let location = Location {
                block,
                statement_index,
            };
            print_after_loc(c, location, &mut graph);
        }
        // Terminator
        let location = Location {
            block,
            statement_index: body.terminator_loc(block).statement_index,
        };
        if let TerminatorKind::Return = data.terminator().kind {
            c.seek_before_primary_effect(location);
            let mut g = c.get().clone();
            g.dot_node_filter = |k| !k.is_unknown_local();
            dot::render(&g, &mut graph).unwrap();
            c.seek_after_primary_effect(location);
            let mut g = c.get().clone();
            g.location = location.successor_within_block();
            g.dot_node_filter = |k| !k.is_unknown_local();
            dot::render(&g, &mut graph).unwrap();
        } else {
            print_after_loc(c, location, &mut graph);
        }
    }
    let combined = std::str::from_utf8(graph.as_slice()).unwrap().to_string();

    let regex = regex::Regex::new(r"digraph (([^ ])+) \{").unwrap();
    let combined = regex.replace_all(&combined, "subgraph cluster_$1 {\n    label = \"$1\"");

    std::fs::write(
        "log/coupling/all.dot",
        format!("digraph root {{\n{combined}}}"),
    )
    .expect("Unable to write file");
}

fn print_after_loc<'tcx, 'a>(
    c: &mut ResultsCursor<'_, 'tcx, CgEngine<'a, 'tcx>>,
    location: Location,
    graph: &mut Vec<u8>,
) {
    c.seek_after_primary_effect(location);
    let mut g = c.get().clone();
    g.dot_node_filter = |k| k.local();
    g.dot_edge_filter = |sup, sub| !(sup.local() && sub.universal());
    dot::render(&g, graph).unwrap();
}

pub(crate) struct CgEngine<'a, 'tcx> {
    pub(crate) cgx: Rc<CgContext<'a, 'tcx>>,
    bb_index: Cell<BasicBlock>,
    top_crates: bool,
}

impl<'a, 'tcx> CgEngine<'a, 'tcx> {
    pub(crate) fn new(cgx: Rc<CgContext<'a, 'tcx>>, top_crates: bool) -> Self {
        if cfg!(debug_assertions) && !top_crates {
            std::fs::remove_dir_all("log/coupling").ok();
            std::fs::create_dir_all("log/coupling/individual").unwrap();
        }

        let borrow_set = &cgx.mir.borrow_set;
        let regioncx = &*cgx.mir.region_inference_context;
        let out_of_scope =
            calculate_borrows_out_of_scope_at_location(cgx.rp.body(), regioncx, borrow_set);
        let flow_borrows = Borrows::new(cgx.rp.tcx(), cgx.rp.body(), regioncx, borrow_set)
            .into_engine(cgx.rp.tcx(), cgx.rp.body())
            .pass_name("borrowck")
            .iterate_to_fixpoint()
            .into_results_cursor(cgx.rp.body());

        if false && !top_crates {
            println!("body: {:#?}", cgx.rp.body());
            println!("\ninput_facts: {:?}", cgx.mir.input_facts);
            println!("output_facts: {:#?}\n", cgx.mir.output_facts);
            println!("location_map: {:#?}\n", cgx.mir.borrow_set.location_map);
            println!(
                "activation_map: {:#?}\n",
                cgx.mir.borrow_set.activation_map
            );
            println!("local_map: {:?}\n", cgx.mir.borrow_set.local_map);
            // println!("locals_state_at_exit: {:#?}\n", facts2.borrow_set.locals_state_at_exit);
            let lt = cgx.mir.location_table.as_ref().unwrap();
            for pt in lt.all_points() {
                println!("{pt:?} -> {:?} ({:?})", lt.to_location(pt), ""); //, facts.output_facts.origins_live_at(pt));
            }
            println!("out_of_scope: {:?}", out_of_scope);
            println!(
                "outlives_constraints: {:#?}\n",
                cgx.mir
                    .region_inference_context
                    .outlives_constraints()
                    .collect::<Vec<_>>()
            );
            println!("cgx: {:#?}\n", cgx);
            for r in cgx.region_info.map.all_regions() {
                println!(
                    "R: {r:?}: {:?}, {:?}",
                    cgx.mir.region_inference_context.var_infos.get(r),
                    cgx.region_info.map.get(r),
                );
            }
            panic!();
        }

        Self {
            cgx,
            bb_index: Cell::new(START_BLOCK),
            top_crates,
        }
    }
}

impl<'a, 'tcx> AnalysisDomain<'tcx> for CgEngine<'a, 'tcx> {
    type Domain = CouplingGraph<'a, 'tcx>;
    const NAME: &'static str = "coupling_graph";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        let block = self.bb_index.get();
        self.bb_index.set(block.plus(1));
        CouplingGraph::new(
            self.cgx.clone(),
            self.top_crates,
            block,
        )
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        self.bb_index.set(START_BLOCK);
        state.initialize_start_block(&self.cgx)
    }
}

impl<'a, 'tcx> Analysis<'tcx> for CgEngine<'a, 'tcx> {
    #[tracing::instrument(
        name = "CgEngine::apply_before_statement_effect",
        level = "debug",
        skip(self)
    )]
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        state.location = location;
        state.reset_ops();

        if location.statement_index == 0 {
            state.is_pre = false;
            // println!("\nblock: {:?}", location.block);
            let l = format!("{location:?}").replace('[', "_").replace(']', "");
            state.output_to_dot(
                format!(
                    "log/coupling/individual/{l}_v{}_start.dot",
                    state.sum_version()
                ),
                false,
            );
        }
        let oos = self.cgx.borrows_killed_at_location(location);
        state.handle_kills(oos, location, statement.kind.assigns_to());
        state.start = state.after.clone();
    }

    #[tracing::instrument(
        name = "CgEngine::apply_statement_effect",
        level = "debug",
        skip(self)
    )]
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        state.reset_ops();
        state.handle_outlives(location, statement.kind.assigns_to());
        state.visit_statement(statement, location);

        let l = format!("{location:?}").replace('[', "_").replace(']', "");
        state.output_to_dot(
            format!("log/coupling/individual/{l}_v{}.dot", state.sum_version()),
            false,
        );
    }

    #[tracing::instrument(
        name = "CgEngine::apply_before_terminator_effect",
        level = "debug",
        skip(self)
    )]
    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        // println!("Location: {l}");
        state.location = location;
        state.reset_ops();

        if location.statement_index == 0 {
            state.is_pre = false;
            // println!("\nblock: {:?}", location.block);
            let l = format!("{location:?}").replace('[', "_").replace(']', "");
            state.output_to_dot(
                format!(
                    "log/coupling/individual/{l}_v{}_start.dot",
                    state.sum_version()
                ),
                false,
            );
        }
        let oos = self.cgx.borrows_killed_at_location(location);
        state.handle_kills(oos, location, terminator.kind.assigns_to());
        state.start = state.after.clone();
    }

    #[tracing::instrument(
        name = "CgEngine::apply_terminator_effect",
        level = "debug",
        skip(self)
    )]
    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        state.reset_ops();
        state.handle_outlives(location, terminator.kind.assigns_to());
        state.visit_terminator(terminator, location);

        match &terminator.kind {
            TerminatorKind::Return => {
                let l = format!("{location:?}").replace('[', "_").replace(']', "");
                state.output_to_dot(
                    format!(
                        "log/coupling/individual/{l}_v{}_pre.dot",
                        state.sum_version()
                    ),
                    false,
                );
                // Pretend we have a storage dead for all `always_live_locals` other than the args/return
                for l in self.cgx.rp.always_live_locals_non_args().iter() {
                    state.kill_regions_on_place(Some(location), l.into());
                }
                // Kill all the intermediate borrows, i.e. turn `return -> x.0 -> x` into `return -> x`
                for r in self
                    .cgx
                    .mir
                    .borrow_set
                    .location_map
                    .values()
                    .chain(self.cgx.sbs.location_map.values())
                {
                    state.remove(r.region, Some(location));
                }

                state.merge_for_return(location);
            }
            _ => (),
        };

        let l = format!("{:?}", location).replace('[', "_").replace(']', "");
        state.output_to_dot(
            format!("log/coupling/individual/{l}_v{}.dot", state.sum_version()),
            false,
        );
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
