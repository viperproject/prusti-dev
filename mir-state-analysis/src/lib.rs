// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(box_patterns, hash_extract_if, extract_if)]

pub mod free_pcs;
pub mod utils;
pub mod coupling_graph;

use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    dataflow::Analysis,
    middle::{mir::Body, ty::TyCtxt},
};

pub fn run_free_pcs<'mir, 'tcx>(
    mir: &'mir Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> free_pcs::FreePcsAnalysis<'mir, 'tcx> {
    let fpcs = free_pcs::engine::FreePlaceCapabilitySummary::new(tcx, mir);
    let analysis = fpcs
        .into_engine(tcx, mir)
        .pass_name("free_pcs")
        .iterate_to_fixpoint();
    free_pcs::FreePcsAnalysis::new(analysis.into_results_cursor(mir))
}

pub fn test_free_pcs<'tcx>(mir: &Body<'tcx>, tcx: TyCtxt<'tcx>) {
    let analysis = run_free_pcs(mir, tcx);
    free_pcs::check(analysis);
}

pub fn run_coupling_graph<'mir, 'tcx>(
    mir: &'mir Body<'tcx>,
    facts: &'mir BorrowckFacts,
    facts2: &'mir BorrowckFacts2<'tcx>,
    tcx: TyCtxt<'tcx>,
) {
    // let name = tcx.opt_item_name(mir.source.def_id());
    // println!("Running for {}", name.as_ref().map(|n| n.as_str()).unwrap_or("unnamed"));
    println!("Running for {:?}", mir.source.def_id());
    // if tcx.item_name(mir.source.def_id()).as_str() == "main" {
    //     return;
    // }
    let fpcs = coupling_graph::engine::CoupligGraph::new(tcx, mir, facts, facts2);
    let analysis = fpcs
        .into_engine(tcx, mir)
        .pass_name("coupling_graph")
        .iterate_to_fixpoint();
    let c = analysis.into_results_cursor(mir);
    if cfg!(debug_assertions) {
        coupling_graph::engine::draw_dots(c);
    }
}

pub fn test_coupling_graph<'tcx>(mir: &Body<'tcx>, facts: &BorrowckFacts, facts2: &BorrowckFacts2<'tcx>, tcx: TyCtxt<'tcx>) {
    let analysis = run_coupling_graph(mir, facts, facts2, tcx);
    // free_pcs::check(analysis);
}
