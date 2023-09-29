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
pub mod r#loop;

use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    dataflow::Analysis,
    middle::{mir::Body, ty::TyCtxt},
};

#[tracing::instrument(name = "run_free_pcs", level = "debug", skip(tcx))]
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

#[tracing::instrument(name = "run_coupling_graph", level = "debug", skip(facts, facts2, tcx))]
pub fn run_coupling_graph<'mir, 'tcx>(
    mir: &'mir Body<'tcx>,
    facts: &'mir BorrowckFacts,
    facts2: &'mir BorrowckFacts2<'tcx>,
    tcx: TyCtxt<'tcx>,
    top_crates: bool,
) {
    // if tcx.item_name(mir.source.def_id()).as_str().starts_with("main") {
    //     return;
    // }
    // if !format!("{:?}", mir.source.def_id()).contains("fmt") {
    //     return;
    // }
    let cgx = coupling_graph::CgContext::new(tcx, mir, facts, facts2);
    let fpcs = coupling_graph::engine::CoupligGraph::new(&cgx, top_crates);
    let analysis = fpcs
        .into_engine(tcx, mir)
        .pass_name("coupling_graph")
        .iterate_to_fixpoint();
    let c = analysis.into_results_cursor(mir);
    if cfg!(debug_assertions) && !top_crates {
        coupling_graph::engine::draw_dots(c);
    }
}

pub fn test_coupling_graph<'tcx>(mir: &Body<'tcx>, facts: &BorrowckFacts, facts2: &BorrowckFacts2<'tcx>, tcx: TyCtxt<'tcx>, top_crates: bool) {
    let analysis = run_coupling_graph(mir, facts, facts2, tcx, top_crates);
    // free_pcs::check(analysis);
}
