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
pub mod combined_pcs;

use combined_pcs::{PcsEngine, PlaceCapabilitySummary};
use free_pcs::{FreePlaceCapabilitySummary, engine::FpcsEngine};
use prusti_rustc_interface::{
    borrowck::consumers::BodyWithBorrowckFacts,
    dataflow::{Analysis, Results},
    index::IndexVec,
    middle::{
        mir::{Body, Promoted, START_BLOCK, BasicBlock},
        ty::TyCtxt,
    },
};

pub type FpcsOutput<'mir, 'tcx> = free_pcs::FreePcsAnalysis<'mir, 'tcx, PlaceCapabilitySummary<'mir, 'tcx>, PcsEngine<'mir, 'tcx>>;

#[tracing::instrument(name = "run_free_pcs", level = "debug", skip(mir, tcx))]
pub fn run_free_pcs<'mir, 'tcx>(
    mir: &'mir BodyWithBorrowckFacts<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> FpcsOutput<'mir, 'tcx> {
    let cgx = coupling_graph::CgContext::new(tcx, mir);
    let fpcs = PcsEngine::new(cgx);
    let analysis = fpcs
        .into_engine(tcx, &mir.body)
        .pass_name("free_pcs")
        .iterate_to_fixpoint();
    free_pcs::FreePcsAnalysis::new(analysis.into_results_cursor(&mir.body))
}

pub fn get_cgx<'mir, 'tcx>(
    mir: &'mir BodyWithBorrowckFacts<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> coupling_graph::CgContext<'mir, 'tcx> {
    coupling_graph::CgContext::new(tcx, mir)
}

pub fn test_free_pcs<'tcx>(
    mir: &BodyWithBorrowckFacts<'tcx>,
    promoted: &IndexVec<Promoted, Body<'tcx>>,
    tcx: TyCtxt<'tcx>,
) {
    let analysis = run_free_pcs(mir, tcx);
    free_pcs::check(analysis);
}

#[tracing::instrument(name = "run_coupling_graph", level = "debug", skip(tcx))]
pub fn run_coupling_graph<'mir, 'tcx>(
    cgx: coupling_graph::CgContext<'mir, 'tcx>,
    tcx: TyCtxt<'tcx>,
    top_crates: bool,
) -> coupling_graph::cursor::CgAnalysis<'mir, 'mir, 'tcx> {
    // if tcx.item_name(mir.source.def_id()).as_str().starts_with("main") {
    //     return;
    // }
    let cgx = std::rc::Rc::new(cgx);
    let fpcs = coupling_graph::engine::CgEngine::new(cgx.clone(), top_crates);
    let analysis = fpcs
        .into_engine(tcx, &cgx.mir.body)
        .pass_name("coupling_graph")
        .iterate_to_fixpoint();
    let mut c = analysis.into_results_cursor(&cgx.mir.body);
    if cfg!(debug_assertions) && !top_crates {
        coupling_graph::engine::draw_dots(&mut c);
    }
    c.seek_to_block_start(START_BLOCK);
    coupling_graph::cursor::CgAnalysis::new(c)
}

pub fn test_coupling_graph<'tcx>(
    mir: &BodyWithBorrowckFacts<'tcx>,
    tcx: TyCtxt<'tcx>,
    top_crates: bool,
) {
    // println!("{:?}", mir.source.def_id());
    // if !format!("{:?}", mir.source.def_id())
    //     .ends_with("parse_delimited)")
    // {
    //     return;
    // }

    let fpcs_analysis = run_free_pcs(mir, tcx);
    let cgx = coupling_graph::CgContext::new(tcx, mir);
    let cg_analysis = run_coupling_graph(cgx, tcx, top_crates);
    // coupling_graph::check(cg_analysis, fpcs_analysis);

    // panic!()
}
