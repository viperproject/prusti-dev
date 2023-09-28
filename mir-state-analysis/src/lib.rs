// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(box_patterns, hash_extract_if, extract_if)]

pub mod free_pcs;
pub mod utils;

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
