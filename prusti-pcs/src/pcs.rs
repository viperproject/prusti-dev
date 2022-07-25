// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use crate::{
    joins::{unify_moves, PCSRepacker},
    pcs_analysis::straight::straight_line_pcs,
    syntax::{
        hoare_semantics::HoareSemantics, LinearResource, MicroMirData, MicroMirEncoder,
        MicroMirStatement, MicroMirTerminator, PCSPermission, PCS,
    },
    util::EncodingResult,
};
use prusti_interface::{
    environment::{Environment, Procedure},
    utils::is_prefix,
    PrustiError,
};
use prusti_rustc_interface::{
    data_structures::stable_set::FxHashSet,
    errors::MultiSpan,
    middle::mir::{Body, Mutability, Place},
};
use std::iter::zip;

/// Computes the PCS and prints it to the console
/// Currently the entry point for the compiler
pub fn dump_pcs<'env, 'tcx: 'env>(env: &'env Environment<'tcx>) -> EncodingResult<()> {
    for proc_id in env.get_annotated_procedures().iter() {
        println!("id: {:#?}", env.get_unique_item_name(*proc_id));
        let current_procedure: Procedure<'tcx> = env.get_procedure(*proc_id);
        let mir: &Body<'tcx> = current_procedure.get_mir();
        let micro_mir: MicroMirEncoder<'tcx> = MicroMirEncoder::expand_syntax(mir)?;
        micro_mir.pprint();
        straight_line_pcs(&micro_mir, mir, env)?.pprint();
    }
    Ok(())
}
