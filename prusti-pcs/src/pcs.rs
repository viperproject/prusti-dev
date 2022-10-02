// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use crate::{pcs_analysis::conditional::CondPCSctx, syntax::MicroMirEncoder, util::EncodingResult};
use prusti_common::report::log;
use prusti_interface::{
    environment::{
        mir_analyses::{
            allocation::compute_definitely_allocated,
            initialization::compute_definitely_initialized,
        },
        polonius_info::PoloniusInfo,
        Environment, Procedure,
    },
    PrustiError,
};
use prusti_rustc_interface::{errors::MultiSpan, middle::mir::Body};
use std::{fs::File, io::Write};

/// Computes the PCS and prints it to the console
/// Currently the entry point for the compiler
pub fn dump_pcs<'env, 'tcx: 'env>(env: &'env Environment<'tcx>) -> EncodingResult<()> {
    for proc_id in env.get_annotated_procedures().iter() {
        println!("id: {:#?}", env.get_unique_item_name(*proc_id));
        let current_procedure: Procedure<'tcx> = env.get_procedure(*proc_id);
        let mir: &Body<'tcx> = current_procedure.get_mir();
        let micro_mir: MicroMirEncoder<'_, 'tcx> = MicroMirEncoder::expand_syntax(mir, env.tcx())?;
        micro_mir.pprint();

        let polonius_info =
            PoloniusInfo::new_without_loop_invariant_block(env, &current_procedure).unwrap();

        CondPCSctx {
            micro_mir: &(micro_mir.encoding),
            mir,
            env,
            init_analysis: compute_definitely_initialized((*proc_id).clone(), mir, env.tcx()),
            alloc_analysis: compute_definitely_allocated((*proc_id).clone(), mir),
            polonius_info,
        }
        .cond_pcs()?
        .pprint();

        // straight_line_pcs(&micro_mir, mir, env)?.pprint();
    }
    Ok(())
}

pub fn vis_pcs_facts<'env, 'tcx: 'env>(env: &'env Environment<'tcx>) -> EncodingResult<()> {
    for proc_id in env.get_annotated_procedures().iter() {
        println!("id: {:#?}", env.get_unique_item_name(*proc_id));
        let current_procedure: Procedure<'tcx> = env.get_procedure(*proc_id);
        let mir: &Body<'tcx> = current_procedure.get_mir();
        let micro_mir: MicroMirEncoder<'_, 'tcx> = MicroMirEncoder::expand_syntax(mir, env.tcx())?;
        micro_mir.pprint();

        let polonius_info =
            PoloniusInfo::new_without_loop_invariant_block(env, &current_procedure).unwrap();

        let ctx = CondPCSctx {
            micro_mir: &(micro_mir.encoding),
            mir,
            env,
            init_analysis: compute_definitely_initialized((*proc_id).clone(), mir, env.tcx()),
            alloc_analysis: compute_definitely_allocated((*proc_id).clone(), mir),
            polonius_info,
        };

        // let namespace = format!("pcs_input_facts_{:?}", proc_id);
        // let mut writer = File::create("hello.bees.dot").unwrap();
        log::report_with_writer("pcs_input_facts_test", "test.graph.dot", |writer| {
            ctx.vis_input_facts(writer).unwrap()
        });
    }
    Ok(())
}
