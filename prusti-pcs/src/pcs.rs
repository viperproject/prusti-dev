// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use crate::{
    pcs_analysis::conditional::CondPCSctx,
    syntax::MicroMirEncoder,
    util::{abbreviate_terminator, EncodingResult},
};
use prusti_common::report::log;
use prusti_interface::{
    environment::{
        borrowck::facts::{Point, PointType},
        mir_analyses::{
            allocation::{compute_definitely_allocated, DefinitelyAllocatedAnalysisResult},
            initialization::{compute_definitely_initialized, DefinitelyInitializedAnalysisResult},
        },
        mir_body::borrowck::facts::RichLocation,
        mir_sets::{LocalSet, PlaceSet},
        polonius_info::{graphviz, PoloniusInfo},
        Environment, Procedure,
    },
    utils::is_prefix,
    PrustiError,
};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    errors::MultiSpan,
    middle::mir::{BasicBlock, Body, Location, Mutability, Mutability::*, Place, TerminatorKind},
};
use std::{fs::File, io, io::Write};

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
        let local_def_id = proc_id.expect_local();
        let def_path = env.tcx().hir().def_path(local_def_id);
        // This panics all the time and is never called by anything else. Fixable?
        // graphviz(env, &def_path, *proc_id);
        let current_procedure: Procedure<'tcx> = env.get_procedure(*proc_id);
        let mir: &Body<'tcx> = current_procedure.get_mir();
        let current_procedure: Procedure<'tcx> = env.get_procedure(*proc_id);
        let polonius_info =
            PoloniusInfo::new_without_loop_invariant_block(env, &current_procedure).unwrap();

        log::report_with_writer(
            "pcs_input_facts",
            format!("{}.graph.dot", env.get_unique_item_name(*proc_id)),
            |writer| vis_input_facts(&polonius_info, &mir, writer).unwrap(),
        );
    }
    Ok(())
}

pub fn vis_input_facts<'mir, 'tcx: 'mir>(
    polonius_info: &PoloniusInfo<'mir, 'tcx>,
    mir: &'mir Body<'tcx>,
    writer: &mut dyn io::Write,
) -> Result<(), io::Error> {
    let mut bb_nodes: FxHashMap<BasicBlock, FxHashSet<usize>> = FxHashMap::default();
    let mut loan_live_at: FxHashMap<usize, Vec<usize>> = FxHashMap::default();

    println!("{:?}", polonius_info.borrowck_in_facts.loan_issued_at);

    // Populate bb_nodes with the CFG
    // TODO: Factor out this code
    for (l0, l1) in polonius_info.borrowck_in_facts.cfg_edge.iter() {
        let block_set_borrow_0 = bb_nodes
            .entry(polonius_info.interner.get_point(*l0).location.block)
            .or_insert(FxHashSet::default());
        (*block_set_borrow_0).insert(l0.index());
        loan_live_at.insert(
            l0.index(),
            match polonius_info.borrowck_out_facts.loan_live_at.get(l0) {
                Some(v) => v.iter().map(|loan| loan.index()).collect::<Vec<usize>>(),
                None => vec![],
            },
        );

        let block_set_borrow_1 = bb_nodes
            .entry(polonius_info.interner.get_point(*l1).location.block)
            .or_insert(FxHashSet::default());
        (*block_set_borrow_1).insert(l1.index());
        loan_live_at.insert(
            l1.index(),
            match polonius_info.borrowck_out_facts.loan_live_at.get(l1) {
                Some(v) => v.iter().map(|loan| loan.index()).collect::<Vec<usize>>(),
                None => vec![],
            },
        );
    }

    writeln!(writer, "digraph CFG {{")?;

    // Write locations into clusters
    for (bb, locations) in bb_nodes.drain() {
        writeln!(writer, "subgraph cluster{:?} {{", bb)?;
        writeln!(writer, "style=filled;")?;
        writeln!(writer, "color=lightgrey;")?;

        for loc in locations.iter() {
            let mut xlabel = "".to_string();

            match loan_live_at.get(loc) {
                Some(v) => {
                    if v.len() > 0 {
                        xlabel = format!("{}\nlive: {:?}", xlabel, v);
                    }
                }
                None => unreachable!(),
            };

            writeln!(
                writer,
                " {:?} [style=filled, color=white, shape=circle, xlabel=\"{}\"]",
                loc, xlabel
            )?;
        }
        writeln!(writer, "label={:?}", bb)?;
        writeln!(writer, "}}")?;
    }

    // Write the CFG edges with MIR annotations
    for (l0, l1) in polonius_info.borrowck_in_facts.cfg_edge.iter() {
        let rl0 = polonius_info.interner.get_point(*l0);
        let rl1 = polonius_info.interner.get_point(*l1);
        let mir_stmt = mir.stmt_at(rl0.location);
        let internal_edge = rl0.typ == PointType::Start && rl1.typ == PointType::Mid;

        if internal_edge && mir_stmt.is_left() {
            // Statement (not terminator)
            writeln!(
                writer,
                "{:?} -> {:?} [label=\"{:?}\"]",
                l0.index(),
                l1.index(),
                mir_stmt.left().unwrap()
            )?;
        } else if internal_edge && mir_stmt.is_right() {
            // Terminator
            writeln!(
                writer,
                "{:?} -> {:?} [label=\"({:?} term) {}\"]",
                l0.index(),
                l1.index(),
                rl0.location.block,
                abbreviate_terminator(&mir_stmt.right().unwrap().kind)
            )?;
        } else {
            // Edge between statements
            writeln!(writer, "{:?} -> {:?}", l0.index(), l1.index())?;
        }
    }

    writeln!(writer, "}}")?;

    Ok(())
}
