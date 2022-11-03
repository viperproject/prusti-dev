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
        borrowck::facts::{BorrowckFacts, Loan, Point, PointIndex, PointType},
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
use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io,
    io::Write,
    rc::Rc,
};

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

        let polonius_facts = env.local_mir_borrowck_facts(local_def_id);

        let bctx = BorrowingContext {
            polonius_facts,
            mir: &mir,
        };

        log::report_with_writer(
            "pcs_input_facts",
            format!("{}.graph.dot", env.get_unique_item_name(*proc_id)),
            |writer| vis_input_facts(bctx, writer).unwrap(),
        );
    }
    Ok(())
}

// Computes the reborrowing DAG and outputs a graphviz file with it's trace
pub fn vis_input_facts<'mir, 'tcx: 'mir>(
    ctx: BorrowingContext<'mir, 'tcx>,
    writer: &mut dyn io::Write,
) -> Result<(), io::Error> {
    println!("{:?}", ctx.polonius_facts.output_facts);
    Ok(())
}

pub struct BorrowingContext<'mir, 'tcx: 'mir> {
    polonius_facts: Rc<BorrowckFacts>,
    mir: &'mir Body<'tcx>,
}

// Inefficient right now... but easy to write code for.
type Digraph<N, E> = Vec<(N, N, E)>;
type LoanSCC = Digraph<FxHashSet<Loan>, ()>;

impl<'mir, 'tcx: 'mir> BorrowingContext<'mir, 'tcx> {
    // Compute the strongly connected components of
    //      origin_contains_loan_at (intersect live loans?) at a point
    pub fn loan_scc_at(&self, loc: PointIndex) -> LoanSCC {
        // 1. Collect the loan_live_at fact
        todo!();
    }
}

// Todo: get rid of this thing
// pub fn vis_input_facts<'mir, 'tcx: 'mir>(
//     polonius_info: &PoloniusInfo<'mir, 'tcx>,
//     mir: &'mir Body<'tcx>,
//     writer: &mut dyn io::Write,
// ) -> Result<(), io::Error> {
//     let mut bb_nodes: FxHashMap<BasicBlock, FxHashSet<usize>> = FxHashMap::default();
//     let mut loan_live_at: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
//     let mut subsets: FxHashMap<
//         usize,
//         Option<&BTreeMap<rustc_middle::ty::RegionVid, BTreeSet<rustc_middle::ty::RegionVid>>>,
//     > = FxHashMap::default();
//
//     println!(
//         "kills: {:?}",
//         polonius_info.borrowck_in_facts.loan_killed_at
//     );
//     println!(
//         "issues: {:?}",
//         polonius_info.borrowck_in_facts.loan_issued_at
//     );
//     // println!(
//     //     "{:?}",
//     //     polonius_info.borrowck_out_facts.origin_live_on_entry
//     // );
//
//     // let u: usize =
//
//     let mut ocla_map: FxHashMap<usize, String> = FxHashMap::default();
//     let mut oloe_map: FxHashMap<usize, String> = FxHashMap::default();
//     let mut loan_to_origin: FxHashMap<usize, rustc_middle::ty::RegionVid> = FxHashMap::default();
//     let mut origin_to_loan: FxHashMap<rustc_middle::ty::RegionVid, usize> = FxHashMap::default();
//     let mut base_origins: FxHashSet<rustc_middle::ty::RegionVid> = FxHashSet::default();
//
//     for (r, ix, _) in polonius_info.borrowck_in_facts.loan_issued_at.iter() {
//         loan_to_origin.insert(ix.index().clone(), r.clone());
//         origin_to_loan.insert(r.clone(), ix.index().clone());
//         base_origins.insert(r.clone());
//     }
//
//     // Populate bb_nodes with the CFG
//     // TODO: Factor out this code
//     for (l0, l1) in polonius_info.borrowck_in_facts.cfg_edge.iter() {
//         let block_set_borrow_0 = bb_nodes
//             .entry(polonius_info.interner.get_point(*l0).location.block)
//             .or_insert(FxHashSet::default());
//         (*block_set_borrow_0).insert(l0.index());
//         loan_live_at.insert(
//             l0.index(),
//             match polonius_info.borrowck_out_facts.loan_live_at.get(l0) {
//                 Some(v) => v.iter().map(|loan| loan.index()).collect::<Vec<usize>>(),
//                 None => vec![],
//             },
//         );
//         subsets.insert(l0.index(), polonius_info.borrowck_out_facts.subset.get(l0));
//
//         if let Some(vocla) = polonius_info
//             .borrowck_out_facts
//             .origin_contains_loan_at
//             .get(l0)
//         {
//             ocla_map.insert(l0.index(), format!("{:?}", vocla));
//         }
//
//         if let Some(voloe) = polonius_info
//             .borrowck_out_facts
//             .origin_live_on_entry
//             .get(l0)
//         {
//             oloe_map.insert(l0.index(), format!("{:?}", voloe));
//         }
//
//         let block_set_borrow_1 = bb_nodes
//             .entry(polonius_info.interner.get_point(*l1).location.block)
//             .or_insert(FxHashSet::default());
//         (*block_set_borrow_1).insert(l1.index());
//         loan_live_at.insert(
//             l1.index(),
//             match polonius_info.borrowck_out_facts.loan_live_at.get(l1) {
//                 Some(v) => v.iter().map(|loan| loan.index()).collect::<Vec<usize>>(),
//                 None => vec![],
//             },
//         );
//         subsets.insert(l1.index(), polonius_info.borrowck_out_facts.subset.get(l1));
//         if let Some(vocla) = polonius_info
//             .borrowck_out_facts
//             .origin_contains_loan_at
//             .get(l1)
//         {
//             ocla_map.insert(l1.index(), format!("{:?}", vocla));
//         }
//         if let Some(voloe) = polonius_info
//             .borrowck_out_facts
//             .origin_live_on_entry
//             .get(l1)
//         {
//             oloe_map.insert(l1.index(), format!("{:?}", voloe));
//         }
//     }
//
//     writeln!(writer, "digraph CFG {{")?;
//     // writeln!(writer, "newrank=true;")?;
//
//     // Write locations into clusters
//     for (bb, locations) in bb_nodes.drain() {
//         writeln!(writer, "subgraph cluster{:?} {{", bb)?;
//         writeln!(writer, "style=filled;")?;
//         writeln!(writer, "color=orange;")?;
//
//         for loc in locations.iter() {
//             // writeln!(writer, "subgraph cluster{:?} {{", loc)?;
//             // writeln!(writer, "style=filled;")?;
//             // writeln!(writer, "color=orange;")?;
//
//             // writeln!(writer, " subs{:?} [style=invis]", loc)?;
//
//             // for og in base_origins.iter() {
//             //     writeln!(
//             //         writer,
//             //         "origin{:?}_{} [style=filled, color=white, shape=square, label=\"{}\"]",
//             //         loc,
//             //         prettify_origin(*og),
//             //         prettify_origin(*og),
//             //     )?;
//             // }
//
//             // if let Some(mp) = subsets.get(loc).unwrap() {
//             //     for (k, vs) in mp.iter() {
//             //         for v in vs.iter() {
//             //             writeln!(
//             //                 writer,
//             //                 "origin{:?}_{} -> origin{:?}_{}",
//             //                 loc,
//             //                 prettify_origin(*k),
//             //                 loc,
//             //                 prettify_origin(*v),
//             //             )?;
//             //         }
//             //     }
//             // }
//
//             // writeln!(writer, "label=\"subsets {:?}\"", loc)?;
//             // writeln!(writer, "}}")?;
//
//             let mut xlabel = "".to_string();
//
//             if let Some(v) = ocla_map.get(loc) {
//                 xlabel = format!("{} ocla: {}", xlabel, v);
//             }
//
//             if let Some(v) = oloe_map.get(loc) {
//                 xlabel = format!("{}\n oloe: {}", xlabel, v);
//             }
//
//             // match ocla_map.get(loc) {
//             //     Some(v) => {
//             //         xlabel = format!("{}\nlive: {:?}", xlabel, v);
//             //     }
//             //     None => unreachable!(),
//             // };
//
//             writeln!(
//                 writer,
//                 " {:?} [style=filled, color=white, shape=circle, xlabel=\"{}\"]",
//                 loc, xlabel
//             )?;
//
//             // writeln!(writer, " {:?} -> subs{:?} [weight=1.5]", loc, loc)?;
//         }
//         writeln!(writer, "label=\"{:?}\"", bb)?;
//         writeln!(writer, "}}")?;
//     }
//
//     // Write the CFG edges with MIR annotations
//     for (l0, l1) in polonius_info.borrowck_in_facts.cfg_edge.iter() {
//         let rl0 = polonius_info.interner.get_point(*l0);
//         let rl1 = polonius_info.interner.get_point(*l1);
//         let mir_stmt = mir.stmt_at(rl0.location);
//         let internal_edge = rl0.typ == PointType::Start && rl1.typ == PointType::Mid;
//
//         if internal_edge && mir_stmt.is_left() {
//             // Statement (not terminator)
//             writeln!(
//                 writer,
//                 "{:?} -> {:?} [label=\"{:?}\", lhead=cluster_{:?}, ltail=cluster_{:?}]",
//                 l0.index(),
//                 l1.index(),
//                 mir_stmt.left().unwrap(),
//                 l0.index(),
//                 l1.index(),
//             )?;
//         } else if internal_edge && mir_stmt.is_right() {
//             // Terminator
//             writeln!(
//                 writer,
//                 "{:?} -> {:?} [label=\"({:?} term) {}\", lhead=cluster_{:?}, ltail=cluster_{:?}, weight=1.5]",
//                 l0.index(),
//                 l1.index(),
//                 rl0.location.block,
//                 abbreviate_terminator(&mir_stmt.right().unwrap().kind),
//                 l0.index(),
//                 l1.index(),
//             )?;
//         } else {
//             // Edge between statements
//             writeln!(
//                 writer,
//                 "{:?} -> {:?} [lhead=cluster_{:?}, ltail=cluster_{:?}, weight=1.5]",
//                 l0.index(),
//                 l1.index(),
//                 l0.index(),
//                 l1.index(),
//             )?;
//         }
//         // writeln!(
//         //     writer,
//         //     "subs{:?} -> subs{:?} [style=invis, weight=1.5]",
//         //     l0.index(),
//         //     l1.index(),
//         // )?;
//     }
//
//     writeln!(writer, "}}")?;
//
//     Ok(())
// }

fn prettify_origin(og: rustc_middle::ty::RegionVid) -> String {
    format!("{:?}", og)[3..].to_owned()
}
