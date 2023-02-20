// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![allow(unused)]
use prusti_rustc_interface::middle::mir::{
    Operand::Move,
    Rvalue::{Ref, Use},
    StatementKind::Assign,
};
use rustc_middle::mir::{Place, Statement};
use rustc_mir_dataflow::{move_paths::MoveData, MoveDataParamEnv};
use std::{collections::BTreeSet, default::Default, fmt::Debug};

use crate::{
    coupling_digraph::*,
    pcs_analysis::conditional::CondPCSctx,
    syntax::MicroMirEncoder,
    util::{abbreviate_terminator, EncodingResult},
};
// use analysis::mir_utils::get_blocked_place;
use itertools::Itertools;
use prusti_common::report::log;
use prusti_interface::environment::{
    borrowck::facts::{AllInputFacts, AllOutputFacts, Loan, PointIndex},
    mir_analyses::{
        allocation::compute_definitely_allocated, initialization::compute_definitely_initialized,
    },
    polonius_info::PoloniusInfo,
    Environment, Procedure,
};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::mir::{BasicBlock, Body, Location, TerminatorKind},
    polonius_engine::{Algorithm, Output},
};
use rustc_borrowck::consumers::{
    LocationTable, RichLocation,
    RichLocation::{Mid, Start},
};
use std::io;

/// Computes the PCS and prints it to the console
/// Currently the entry point for the compiler
pub fn dump_pcs<'env, 'tcx: 'env>(env: &'env Environment<'tcx>) -> EncodingResult<()> {
    for proc_id in env.get_annotated_procedures_and_types().0.iter() {
        println!("id: {:#?}", env.name.get_unique_item_name(*proc_id));
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
    for proc_id in env.get_annotated_procedures_and_types().0.iter() {
        let local_def_id = proc_id.expect_local();
        let _def_path = env.tcx().hir().def_path(local_def_id);
        // This panics all the time and is never called by anything else. Fixable?
        // graphviz(env, &def_path, *proc_id);
        let current_procedure: Procedure<'tcx> = env.get_procedure(*proc_id);
        let mir: &Body<'tcx> = current_procedure.get_mir();

        // There's probably a better way to do this, but local_mir_borrowck_facts
        // doesn't actually populate the output facts.
        let polonius_facts = env.body.local_mir_borrowck_facts(local_def_id);
        let borrowck_in_facts = polonius_facts.input_facts.take().unwrap();
        let borrowck_out_facts = Output::compute(&borrowck_in_facts, Algorithm::Naive, true);
        let location_table = polonius_facts.location_table.take().unwrap();
        let tcx = env.tcx();
        let param_env = tcx.param_env_reveal_all_normalized(*proc_id);
        let move_data = match MoveData::gather_moves(mir, tcx, param_env) {
            Ok((_, move_data)) => move_data,
            Err((move_data, _)) => {
                panic!("no move errors in compiled code")
            }
        };
        let mdpe = MoveDataParamEnv {
            move_data,
            param_env,
        };

        println!("{:#?}", borrowck_in_facts);
        println!("{:#?}", borrowck_out_facts);

        let bctx = BorrowingContext {
            borrowck_in_facts: &borrowck_in_facts,
            borrowck_out_facts: &borrowck_out_facts,
            location_table: &location_table,
            mir: &mir,
            env: &env,
            mdpe,
        };

        //  bctx.compute_cdg_trace();

        log::report_with_writer(
            "scc_trace",
            format!("{}.graph.dot", env.name.get_unique_item_name(*proc_id)),
            |writer| vis_scc_trace(bctx, writer).unwrap(),
        );
    }
    Ok(())
}

#[allow(unused)]
// Computes the reborrowing DAG and outputs a graphviz file with it's trace
pub fn vis_input_facts<'facts, 'env, 'mir: 'env, 'tcx: 'mir>(
    ctx: BorrowingContext<'facts, 'mir, 'env, 'tcx>,
    writer: &mut dyn io::Write,
) -> Result<(), io::Error> {
    todo!();
}

type WriterResult = Result<(), io::Error>;

pub fn vis_scc_trace<'facts, 'env, 'mir: 'env, 'tcx: 'mir>(
    ctx: BorrowingContext<'facts, 'mir, 'env, 'tcx>,
    writer: &mut dyn io::Write,
) -> WriterResult {
    // collect information
    let name = "CFG";
    let happy_cfg = ctx.compute_happy_cfg();

    // nodes

    writeln!(writer, "digraph {name} {{")?;
    writeln!(writer, "rankdir=TB")?;

    // todo: Make these vertically aligned (so the layout isn't borked for larger graphs)
    for bb in happy_cfg.blocks().iter() {
        let block_title = bb_title(&bb);
        let block_cfg = ctx.bb_cfg(bb);
        let points = block_cfg.nodes;
        let block_edges = block_cfg.edges;
        writeln!(writer, "subgraph cluster_block_{block_title} {{")?;
        writeln!(writer, "rankdir=TB;")?;
        writeln!(writer, "title=\"{block_title}\";")?;
        // writeln!(writer, "bgcolor=;")?;

        // Add subgraph corresponding to point, with OCLA relation
        for point in points.iter() {
            let cluster_title = cluster_location(ctx.location_table.to_location(*point));
            let location_label = display_location(ctx.location_table.to_location(*point));
            let point_formatted = escape_graphviz(format!("{:#?}", *point));
            let scc = ctx.loan_scc_at(*point);

            writeln!(writer, "subgraph cluster_{cluster_title} {{")?;
            writeln!(writer, "location_{cluster_title}[style=filled, shape=rectangle, fillcolor=lightgrey, rank=\"same\", label=\"{location_label}\n{point_formatted}\"]")?;

            /*
            let (dag_nodes, dag_edges) = dag_trace.get(point).unwrap();
            for node in dag_nodes.iter() {
                writeln!(
                    writer,
                    "{}_{}",
                    cluster_title,
                    rename_for_labelling(remove_whitespace(format!("{:#?}", node)))
                )?;
            }

            for (nl, nr, ann) in dag_edges.iter() {
                writeln!(
                    writer,
                    "{}_{} -> {}_{}",
                    cluster_title,
                    rename_for_labelling(remove_whitespace(format!("{:#?}", nl))),
                    cluster_title,
                    rename_for_labelling(remove_whitespace(format!("{:#?}", nr)))
                )?;
            }
            */

            // println!(
            //     "{:#?} {}",
            //     point,
            //     escape_graphviz(remove_whitespace(format!(
            //         "{:#?}",
            //         dag_trace.get(point).unwrap()
            //     )))
            // );

            if let Some(scc_v) = scc {
                let scc_nodes = scc_v.0.nodes;
                let scc_edges = scc_v.0.edges;
                for node in scc_nodes.iter() {
                    let scc_label = scc_node_label(node);
                    let scc_title = escape_graphviz(format!("{:#?}", node));
                    writeln!(
                        writer,
                        "{cluster_title}_scc_{scc_label}[fillcolor=lightgrey, label=\"{scc_title}\"]"
                    )?;
                }
                for (e0, e1, _) in scc_edges.iter() {
                    writeln!(
                        writer,
                        "{cluster_title}_scc_{} -> {cluster_title}_scc_{}",
                        scc_node_label(e0),
                        scc_node_label(e1),
                    )?;
                }
            }
            writeln!(writer, "}}")?;
        }

        // Write out the edges between subgraphs
        // todo remove this without destroying my ordering (somehow?????)
        for (p0, p1, label) in block_edges.iter() {
            let p0_title = cluster_location(ctx.location_table.to_location(*p0));
            let p1_title = cluster_location(ctx.location_table.to_location(*p1));
            let edge_weight = if ctx.point_to_mir_block(*p0) == ctx.point_to_mir_block(*p1) {
                1.5
            } else {
                1.0
            };
            writeln!(writer, "location_{p0_title} -> location_{p1_title} [weight={edge_weight}, label=\"{label}\"]")?;
        }

        writeln!(writer, "}}")?;
    }

    // Write out inter-block edges
    for (bb0, bb1) in happy_cfg.edges().iter() {
        let t0 = ctx
            .location_table
            .to_location(ctx.location_table.mid_index(ctx.mir.terminator_loc(*bb0)));
        let t1 = ctx
            .location_table
            .to_location(ctx.location_table.start_index(Location {
                block: *bb1,
                statement_index: 0,
            }));
        let l0 = cluster_location(t0);
        let l1 = cluster_location(t1);
        // let t0 = bb_title(bb0);
        // let t1 = bb_title(bb1);
        writeln!(writer, "location_{l0} -> location_{l1} [weight=0.7]")?;
    }

    writeln!(writer, "}}")
}

// Refactor: The first 4 fields here could be changed to a BodyWithBorrowckFacts
pub struct BorrowingContext<'facts, 'mir, 'env: 'mir, 'tcx: 'env> {
    borrowck_in_facts: &'facts AllInputFacts,
    borrowck_out_facts: &'facts AllOutputFacts,
    location_table: &'facts LocationTable,
    mir: &'mir Body<'tcx>,
    env: &'env Environment<'tcx>,
    mdpe: MoveDataParamEnv<'tcx>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Digraph<N: Clone + Debug + Eq, E: Clone + Debug + Eq> {
    pub nodes: Vec<N>,
    pub edges: Vec<(N, N, E)>,
}

impl<N: Clone + Debug + Eq, E: Clone + Debug + Eq> Default for Digraph<N, E> {
    fn default() -> Self {
        Digraph {
            nodes: vec![],
            edges: vec![],
        }
    }
}

impl<N: Clone + Debug + Eq, E: Clone + Debug + Eq> Digraph<N, E> {
    #[allow(unused)]
    pub fn outgoing_edges(&self, n: N) -> Vec<(N, N, E)> {
        self.edges
            .iter()
            .filter(|(n0, n1, e)| *n0 == n)
            .cloned()
            .collect()
    }

    // Returns all paths, represented as edges, between two nodes
    #[allow(unused)]
    pub fn paths_between(&self, n0: N, n1: &N) -> Vec<Vec<E>> {
        if n0 == *n1 {
            return vec![vec![]];
        }

        let mut ret = vec![];
        for out_edge @ (_, vout, _) in self.outgoing_edges(n0).iter() {
            let rec: Vec<Vec<E>> = self
                .paths_between((*vout).clone(), n1)
                .into_iter()
                .map(|mut v| {
                    v.push((out_edge.2).clone());
                    v
                })
                .collect();
            for r in rec {
                ret.push(r)
            }
        }
        ret
    }
}

// TODO refactor this (and the CFG) to use the other Digraph implementation, which doens't
//  use these janky tuples.
pub struct LoanSCC(pub Digraph<Vec<Loan>, ()>);

impl LoanSCC {
    pub fn new(nodes: Vec<Vec<Loan>>, edges: Vec<(Vec<Loan>, Vec<Loan>, ())>) -> Self {
        Self {
            0: Digraph { nodes, edges },
        }
    }

    // Coarsest possible partition of the loans such that each collection of loans
    //  is finer than the family of nodes.

    // Explanation of the algorithm: maintain the invariant "rr is the
    //      coarsest partition which is finer than all l checked so far"
    //      iteratively checking loans l:
    //      For each rr in r:
    //          if rr is finer than l, that's okay
    //          if rr is coarser than l (rr is not a subset of l)
    //               split rr in two: rr intersect l and rr minus l
    //          re-add the two parts back in.
    // The inner check can be combined into a statement about sets:
    //       Set rr to be the set {rr - l | rr in r} U {rr intersect l | rr in r}
    //  since when rr is finer than l, rr - l is empty and rr intersect l is rr.
    pub fn distinguishing_loans(&self) -> BTreeSet<BTreeSet<Loan>> {
        // Start with the coarsest possible partition (the union of all nodes)
        let mut r: Vec<Vec<Loan>> = vec![self.0.nodes.iter().cloned().flatten().collect()];
        for l in self.0.nodes.iter() {
            let r_int = r.iter().cloned().map(|rr| vec_intersection(rr, &l));
            let r_sub = r.iter().cloned().map(|rr| vec_set_difference(rr, &l));
            r = r_int.chain(r_sub).collect();
        }

        // Remove empty set
        // Change types to something easier to work with (fixme: refactor to other digraph implementation)
        r.into_iter()
            .filter(|p| p.len() > 0)
            .map(|p| p.into_iter().collect())
            .collect()
    }

    #[allow(unused)]
    pub fn all_loans(&self) -> BTreeSet<Loan> {
        self.0.nodes.iter().cloned().flatten().collect()
    }
}

struct CFG(Digraph<BasicBlock, ()>);

impl CFG {
    pub fn new(n: Vec<BasicBlock>, e: Vec<(BasicBlock, BasicBlock)>) -> Self {
        Self {
            0: Digraph {
                nodes: n,
                edges: e
                    .iter()
                    .map(|(b0, b1)| ((*b0).clone(), (*b1).clone(), ()))
                    .collect(),
            },
        }
    }

    pub fn is_node(&self, b: &BasicBlock) -> bool {
        self.0.nodes.contains(b)
    }

    pub fn blocks(&self) -> Vec<BasicBlock> {
        self.0.nodes.clone()
    }

    pub fn edges(&self) -> Vec<(BasicBlock, BasicBlock)> {
        self.0
            .edges
            .iter()
            .map(|(b0, b1, _)| ((*b0).clone(), (*b1).clone()))
            .collect()
    }
}

impl<'facts, 'env, 'mir: 'env, 'tcx: 'env> BorrowingContext<'facts, 'mir, 'env, 'tcx> {
    /// Strongly connected components of the Origin Contains Loan At fact at a point
    pub fn loan_scc_at(&self, loc: PointIndex) -> Option<LoanSCC> {
        let ocla_data = self.borrowck_out_facts.origin_contains_loan_at.get(&loc)?;
        let mut nodes: Vec<Vec<Loan>> = vec![];
        for s in ocla_data.values() {
            let sv: Vec<Loan> = s.iter().cloned().collect();
            nodes.push(sv);
        }
        let mut edges: FxHashSet<(Vec<Loan>, Vec<Loan>, ())> = FxHashSet::default();

        // refactor: nodes.dedup() doesn't work... why? Does it not deeply check vectors?
        let mut nodes_tmp: Vec<Vec<Loan>> = vec![];
        for n in nodes.iter() {
            if !nodes_tmp.contains(n) {
                nodes_tmp.push((*n).clone());
            }
        }
        nodes = nodes_tmp;
        for v in ocla_data.values().combinations(2) {
            let v0 = v[0].iter().cloned().collect::<Vec<Loan>>();
            let v1 = v[1].iter().cloned().collect::<Vec<Loan>>();
            if v0 == v1 {
                continue;
            }
            if v[0].is_subset(v[1]) {
                edges.insert((v0.clone(), v1.clone(), ()));
            } else if v[0].is_superset(v[1]) {
                edges.insert((v1.clone(), v0.clone(), ()));
            }
        }
        Some(LoanSCC::new(nodes, edges.into_iter().collect()))
    }

    fn compute_happy_cfg(&self) -> CFG {
        let mut dirty: Vec<BasicBlock> = vec![BasicBlock::from_usize(0 as usize)];
        let mut nodes: Vec<BasicBlock> = Vec::default();
        let mut edges: Vec<(BasicBlock, BasicBlock)> = Vec::default();
        while let Some(b) = dirty.pop() {
            if nodes.contains(&b) {
                continue;
            }
            nodes.push(b);
            match &(self
                .mir
                .stmt_at(self.mir.terminator_loc(b))
                .right()
                .unwrap()
                .kind)
            {
                TerminatorKind::SwitchInt {
                    targets: ts,
                    ..
                } => {
                    for t in ts.all_targets().iter() {
                        edges.push((b, *t));
                        dirty.push(*t);
                    }
                }
                TerminatorKind::Resume
                | TerminatorKind::Abort
                | TerminatorKind::Return
                | TerminatorKind::Unreachable
                | TerminatorKind::GeneratorDrop => {}
                TerminatorKind::Goto { target: t }
                | TerminatorKind::Drop {
                    place: _,
                    target: t,
                    unwind: _,
                }
                | TerminatorKind::DropAndReplace {
                    place: _,
                    value: _,
                    target: t,
                    unwind: _,
                }
                | TerminatorKind::Assert {
                    cond: _,
                    expected: _,
                    msg: _,
                    target: t,
                    cleanup: _,
                }
                | TerminatorKind::Yield {
                    value: _,
                    resume: t,
                    resume_arg: _,
                    drop: _,
                }
                | TerminatorKind::FalseEdge {
                    real_target: t,
                    imaginary_target: _,
                }
                | TerminatorKind::FalseUnwind {
                    real_target: t,
                    unwind: _,
                }
                | TerminatorKind::Call {
                    func: _,
                    args: _,
                    destination: _,
                    target: Some(t),
                    cleanup: _,
                    from_hir_call: _,
                    fn_span: _,
                } => {
                    edges.push((b, (*t).clone()));
                    dirty.push((*t).clone());
                }
                _ => {
                    todo!();
                }
            }
        }

        return CFG::new(nodes, edges);
    }

    fn compute_cdg_trace(&self) -> FxHashMap<PointIndex, CouplingDigraph<'tcx>> {
        let mut f: FxHashMap<PointIndex, CouplingDigraph<'tcx>> = FxHashMap::default();
        let (pred_map, succ_map) = self.traversal_maps_happy();
        let mut dirty_single: Vec<(PointIndex, CouplingDigraph<'tcx>)> = vec![(
            self.location_table.all_points().next().unwrap(),
            CouplingDigraph::default(),
        )];
        let mut dirty_joins: Vec<PointIndex> = vec![];
        let mut done: Vec<PointIndex> = vec![];

        loop {
            let pt: PointIndex;
            let mut working_cdg: CouplingDigraph<'tcx>;

            if let Some((curr_pt, prev_dag)) = dirty_single.pop() {
                // Update the collection of essential nodes in the tree
                working_cdg = prev_dag.clone();
                pt = curr_pt;
                println!("enter {:?}", pt);

                // Sequential coupling procedure
                self.update_cdg_with_issue(pt, &mut working_cdg);
                let scc = self.loan_scc_at(pt);
                if let Some(scc_v) = &scc {
                    working_cdg.constrain_by_scc(scc_v);
                }
                working_cdg.update_cdg_with_expiries(&scc);
            } else if let Some(r) = dirty_joins.pop() {
                // let preds = pred_map.get(r).unwrap();
                pt = r;
                println!("enter {:?}", pt);
                for p in pred_map.get(&pt).unwrap() {
                    println!("\t[join] {:?}: ", p);
                    match f.get(p) {
                        None => println!("None"),
                        Some(cdg) => cdg.pprint(),
                    }
                }
                println!("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! incorrect join !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
                working_cdg = CouplingDigraph::default();
            } else {
                println!(
                    "end, remaning jobs: {:?} {:?}",
                    dirty_single.len(),
                    dirty_joins.len()
                );
                break;
            };

            // self.strengthen_dag_by_scc(pt, &mut working_dag);

            if let Some(bm) = self.borrow_moves_at_location(&pt) {
                println!("borrow_moves: {:?}", bm);

                // Apply the borrow moves to the LHS of all wands:
                // Note to self: This is slightly a hack because the compiler models borrow creation/moves like this
                //      x = &mut y  => create temporary (issuing) origin for borrow, move that issuing origin into new origin
                //      x = y       => move the origin corresponding to y and kill x
                // whereas we model it like
                //      x = &mut y  => origins issung and assigning origins are the same in the SCC so create one edge
                //      x = y       => modify the edge corresponding to y and kill x
                // I suspect these are no different when using the SCC since we treat origins as sets (so these
                // new origins after a subset are indistinguishable) but if there are issues translating CDG edges
                // to origins this line is probably why.

                // Changing this will involve some backwards reasoning on the types of origins and moves: if I can
                // characterize all origins (issuing origin, assignment origin, etc.) we might consider moving from
                // the SCC model for figuring out which loans are coupled.
                // MARKUS: I'm investigating this, and have asked about it on the Rust Zulip.

                working_cdg.apply_borrow_move(bm.clone(), pt.clone());
            };

            println!(">> finished cdg computation");
            working_cdg.pprint();
            f.insert(pt, working_cdg.clone());
            println!("exit {:?}", pt);
            println!();

            // Add all successors to the dirty lists
            if let Some(nexts) = succ_map.get(&pt) {
                for nxt in nexts.iter() {
                    if !done.contains(nxt) && !dirty_joins.contains(nxt) {
                        let preds_len = pred_map.get(&nxt).unwrap().len();
                        if preds_len == 1 {
                            dirty_single.push((*nxt, working_cdg.clone()));
                        } else {
                            dirty_joins.push(*nxt);
                        }
                    }
                }
            }
            done.push(pt);
        }

        f
    }

    fn location_index_to_location(&self, pt: &PointIndex) -> Location {
        match self.location_table.to_location(*pt) {
            Start(location) => location,
            Mid(location) => location,
        }
    }

    #[allow(unused)]
    fn show_move_path_moves(&self, loc: &PointIndex) -> () {
        let location = self.location_index_to_location(&loc);
        let move_outs = self.mdpe.move_data.loc_map[location]
            .iter()
            .map(|mo_ix| self.mdpe.move_data.moves[*mo_ix])
            .map(|mo| mo.path)
            .map(|mpi| self.mdpe.move_data.move_paths[mpi].place)
            .collect::<Vec<rustc_middle::mir::Place>>();
        if move_outs.len() > 0 {
            print!("move_out: [");
            for p in move_outs.iter() {
                print!("{:?}, ", p);
            }
            println!("]");
        }

        let move_inits = self.mdpe.move_data.init_loc_map[location]
            .iter()
            .map(|mo_ix| self.mdpe.move_data.inits[*mo_ix])
            .map(|mo| mo.path)
            .map(|mpi| self.mdpe.move_data.move_paths[mpi].place)
            .collect::<Vec<rustc_middle::mir::Place>>();

        if move_outs.len() > 0 {
            print!("move_init: [");
            for p in move_inits.iter() {
                print!("{:?}, ", p);
            }
            println!("]");
        }
    }

    // Plan: SCC nodes => subgraphs of the CDG
    //      remember: SCC nodes correspond to origins
    //      So if an origin has two loans in it, then those loans all possibly flowed
    //          into some variable
    //      It is our job to order those loans
    // SCC edges => constraints on the structure of nodes
    //      The LHS of a SCC edge must have a subgraph corresponding to the RHS

    // 1. Figure out which edges belong to which SCC's
    //          All SCC nodes should be in the same (directed) connected component

    // 2. Figure out what the "signature" of each SCC subgraph should be

    // eg. SCC contains {bw0, bw1} and {bw0}
    // - It must be possible to unwind from from a dag with {bw0, bw1} live to one with {bw0} live
    // - DAG contains the structure
    //      [bw1] -(?)-> [bw0]
    // Right now the "dag" looks like
    //      a -bw1-> b  <--repack--> b -bw0-> c
    // So we just select (?) to be the rightwards repacking
    // The DAG then satisfies all SCC contstraints; we are done.

    // Updates cdg with any newly issued loans at a point.
    fn update_cdg_with_issue(&self, loc: PointIndex, cdg: &mut CouplingDigraph<'tcx>) {
        if let Some(loan) = self.loan_issued_at_at(loc) {
            match self.expect_mir_statement(loc).kind {
                Assign(box (to, Ref(_, _, from))) | Assign(box (to, Use(Move(from)))) => {
                    let lhs: BTreeSet<_> = vec![CPlace {
                        place: to,
                        tag: None,
                    }]
                    .iter()
                    .cloned()
                    .collect();
                    let rhs: BTreeSet<_> = vec![CPlace {
                        place: from,
                        tag: None,
                    }]
                    .iter()
                    .cloned()
                    .collect();
                    cdg.new_loan(self.mir, self.env.tcx().clone(), lhs, rhs, loan);
                }
                _ => {
                    panic!("unsupported borrow creation, at {:#?}", loc);
                }
            }
        }
    }

    /// Gets a statement at a point, if we know it is not a terminator
    fn expect_mir_statement(&self, loc: PointIndex) -> Statement<'tcx> {
        self.mir
            .stmt_at(self.point_to_mir_location(loc))
            .left()
            .unwrap()
            .clone()
    }

    /// Reads the content of loan_issued_at at a point
    /// fails if more than one loan is created at a point
    fn loan_issued_at_at(&self, loc: PointIndex) -> Option<Loan> {
        let loans: Vec<_> = self
            .borrowck_in_facts
            .loan_issued_at
            .iter()
            .filter(|(_, _, p)| *p == loc)
            .map(|(_, l, _)| l)
            .cloned()
            .collect();
        if loans.len() == 1 {
            Some(loans[0])
        } else if loans.len() == 0 {
            None
        } else {
            panic!("unsupported multi-loan creations");
        }
    }

    /// Convert a PointIndex into it's basic block
    pub fn point_to_mir_block(&self, loc: PointIndex) -> BasicBlock {
        self.point_to_mir_location(loc).block
    }

    /// Reads underlying MIR location from a point index
    fn point_to_mir_location(&self, loc: PointIndex) -> Location {
        match self.location_table.to_location(loc) {
            Start(l) => l,
            Mid(l) => l,
        }
    }

    // cfg within a single basic block
    fn bb_cfg(&self, b: &BasicBlock) -> Digraph<PointIndex, String> {
        let mut nodes: Vec<PointIndex> = Vec::default();
        let mut edges: Vec<(PointIndex, PointIndex, String)> = Vec::default();
        // refactor: highly stupid way of doing this (I bet this is somehwere else in the compiler... probably even prusti... probably even my code...)
        for loc in self.location_table.all_points().filter(|pt| {
            *b == match self.location_table.to_location(*pt) {
                Start(l) => l,
                Mid(l) => l,
            }
            .block
        }) {
            nodes.push(loc);
        }

        for n in nodes.iter() {
            // switch: internal edge vs inter-stmt edge vs terminator (term is alreayd covered)
            let rich_n = self.location_table.to_location(*n);
            match rich_n {
                Start(l) => {
                    let edge_label: String;
                    if l != self.mir.terminator_loc(*b) {
                        edge_label =
                            escape_graphviz(format!("{:#?}", self.mir.stmt_at(l).left().unwrap()));
                    } else {
                        edge_label = escape_graphviz(
                            abbreviate_terminator(&self.mir.stmt_at(l).right().unwrap().kind)
                                .to_string(),
                        );
                    }
                    edges.push((
                        self.location_table.start_index(l),
                        self.location_table.mid_index(l),
                        edge_label,
                    ));
                }
                Mid(l) => {
                    if l != self.mir.terminator_loc(*b) {
                        edges.push((
                            self.location_table.mid_index(l),
                            self.location_table.start_index(l.successor_within_block()),
                            "".to_string(),
                        ));
                    }
                }
            }
        }
        Digraph { nodes, edges }
    }

    #[allow(unused)]
    /// Constructs predecessor and successor maps from the cfg_edge fact
    fn traversal_maps(
        &self,
    ) -> (
        FxHashMap<PointIndex, FxHashSet<PointIndex>>,
        FxHashMap<PointIndex, FxHashSet<PointIndex>>,
    ) {
        let mut succ: FxHashMap<PointIndex, FxHashSet<PointIndex>> = FxHashMap::default();
        let mut pred: FxHashMap<PointIndex, FxHashSet<PointIndex>> = FxHashMap::default();
        for edge in self.borrowck_in_facts.cfg_edge.iter() {
            let entry_borrow = succ.entry(edge.0).or_insert(FxHashSet::default());
            (*entry_borrow).insert(edge.1.clone());

            let entry_borrow = pred.entry(edge.1).or_insert(FxHashSet::default());
            (*entry_borrow).insert(edge.0.clone());
        }
        (pred, succ)
    }

    /// Traversal maps which ignore unwinding paths
    fn traversal_maps_happy(
        &self,
    ) -> (
        FxHashMap<PointIndex, FxHashSet<PointIndex>>,
        FxHashMap<PointIndex, FxHashSet<PointIndex>>,
    ) {
        let mut succ: FxHashMap<PointIndex, FxHashSet<PointIndex>> = FxHashMap::default();
        let mut pred: FxHashMap<PointIndex, FxHashSet<PointIndex>> = FxHashMap::default();
        let cfg = self.compute_happy_cfg();
        for edge in self.borrowck_in_facts.cfg_edge.iter() {
            if cfg.is_node(&self.point_to_mir_block(edge.0))
                && cfg.is_node(&self.point_to_mir_block(edge.0))
            {
                let entry_borrow = succ.entry(edge.0).or_insert(FxHashSet::default());
                (*entry_borrow).insert(edge.1.clone());

                let entry_borrow = pred.entry(edge.1).or_insert(FxHashSet::default());
                (*entry_borrow).insert(edge.0.clone());
            }
        }
        (pred, succ)
    }

    fn place_is_ref(&self, p: &rustc_middle::mir::Place<'tcx>) -> bool {
        p.ty(&self.mir.local_decls, self.env.tcx()).ty.is_ref()
    }

    fn borrow_moves_at_location(&self, point: &PointIndex) -> Option<BorrowMove<'tcx>> {
        // Detecting borrow moves syntactically right now. Could (should?) be refactored
        // to detect using eg. MovePaths.

        let location = match self.location_table.to_location(*point) {
            Start(location) => location,
            Mid(location) => {
                return None;
            }
        };

        self.mir
            .stmt_at(location)
            .left()
            .and_then(|mir_stmt| match &mir_stmt.kind {
                rustc_middle::mir::StatementKind::Assign(box (
                    assign_to,
                    rustc_middle::mir::Rvalue::Use(rustc_middle::mir::Operand::Move(assign_from)),
                )) => {
                    if self.place_is_ref(assign_to) && self.place_is_ref(assign_from) {
                        Some(BorrowMove {
                            from: (*assign_from).clone(),
                            to: (*assign_to).clone(),
                        })
                    } else {
                        None
                    }
                }
                _ => None,
            })
    }

    pub fn loan_kills_at_location(&self, pt: &PointIndex) -> Vec<Place<'tcx>> {
        let killed_loans = self
            .borrowck_in_facts
            .loan_killed_at
            .iter()
            .filter(|(_, l)| l == pt)
            .map(|(loan, _)| loan);
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct BorrowMove<'tcx> {
    pub from: rustc_middle::mir::Place<'tcx>,
    pub to: rustc_middle::mir::Place<'tcx>,
}

fn prettify_origin(og: rustc_middle::ty::RegionVid) -> String {
    format!("{:?}", og)[3..].to_owned()
}

fn display_location(l: RichLocation) -> String {
    escape_graphviz(format!("{:#?}", l))
        .trim()
        .replace(",", "")
        .replace(" ", "")
        .replace("\n", "")
        .replace("\t", "")
}

fn cluster_location(l: RichLocation) -> String {
    escape_graphviz(remove_whitespace(
        format!("{:#?}", l)
            .trim()
            .replace(",", "_")
            .replace("(", "_")
            .replace(")", "_")
            .replace("[", "_")
            .replace("]", "_"),
    ))
}

fn rename_for_labelling(s: String) -> String {
    s.replace(",", "_")
        .replace("(", "_")
        .replace(")", "_")
        .replace("[", "_")
        .replace("]", "_")
        .replace("{", "_")
        .replace("}", "_")
        .replace("*", "deref")
        .replace(":", "_")
        .replace("<", "_")
        .replace(">", "_")
}

fn scc_node_label(l: &Vec<Loan>) -> String {
    escape_graphviz(remove_whitespace(
        format!("{:#?}", l)
            .trim()
            .replace(",", "_")
            .replace("(", "_")
            .replace(")", "_")
            .replace("[", "_")
            .replace("]", "_")
            .replace("{", "_")
            .replace("}", "_"),
    ))
}

fn remove_whitespace(a: String) -> String {
    a.replace("\t", "").replace(" ", "").replace("\n", "")
}

fn escape_graphviz(a: String) -> String {
    a.replace("\"", "\\\"")
        .replace("[", "\\[")
        .replace("]", "\\]")
        .replace("{", "\\{")
        .replace("}", "\\}")
        .replace("<", "\\<")
        .replace(">", "\\>")
        .replace("-", "\\-")
        .replace("\t", "")
        .replace(" ", "")
        .replace("\n", "")
}

fn bb_title(b: &BasicBlock) -> String {
    escape_graphviz(remove_whitespace(
        format!("{:#?}", b)
            .trim()
            .replace(",", "_")
            .replace("(", "_")
            .replace(")", "_")
            .replace("[", "_")
            .replace("]", "_")
            .replace("{", "_")
            .replace("}", "_"),
    ))
}

pub fn debug_print_scc(s: &LoanSCC) {
    for n in s.0.nodes.iter() {
        print!("{:?} ", n);
    }
    println!();
    for (e1, e2, ann) in s.0.edges.iter() {
        println!(
            "\t{:#?}\t{} -> {}",
            ann,
            format!("{:#?}", e1).replace("\n", " ").replace("\t", " "),
            format!("{:#?}", e2).replace("\n", " ").replace("\t", " ")
        );
    }
}

fn vec_subset<T: Eq>(v1: &Vec<T>, v2: &Vec<T>) -> bool {
    v1.iter().all(|v| v2.contains(v))
}

fn vec_set_eq<T: Eq>(v1: &Vec<T>, v2: &Vec<T>) -> bool {
    vec_subset(v1, v2) && vec_subset(v2, v1)
}

fn vec_set_difference<T: Eq + Clone>(v: Vec<T>, subtrahend: &Vec<T>) -> Vec<T> {
    v.iter()
        .filter(|vv| !subtrahend.contains(vv))
        .cloned()
        .collect()
}

fn vec_intersection<T: Eq>(v1: Vec<T>, v2: &Vec<T>) -> Vec<T> {
    v1.into_iter().filter(|vv| v2.contains(vv)).collect()
}
