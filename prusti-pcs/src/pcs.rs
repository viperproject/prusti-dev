// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![allow(unused_imports)]
use prusti_rustc_interface::middle::mir::{
    Operand::Move,
    Rvalue::{Ref, Use},
    StatementKind::Assign,
};
use rustc_data_structures::sync::Atomic;
use rustc_middle::mir::Statement;
use std::{default::Default, fmt::Debug, hash::Hash};

use crate::{
    pcs::DagAnnotations::Borrow,
    pcs_analysis::conditional::CondPCSctx,
    syntax::MicroMirEncoder,
    util::{abbreviate_terminator, EncodingResult},
};
use analysis::mir_utils::get_blocked_place;
use itertools::Itertools;
use prusti_common::report::log;
use prusti_interface::{
    environment::{
        borrowck::facts::{
            AllInputFacts, AllOutputFacts, BorrowckFacts, Loan, Point, PointIndex, PointType,
        },
        mir_analyses::{
            allocation::{compute_definitely_allocated, DefinitelyAllocatedAnalysisResult},
            initialization::{compute_definitely_initialized, DefinitelyInitializedAnalysisResult},
        },
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
    polonius_engine::{Algorithm, Output},
};
use rustc_borrowck::consumers::{
    LocationTable, RichLocation,
    RichLocation::{Mid, Start},
};
use std::{
    cell::RefCell,
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

        // There's probably a better way to do this, but local_mir_borrowck_facts
        // doesn't actually populate the output facts.
        let mut polonius_facts = env.local_mir_borrowck_facts(local_def_id);
        let borrowck_in_facts = polonius_facts.input_facts.take().unwrap();
        let borrowck_out_facts = Output::compute(&borrowck_in_facts, Algorithm::Naive, true);
        let location_table = polonius_facts.location_table.take().unwrap();
        let bctx = BorrowingContext {
            borrowck_in_facts: &borrowck_in_facts,
            borrowck_out_facts: &borrowck_out_facts,
            location_table: &location_table,
            mir: &mir,
        };

        log::report_with_writer(
            "scc_trace",
            format!("{}.graph.dot", env.get_unique_item_name(*proc_id)),
            |writer| vis_scc_trace(bctx, writer).unwrap(),
        );
    }
    Ok(())
}

// Computes the reborrowing DAG and outputs a graphviz file with it's trace
pub fn vis_input_facts<'facts, 'mir, 'tcx: 'mir>(
    ctx: BorrowingContext<'facts, 'mir, 'tcx>,
    writer: &mut dyn io::Write,
) -> Result<(), io::Error> {
    todo!();
}

type WriterResult = Result<(), io::Error>;

pub fn vis_scc_trace<'facts, 'mir, 'tcx: 'mir>(
    ctx: BorrowingContext<'facts, 'mir, 'tcx>,
    writer: &mut dyn io::Write,
) -> WriterResult {
    // collect information
    let name = "CFG";
    // TODO: PUT THIS BACK IN
    // let dag_trace = ctx.compute_dag_trace();
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
pub struct BorrowingContext<'facts, 'mir, 'tcx: 'mir> {
    borrowck_in_facts: &'facts AllInputFacts,
    borrowck_out_facts: &'facts AllOutputFacts,
    location_table: &'facts LocationTable,
    mir: &'mir Body<'tcx>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DagAnnotations {
    Borrow(Loan),
    Repack,
}

// Flaw in trait system: this has to also have clone + debug + eq types
#[derive(Clone, Debug, PartialEq, Eq)]
struct Digraph<N: Clone + Debug + Eq, E: Clone + Debug + Eq> {
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
    pub fn outgoing_edges(&self, n: N) -> Vec<(N, N, E)> {
        self.edges
            .iter()
            .filter(|(n0, n1, e)| *n0 == n)
            .cloned()
            .collect()
    }

    // Returns all paths, represented as edges, between two nodes
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

#[derive(Clone, Debug, PartialEq, Eq)]
struct AtomicDigraph<N: Clone + Debug + Eq, E: Clone + Debug + Eq> {
    graph: Digraph<usize, usize>,
    node_map: FxHashMap<usize, N>,
    edge_map: FxHashMap<usize, E>,
    last_sym: usize,
}

impl<N: Clone + Debug + Eq, E: Clone + Debug + Eq> Default for AtomicDigraph<N, E> {
    fn default() -> Self {
        AtomicDigraph {
            graph: Digraph::default(),
            node_map: FxHashMap::default(),
            edge_map: FxHashMap::default(),
            last_sym: 0,
        }
    }
}

impl<N: Clone + Debug + Eq, E: Clone + Debug + Eq> AtomicDigraph<N, E> {
    fn gensym(&mut self) -> usize {
        self.last_sym += 1;
        self.last_sym
    }

    pub fn mapped_edges(&self) -> Vec<(N, N, E)> {
        self.graph
            .edges
            .iter()
            .map(|(n1, n2, e)| {
                (
                    (*self.node_map.get(n1).unwrap()).clone(),
                    (*self.node_map.get(n2).unwrap()).clone(),
                    (*self.edge_map.get(e).unwrap()).clone(),
                )
            })
            .collect()
    }

    pub fn mapped_nodes(&self) -> Vec<(N)> {
        self.graph
            .nodes
            .iter()
            .map(|n| (*self.node_map.get(n).unwrap()).clone())
            .collect()
    }

    // Returns the index of a node, if it exists
    fn node_index(&self, n: &N) -> Option<usize> {
        let matching_nodes = self
            .node_map
            .iter()
            .filter(|(k, v)| *v == n)
            .map(|(k, _)| k)
            .cloned()
            .collect::<Vec<usize>>();
        if matching_nodes.len() == 1 {
            Some(matching_nodes[0])
        } else if matching_nodes.len() == 0 {
            None
        } else {
            panic!("Atomic graph invalid state: values are not unique");
        }
    }

    // Returns the index of a node, if it exists
    fn edge_index(&self, e: &E) -> Option<usize> {
        let matching_edges = self
            .edge_map
            .iter()
            .filter(|(k, v)| *v == e)
            .map(|(k, _)| k)
            .cloned()
            .collect::<Vec<usize>>();
        if matching_edges.len() == 1 {
            Some(matching_edges[0])
        } else if matching_edges.len() == 0 {
            None
        } else {
            panic!("Atomic graph invalid state: edges are not unique");
        }
    }

    // Adds a node, if it doesn't exist
    // Return its index
    pub fn include_node(&mut self, n: N) -> usize {
        match self.node_index(&n) {
            None => {
                let node_sym = self.gensym();
                self.graph.nodes.push(node_sym);
                self.node_map.insert(node_sym, n);
                node_sym
            }
            Some(sym) => sym,
        }
    }

    // Adds an edge, adding extra nodes if they don't exist
    pub fn include_edge(&mut self, v: (N, N, E)) {
        if let Some(_) = self.edge_index(&v.2) {
            let edge_sym = self.gensym();
            self.edge_map.insert(edge_sym, v.2.clone());
            let n0 = self.include_node(v.0);
            let n1 = self.include_node(v.1);
            self.graph.edges.push((n0, n1, edge_sym));
        }
    }

    // partitions nodes by a function
    pub fn quotient_nodes<F, Z: Eq + Hash>(&self, f: F) -> FxHashMap<Z, FxHashSet<usize>>
    where
        F: Fn(&N) -> Z,
    {
        let mut r = FxHashMap::default();

        for n in self.graph.nodes.iter() {
            let res_z = f(&self.node_map.get(n).unwrap());
            let entry_borrow = r.entry(res_z).or_insert(FxHashSet::default());
            (*entry_borrow).insert((*n).clone());
        }

        r
    }
}

struct LoanSCC(Digraph<Vec<Loan>, ()>);

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReborrowingDag<'tcx>(AtomicDigraph<FxHashSet<Place<'tcx>>, DagAnnotations>);
struct CFG(Digraph<BasicBlock, ()>);

impl DagAnnotations {
    pub fn underlying_loan(&self) -> Option<Loan> {
        match self {
            Borrow(l) => Some((*l).clone()),
            Repack => None,
        }
    }
}

impl<'tcx> ReborrowingDag<'tcx> {
    pub fn new(
        n: Vec<FxHashSet<Place<'tcx>>>,
        e: Vec<(
            FxHashSet<Place<'tcx>>,
            FxHashSet<Place<'tcx>>,
            DagAnnotations,
        )>,
    ) -> Self {
        let mut g: AtomicDigraph<FxHashSet<Place<'tcx>>, DagAnnotations> = AtomicDigraph::default();
        for nn in n.into_iter() {
            g.include_node(nn);
        }
        for ee in e.iter() {
            g.include_edge((*ee).clone());
        }
        Self { 0: g }
    }

    pub fn loans(&self) -> Vec<Loan> {
        self.0
            .mapped_edges()
            .iter()
            .filter_map(|(_, _, a)| a.underlying_loan())
            .collect()
    }

    pub fn push_loan(
        &mut self,
        lhs: FxHashSet<Place<'tcx>>,
        rhs: FxHashSet<Place<'tcx>>,
        loan: Loan,
    ) {
        self.0.include_node(lhs.clone());
        self.0.include_node(rhs.clone());
        self.0.include_edge((lhs, rhs, Borrow(loan)));
    }
}

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

impl LoanSCC {
    pub fn new(n: Vec<Vec<Loan>>, e: Vec<(Vec<Loan>, Vec<Loan>)>) -> Self {
        Self {
            0: Digraph {
                nodes: n,
                edges: e
                    .iter()
                    .map(|(l0, l1)| ((*l0).clone(), (*l1).clone(), ()))
                    .collect(),
            },
        }
    }
}

impl<'facts, 'mir, 'tcx: 'mir> BorrowingContext<'facts, 'mir, 'tcx> {
    /// Strongly connected components of the Origin Contains Loan At fact at a point
    pub fn loan_scc_at(&self, loc: PointIndex) -> Option<LoanSCC> {
        let ocla_data = self.borrowck_out_facts.origin_contains_loan_at.get(&loc)?;
        let mut nodes: Vec<Vec<Loan>> = vec![];
        for s in ocla_data.values() {
            let sv: Vec<Loan> = s.iter().cloned().collect();
            nodes.push(sv);
        }
        let mut edges: FxHashSet<(Vec<Loan>, Vec<Loan>)> = FxHashSet::default();

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
                edges.insert((v0.clone(), v1.clone()));
            } else if v[0].is_superset(v[1]) {
                edges.insert((v1.clone(), v0.clone()));
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
                    discr: _,
                    switch_ty: _,
                    targets: ts,
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

    // Detect when two SCC's differ by exactly one new loan, and return it if so
    fn scc_differ_by_loan_issue(
        &self,
        oscc1: &Option<LoanSCC>,
        oscc2: &Option<LoanSCC>,
    ) -> Option<Vec<Loan>> {
        match (oscc1, oscc2) {
            (_, None) => None,
            (None, Some(ssc)) => {
                let v = (*ssc.0.nodes).iter().cloned().collect::<Vec<_>>();
                let e = (*ssc.0.edges).iter().cloned().collect::<Vec<_>>();
                if v.iter().all(|vv| vv.len() == 1) && e.len() == 0 {
                    Some(v.iter().map(|x| x[0]).collect())
                } else {
                    None
                }
            }
            (Some(ssc1), Some(ssc2)) => {
                let v1 = ssc1.0.nodes.iter().cloned().collect::<Vec<_>>();
                let v2 = ssc2.0.nodes.iter().cloned().collect::<Vec<_>>();
                // TODO: There's no self edges in the SCC... right?
                let diff = vec_set_difference(v1.concat(), &v2.concat());
                if diff.len() == 1 {
                    Some(diff)
                } else {
                    None
                }

                // if vec_set_eq(&e1, &e2) {
                //     // Vetices are vectors of loans
                //     let diff = vec_set_difference((*v2).clone(), v1);
                //     if diff.iter().all(|s| s.len() == 1) {
                //         Some(diff.iter().map(|x| x[0]).collect())
                //     } else {
                //         None
                //     }
                // } else {
                //     None
                // }
            }
        }
    }

    fn compute_dag_trace(&self) -> FxHashMap<PointIndex, ReborrowingDag<'tcx>> {
        let mut f: FxHashMap<PointIndex, ReborrowingDag<'tcx>> = FxHashMap::default();
        let (pred_map, succ_map) = self.traversal_maps();
        let mut dirty_single: Vec<(PointIndex, ReborrowingDag)> = vec![(
            self.location_table.all_points().next().unwrap(),
            ReborrowingDag::new(vec![], vec![]),
        )];
        let mut dirty_joins: Vec<PointIndex> = vec![];
        let mut done: Vec<PointIndex> = vec![];

        loop {
            let mut pt: PointIndex;
            let mut working_dag: ReborrowingDag;

            if let Some((curr_pt, prev_dag)) = dirty_single.pop() {
                // Update the collection of essential nodes in the tree
                working_dag = prev_dag.clone();
                pt = curr_pt;

                if let Some(new_loan) = self.loan_issued_at_at(curr_pt) {
                    self.update_dag_with_issue(curr_pt, &mut working_dag);
                }

                // Check for kills and invalidations

                // if let Some(scc) = self.loan_scc_at(curr_pt) {
                //     println!("---- {:#?}", curr_pt);
                //     print!("scc ");
                //     debug_print_scc(&scc);
                //     print!("old ");
                //     debug_print_dag(&prev_dag);
                //     let pred_pt = pred_map.get(&curr_pt).unwrap().iter().next().unwrap();
                //     let pred_scc = self.loan_scc_at(*pred_pt);
                //     let singleton_diff =
                //         self.scc_differ_by_loan_issue(&pred_scc, &Some(scc.clone()));
                //     print!("difference ");
                //     if let Some(vd) = &singleton_diff {
                //         for v in vd.iter() {
                //             print!("{:?} ", v);
                //         }
                //     }
                //     println!();

                //     if Some(scc.clone()) == pred_scc {
                //         // (1) If the scc is the same, do not update
                //         pt = curr_pt;
                //         working_dag = prev_dag;
                //     } else if let Some(new_loans) = singleton_diff {
                //         if new_loans.len() == 1 {
                //             // One new loan issued, add it to the reborrowing DAG
                //             working_dag = prev_dag.clone();
                //             self.update_dag_with_issue(
                //                 curr_pt.clone(),
                //                 &mut working_dag,
                //                 new_loans[0],
                //             );
                //             print!("new dag: ");
                //             debug_print_dag(&working_dag);
                //             pt = curr_pt;
                //         } else {
                //             // More than one new loan issued, or zero new loans issued (somehow)
                //             panic!();
                //         }
                //     } else {
                //         println!("UNHANDLED CASE:");
                //         panic!();
                //     }
                //     // If
                //     //  - we're at an odd location
                //     //  - a singleton scc node is introduced
                //     //  - the previous statement issued the loan in the singleton
                //     // Then we add a new edge to the reborrowing DAG
                // } else {
                //     // If no SCC, the reborrowing DAG is read to be empty
                //     pt = curr_pt;
                //     working_dag = (vec![], vec![]);
                // }
            } else if let Some(r) = dirty_joins.pop() {
                // let preds = pred_map.get(r).unwrap();
                todo!("construct a working_dag from the join");
                pt = r;
                working_dag = todo!();
            } else {
                todo!("unhandled");
                break;
            };

            // We should have a weaker version of the DAG at this point... possible missing some edges
            // and possibly missing some coupling.

            print!("pre-calculation dag: ");
            debug_print_dag(&working_dag);

            self.strengthen_dag_by_scc(pt, &mut working_dag);

            println!("done {:#?}", pt);

            // Add f to the map and continue
            f.insert(pt, working_dag.clone());

            // Add all successors to the dirty lists
            if let Some(nexts) = succ_map.get(&pt) {
                for nxt in nexts.iter() {
                    if !done.contains(nxt) {
                        let preds_len = pred_map.get(&nxt).unwrap().len();
                        if preds_len == 1 {
                            dirty_single.push((*nxt, working_dag.clone()));
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

    fn strengthen_dag_by_scc(&self, pt: PointIndex, dag: &mut ReborrowingDag<'tcx>) {
        let scc = self.loan_scc_at(pt);
        if let Some(scc_v) = scc {
            print!("scc: ");
            debug_print_scc(&scc_v);

            // for scc_node in scc_v.0.nodes.iter() {
            //     // self.add_implicit_edges(dag, scc_node);
            // }
            // Plan: SCC nodes => subgraphs of the DAG
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
        }
    }

    // Compute the minimal (directed) subgraph of the dag containg all nodes in scc_n
    fn get_subgraph_from_loans(&self, dag: &mut ReborrowingDag, scc_n: &Vec<Loan>) {
        // There's defeinitely a better way to find this
        let mut working_dag = (*dag).clone();
        todo!();
    }

    // Figure out all possible repack edges between nodes
    fn add_implicit_edges(&self, dag: &mut ReborrowingDag) {
        // Nodes are sets of places.
        // "Hyperedges" can be represented as one edge (UNPACK p) --REPACK--> {p}
        // and several edges A --incl--> B (where A is a subset of B)
        // A hyperedge is then a family of incl/repack edges where the disjoint union of the RHS's
        //  of the incl edges exactly meet the LHS of the REPACK edge.

        // For now, we're going to ignore this construction and pretend everything unpacks to exactly
        // one place (which it does in the list walk example)

        // 1. For every place that occurs in some node, compute the unpacking of that place.
        //      If that unpacking is the RHS of any node in the graph,
        //          add a repack edge between the two.
        todo!();
    }

    // Updates dag with newly issued loans
    fn update_dag_with_issue(&self, loc: PointIndex, dag: &mut ReborrowingDag<'tcx>) {
        if let Some(loan) = self.loan_issued_at_at(loc) {
            match self.expect_mir_statement(loc).kind {
                Assign(box (to, Ref(_, _, from))) | Assign(box (to, Use(Move(from)))) => {
                    let lhs: FxHashSet<_> = vec![to].iter().cloned().collect();
                    let rhs: FxHashSet<_> = vec![from].iter().cloned().collect();
                    dag.push_loan(lhs, rhs, loan);
                }
                _ => {
                    panic!("unsupported borrow creation");
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

fn debug_print_dag(d: &ReborrowingDag) {
    for n in d.0.mapped_nodes().iter() {
        print!("{:?} ", n);
    }
    println!();
    for (lhs, rhs, ann) in d.0.mapped_edges().iter() {
        for l in lhs.iter() {
            print!("{:?} ", l);
        }
        print!("-> ");
        for r in rhs.iter() {
            print!("{:?} ", r);
        }
        debug_print_annotation(&ann);
        println!();
    }
}

fn debug_print_annotation(ann: &DagAnnotations) {
    match ann {
        Borrow(l) => {
            print!("borrow {:?}", l)
        }
        DagAnnotations::Repack => print!("repack"),
    }
}

fn debug_print_scc(s: &LoanSCC) {
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
