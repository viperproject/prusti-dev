// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::borrowck::{facts, regions};
use super::loops;
use super::loops_utils::*;
use super::mir_analyses::initialization::{
    compute_definitely_initialized,
    DefinitelyInitializedAnalysisResult
};
use crate::utils;
use datafrog::{Iteration, Relation};
use std::cell;
use std::env;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{self, Write, BufWriter};
use std::path::PathBuf;
use polonius_engine::{Algorithm, Output, Atom};
use rustc::hir::{self, intravisit};
use rustc::mir;
use rustc::ty::TyCtxt;
use rustc_data_structures::indexed_vec::Idx;
use syntax::ast;
use syntax::codemap::Span;

pub fn dump_borrowck_info<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>) {
    trace!("[dump_borrowck_info] enter");

    assert!(tcx.use_mir_borrowck(), "NLL is not enabled.");

    let mut printer = InfoPrinter {
        tcx: tcx,
    };
    intravisit::walk_crate(&mut printer, tcx.hir.krate());

    trace!("[dump_borrowck_info] exit");
}

struct InfoPrinter<'a, 'tcx: 'a> {
    pub tcx: TyCtxt<'a, 'tcx, 'tcx>,
}

impl<'a, 'tcx> intravisit::Visitor<'tcx> for InfoPrinter<'a, 'tcx> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'tcx> {
        let map = &self.tcx.hir;
        intravisit::NestedVisitorMap::All(map)
    }

    fn visit_fn(&mut self, fk: intravisit::FnKind<'tcx>, _fd: &'tcx hir::FnDecl,
                _b: hir::BodyId, _s: Span, node_id: ast::NodeId) {
        let name = match fk {
            intravisit::FnKind::ItemFn(name, ..) => name,
            _ => return,
        };

        trace!("[visit_fn] enter name={:?}", name);

        match env::var_os("PRUSTI_DUMP_PROC").and_then(|value| value.into_string().ok()) {
            Some(value) => {
                if name != value {
                    return;
                }
            },
            _ => {},
        };

        let def_id = self.tcx.hir.local_def_id(node_id);
        self.tcx.mir_borrowck(def_id);

        // Read Polonius facts.
        let def_path = self.tcx.hir.def_path(def_id);
        let dir_path = PathBuf::from("nll-facts").join(def_path.to_filename_friendly_no_crate());
        debug!("Reading facts from: {:?}", dir_path);
        let mut facts_loader = facts::FactLoader::new();
        facts_loader.load_all_facts(&dir_path);

        // Read relations between region IDs and local variables.
        let renumber_path = PathBuf::from(format!(
            "log/mir/rustc.{}.-------.renumber.0.mir",
            def_path.to_filename_friendly_no_crate()));
        debug!("Renumber path: {:?}", renumber_path);
        let variable_regions = regions::load_variable_regions(&renumber_path).unwrap();

        let mir = self.tcx.mir_validated(def_id).borrow();

        let mut call_magic_wands = HashMap::new();

        let mut all_facts = facts_loader.facts;
        {
            // TODO: Refactor.
            // The code that adds a creation of a new borrow for each
            // move of a borrow.

            // Find the last loan index.
            let mut last_loan_id = 0;
            for (_, loan, _) in all_facts.borrow_region.iter() {
                if loan.index() > last_loan_id {
                    last_loan_id = loan.index();
                }
            }
            last_loan_id += 1;

            // Create a map from points to (region1, region2) vectors.
            let universal_region = &all_facts.universal_region;
            let mut outlives_at_point = HashMap::new();
            for (region1, region2, point) in all_facts.outlives.iter() {
                if !universal_region.contains(region1) && !universal_region.contains(region2) {
                    let outlives = outlives_at_point.entry(point).or_insert(vec![]);
                    outlives.push((region1, region2));
                }
            }

            // Create new borrow_region facts for points where is only one outlives
            // fact and there is not a borrow_region fact already.
            let borrow_region = &mut all_facts.borrow_region;
            for (point, mut regions) in outlives_at_point {
                if borrow_region.iter().all(|(_, _, loan_point)| loan_point != point) {
                    if regions.len() > 1 {
                        let location = facts_loader.interner.get_point(*point).location.clone();
                        for &(region1, region2) in regions.iter() {
                            debug!("{:?} {:?} {:?}", location, region1, region2);
                        }
                        let call_destination = self.get_call_destination(&mir, location);
                        if let Some(place) = call_destination {
                            match place {
                                mir::Place::Local(local) => {
                                    let var_region = variable_regions.get(&local);
                                    debug!("var_region = {:?}", var_region);
                                    let loan = facts::Loan::from(last_loan_id);
                                    borrow_region.push(
                                        (*var_region.unwrap(),
                                        loan,
                                        *point));
                                    last_loan_id += 1;
                                    call_magic_wands.insert(loan, local);
                                }
                                x => unimplemented!("{:?}", x)
                            }
                        }
                    } else {
                        let (_region1, region2) = regions.pop().unwrap();
                        borrow_region.push((*region2, facts::Loan::from(last_loan_id), *point));
                        last_loan_id += 1;
                    }
                }
            }
        }

        let polonius_dump_enabled = true;
        let output = Output::compute(&all_facts, Algorithm::Naive, polonius_dump_enabled);
        let additional_facts = compute_additional_facts(&all_facts, &output);

        let loop_info = loops::ProcedureLoops::new(&mir);

        let graph_path = PathBuf::from("nll-facts")
            .join(def_path.to_filename_friendly_no_crate())
            .join("graph.dot");
        let graph_file = File::create(graph_path).expect("Unable to create file");
        let graph = BufWriter::new(graph_file);

        let interner = facts_loader.interner;
        let loan_position = all_facts.borrow_region
            .iter()
            .map(|&(_, loan, point_index)| {
                let point = interner.get_point(point_index);
                (loan, point.location)
            })
            .collect();

        let initialization = compute_definitely_initialized(&mir, self.tcx, def_path);

        let mut mir_info_printer = MirInfoPrinter {
            tcx: self.tcx,
            mir: mir,
            borrowck_in_facts: all_facts,
            borrowck_out_facts: output,
            additional_facts: additional_facts,
            interner: interner,
            graph: cell::RefCell::new(graph),
            loops: loop_info,
            variable_regions: variable_regions,
            loan_position: loan_position,
            initialization: initialization,
            call_magic_wands: call_magic_wands,
        };
        mir_info_printer.print_info();

        trace!("[visit_fn] exit");
    }
}


impl<'a, 'tcx> InfoPrinter<'a, 'tcx> {

    /// Extract the call terminator at the location. Otherwise return None.
    fn get_call_destination(&self, mir: &mir::Mir<'tcx>,
                            location: mir::Location) -> Option<mir::Place<'tcx>> {
        let mir::BasicBlockData { ref statements, ref terminator, .. } = mir[location.block];
        if statements.len() != location.statement_index {
            return None;
        }
        match terminator.as_ref().unwrap().kind {
            mir::TerminatorKind::Call { ref destination, .. } => {
                if let Some((ref place, _)) = destination {
                    Some(place.clone())
                } else {
                    None
                }
            }
            ref x => {
                panic!("Expected call, got {:?} at {:?}", x, location);
            }
        }
    }

}


/// Additional facts derived from the borrow checker facts.
struct AdditionalFacts {
    /// A list of loans sorted by id.
    pub loans: Vec<facts::Loan>,
    /// The ``reborrows`` facts are needed for removing “fake” loans: at
    /// a specific program point there are often more than one loan active,
    /// but we are interested in only one of them, which is the original one.
    /// Therefore, we find all loans that are reborrows of the original loan
    /// and remove them. Reborrowing is defined as follows:
    ///
    /// ```datalog
    /// reborrows(Loan, Loan);
    /// reborrows(L1, L2) :-
    ///     borrow_region(R, L1, P),
    ///     restricts(R, P, L2).
    /// reborrows(L1, L3) :-
    ///     reborrows(L1, L2),
    ///     reborrows(L2, L3).
    /// ```
    pub reborrows: Vec<(facts::Loan, facts::Loan)>,
    /// Non-transitive `reborrows`.
    pub reborrows_direct: Vec<(facts::Loan, facts::Loan)>,
}

/// Derive additional facts from the borrow checker facts.
fn compute_additional_facts(all_facts: &facts::AllInputFacts,
                            output: &facts::AllOutputFacts) -> AdditionalFacts {

    use self::facts::{PointIndex as Point, Loan, Region};

    let mut iteration = Iteration::new();

    // Variables that are outputs of our computation.
    let reborrows = iteration.variable::<(Loan, Loan)>("reborrows");

    // Variables for initial data.
    let restricts = iteration.variable::<((Point, Region), Loan)>("restricts");
    let borrow_region = iteration.variable::<((Point, Region), Loan)>("borrow_region");

    // Load initial data.
    restricts.insert(Relation::from(
        output.restricts.iter().flat_map(
            |(&point, region_map)|
            region_map.iter().flat_map(
                move |(&region, loans)|
                loans.iter().map(move |&loan| ((point, region), loan))
            )
        )
    ));
    borrow_region.insert(Relation::from(
        all_facts.borrow_region.iter().map(|&(r, l, p)| ((p, r), l))
    ));

    // Temporaries for performing join.
    let reborrows_1 = iteration.variable_indistinct("reborrows_1");
    let reborrows_2 = iteration.variable_indistinct("reborrows_2");

    while iteration.changed() {

        // reborrows(L1, L2) :-
        //   borrow_region(R, L1, P),
        //   restricts(R, P, L2).
        reborrows.from_join(&borrow_region, &restricts, |_, &l1, &l2| (l1, l2));

        // Compute transitive closure of reborrows:
        // reborrows(L1, L3) :-
        //   reborrows(L1, L2),
        //   reborrows(L2, L3).
        reborrows_1.from_map(&reborrows, |&(l1, l2)| (l2, l1));
        reborrows_2.from_map(&reborrows, |&(l2, l3)| (l2, l3));
        reborrows.from_join(&reborrows_1, &reborrows_2, |_, &l1, &l3| (l1, l3));
    }

    // Remove reflexive edges.
    let reborrows: Vec<_> = reborrows
        .complete()
        .iter()
        .filter(|(l1, l2)| l1 != l2)
        .cloned()
        .collect();
    // A non-transitive version of reborrows.
    let mut reborrows_direct = Vec::new();
    for &(l1, l2) in reborrows.iter() {
        let is_l2_minimal = !reborrows
            .iter()
            .any(|&(l3, l4)| {
                l4 == l2 && reborrows.contains(&(l1, l3))
            });
        if is_l2_minimal {
            reborrows_direct.push((l1, l2));
        }
    }
    // Compute the sorted list of all loans.
    let mut loans: Vec<_> = all_facts
        .borrow_region
        .iter()
        .map(|&(_, l, _)| l)
        .collect();
    loans.sort();
    AdditionalFacts {
        loans: loans,
        reborrows: reborrows,
        reborrows_direct: reborrows_direct,
    }
}


struct MirInfoPrinter<'a, 'tcx: 'a> {
    pub tcx: TyCtxt<'a, 'tcx, 'tcx>,
    pub mir: cell::Ref<'a, mir::Mir<'tcx>>,
    pub borrowck_in_facts: facts::AllInputFacts,
    pub borrowck_out_facts: facts::AllOutputFacts,
    pub additional_facts: AdditionalFacts,
    pub interner: facts::Interner,
    pub graph: cell::RefCell<BufWriter<File>>,
    pub loops: loops::ProcedureLoops,
    pub variable_regions: HashMap<mir::Local, facts::Region>,
    /// Position at which a specific loan was created.
    pub loan_position: HashMap<facts::Loan, mir::Location>,
    pub initialization: DefinitelyInitializedAnalysisResult<'tcx>,
    pub call_magic_wands: HashMap<facts::Loan, mir::Local>,
}

macro_rules! write_graph {
    ( $self:ident, $( $x:expr ),* ) => {
        writeln!($self.graph.borrow_mut(), $( $x ),*)?;
    }
}

macro_rules! to_html {
    ( $o:expr ) => {{
        format!("{:?}", $o)
            .replace("{", "\\{")
            .replace("}", "\\}")
            .replace("&", "&amp;")
            .replace(">", "&gt;")
            .replace("<", "&lt;")
            .replace("\n", "<br/>")
    }};
}

macro_rules! to_html_display {
    ( $o:expr ) => {{
        format!("{}", $o)
            .replace("{", "\\{")
            .replace("}", "\\}")
            .replace("&", "&amp;")
            .replace(">", "&gt;")
            .replace("<", "&lt;")
            .replace("\n", "<br/>")
    }};
}

macro_rules! write_edge {
    ( $self:ident, $source:ident, str $target:ident ) => {{
        write_graph!($self, "\"{:?}\" -> \"{}\"\n", $source, stringify!($target));
    }};
    ( $self:ident, $source:ident, unwind $target:ident ) => {{
        write_graph!($self, "\"{:?}\" -> \"{:?}\" [color=red]\n", $source, $target);
    }};
    ( $self:ident, $source:ident, imaginary $target:ident ) => {{
        write_graph!($self, "\"{:?}\" -> \"{:?}\" [style=\"dashed\"]\n", $source, $target);
    }};
    ( $self:ident, $source:ident, $target:ident ) => {{
        write_graph!($self, "\"{:?}\" -> \"{:?}\"\n", $source, $target);
    }};
}

macro_rules! to_sorted_string {
    ( $o:expr ) => {{
        let mut vector = $o.iter().map(|x| to_html!(x)).collect::<Vec<String>>();
        vector.sort();
        vector.join(", ")
    }}
}


impl<'a, 'tcx> MirInfoPrinter<'a, 'tcx> {

    pub fn print_info(&mut self) -> Result<(),io::Error> {
        write_graph!(self, "digraph G {{\n");
        for bb in self.mir.basic_blocks().indices() {
            self.visit_basic_block(bb);
        }
        self.print_temp_variables();
        self.print_blocked(mir::RETURN_PLACE, mir::Location {
            block: mir::BasicBlock::new(0),
            statement_index: 0,
        });
        self.print_subset_at_start(mir::Location {
            block: mir::BasicBlock::new(0),
            statement_index: 0,
        });
        self.print_borrow_regions();
        self.print_restricts();
        write_graph!(self, "}}\n");
        Ok(())
    }

    fn print_temp_variables(&self) -> Result<(),io::Error> {
        if self.show_temp_variables() {
            write_graph!(self, "Variables [ style=filled shape = \"record\"");
            write_graph!(self, "label =<<table>");
            write_graph!(self, "<tr><td>VARIABLES</td></tr>");
            write_graph!(self, "<tr><td>Name</td><td>Temporary</td><td>Type</td><td>Region</td></tr>");
            for (temp, var) in self.mir.local_decls.iter_enumerated() {
                let name = var.name.map(|s| s.to_string()).unwrap_or(String::from(""));
                let region = self.variable_regions
                    .get(&temp)
                    .map(|region| format!("{:?}", region))
                    .unwrap_or(String::from(""));
                let typ = to_html!(var.ty);
                write_graph!(self, "<tr><td>{}</td><td>{:?}</td><td>{}</td><td>{}</td></tr>",
                             name, temp, typ, region);
            }
            write_graph!(self, "</table>>];");
        }
        Ok(())
    }

    /// Print the restricts relation as a tree of loans.
    fn print_restricts(&self) -> Result<(),io::Error> {
        if !self.show_restricts() {
            return Ok(())
        }
        write_graph!(self, "subgraph cluster_restricts {{");
        let mut interesting_restricts = Vec::new();
        let mut loans = Vec::new();
        for &(region, loan, point) in self.borrowck_in_facts.borrow_region.iter() {
            write_graph!(self, "\"region_live_at_{:?}_{:?}_{:?}\" [ ", region, loan, point);
            write_graph!(self, "label=\"region_live_at({:?}, {:?}, {:?})\" ];", region, loan, point);
            write_graph!(self, "{:?} -> \"region_live_at_{:?}_{:?}_{:?}\" -> {:?}_{:?}",
                         loan, region, loan, point, region, point);
            interesting_restricts.push((region, point));
            loans.push(loan);
        }
        loans.sort();
        loans.dedup();
        for &loan in loans.iter() {
            let position = self.additional_facts
                .reborrows
                .iter()
                .position(|&(_, l)| loan == l);
            if position.is_some() {
                write_graph!(self, "_{:?} [shape=box color=green]", loan);
            } else {
                write_graph!(self, "_{:?} [shape=box]", loan);
            }
        }
        for (region, point) in interesting_restricts.iter() {
            if let Some(restricts_map) = self.borrowck_out_facts.restricts.get(&point) {
                if let Some(loans) = restricts_map.get(&region) {
                    for loan in loans.iter() {
                        write_graph!(self, "\"restricts_{:?}_{:?}_{:?}\" [ ", point, region, loan);
                        write_graph!(self, "label=\"restricts({:?}, {:?}, {:?})\" ];", point, region, loan);
                        write_graph!(self, "{:?}_{:?} -> \"restricts_{:?}_{:?}_{:?}\" -> {:?}",
                                     region, point, point, region, loan, loan);

                    }
                }
            }
        }
        for &(loan1, loan2) in self.additional_facts.reborrows.iter() {
            write_graph!(self, "_{:?} -> _{:?} [color=green]", loan1, loan2);
            // TODO: Compute strongly connected components.
        }
        write_graph!(self, "}}");
        Ok(())
    }

    /// Print the subset relation at the beginning of the given location.
    fn print_subsets(&self, location: mir::Location) -> Result<(),io::Error> {
        let bb = location.block;
        let stmt = location.statement_index;
        let start_point = self.get_point(location, facts::PointType::Start);
        let subset_map = &self.borrowck_out_facts.subset;
        write_graph!(self, "subgraph cluster_{:?}_{:?} {{", bb, stmt);
        write_graph!(self, "cluster_title_{:?}_{:?} [label=\"subset at {:?}\"]",
                     bb, stmt, location);
        let mut used_regions = HashSet::new();
        if let Some(ref subset) = subset_map.get(&start_point).as_ref() {
            for (source_region, regions) in subset.iter() {
                used_regions.insert(source_region);
                for target_region in regions.iter() {
                    write_graph!(self, "{:?}_{:?}_{:?} -> {:?}_{:?}_{:?}",
                                 bb, stmt, source_region, bb, stmt, target_region);
                    used_regions.insert(target_region);
                }
            }
        }
        for region in used_regions {
            write_graph!(self, "{:?}_{:?}_{:?} [shape=box label=\"{:?}\n(region)\"]",
                         bb, stmt, region, region);
        }
        for (region, point) in self.borrowck_in_facts.region_live_at.iter() {
            if *point == start_point {
                write_graph!(self, "{:?} -> {:?}_{:?}_{:?}", bb, bb, stmt, region);
            }
        }
        write_graph!(self, "}}");
        Ok(())
    }

    fn print_borrow_regions(&self) -> Result<(),io::Error> {
        if !self.show_borrow_regions() {
            return Ok(())
        }
        write_graph!(self, "subgraph cluster_Loans {{");
        for (region, loan, point) in self.borrowck_in_facts.borrow_region.iter() {
            write_graph!(self, "subgraph cluster_{:?} {{", loan);
            let subset_map = &self.borrowck_out_facts.subset;
            if let Some(ref subset) = subset_map.get(&point).as_ref() {
                for (source_region, regions) in subset.iter() {
                    if let Some(local) = self.find_variable(*source_region) {
                        write_graph!(self, "{:?}_{:?} -> {:?}_{:?}",
                                     loan, local, loan, source_region);
                    }
                    for target_region in regions.iter() {
                        write_graph!(self, "{:?}_{:?} -> {:?}_{:?}",
                                     loan, source_region, loan, target_region);
                        if let Some(local) = self.find_variable(*target_region) {
                            write_graph!(self, "{:?}_{:?} -> {:?}_{:?}",
                                         loan, local, loan, target_region);
                        }
                    }
                }
            }
            write_graph!(self, "{:?} -> {:?}_{:?}", loan, loan, region);
            write_graph!(self, "}}");
        }
        write_graph!(self, "}}");
        Ok(())
    }

    fn visit_basic_block(&mut self, bb: mir::BasicBlock) -> Result<(),io::Error> {
        write_graph!(self, "\"{:?}\" [ shape = \"record\"", bb);
        if self.loops.loop_heads.contains(&bb) {
            write_graph!(self, "color=green");
        }
        write_graph!(self, "label =<<table>");
        write_graph!(self, "<th>");
        write_graph!(self, "<td>{:?}</td>", bb);
        write_graph!(self, "<td colspan=\"7\"></td>");
        write_graph!(self, "<td>Definitely Initialized</td>");
        write_graph!(self, "</th>");

        // Is this the entry point of a procedure?
        if bb == mir::BasicBlock::new(0) {
            self.write_magic_wands(false, mir::Location {
                block: mir::BasicBlock::new(0),
                statement_index: 0,
            });
        }

        // Is this a loop head?
        if self.loops.loop_heads.contains(&bb) {
//              1.  Let ``A1`` be a set of pairs ``(p, t)`` where ``p`` is a prefix
//                  accessed in the loop body and ``t`` is the type of access (read,
//                  destructive read, …).
//              2.  Let ``A2`` be a subset of ``A1`` that contains only the prefixes
//                  whose roots are defined before the loop. (The root of the prefix
//                  ``x.f.g.h`` is ``x``.)
//              3.  Let ``A3`` be a subset of ``A2`` without accesses that are subsumed
//                  by other accesses.
//              4.  Let ``U`` be a set of prefixes that are unreachable at the loop
//                  head because they are either moved out or mutably borrowed.
//              5.  For each access ``(p, t)`` in the set ``A3``:

//                  1.  Add a read permission to the loop invariant to read the prefix
//                      up to the last element. If needed, unfold the corresponding
//                      predicates.
//                  2.  Add a permission to the last element based on what is required
//                      by the type of access. If ``p`` is a prefix of some prefixes in
//                      ``U``, then the invariant would contain corresponding predicate
//                      bodies without unreachable elements instead of predicates.


            // Paths accessed inside the loop body.
            let accesses = self.loops.compute_used_paths(bb, &self.mir);
            let definitely_initalised_paths = self.initialization.get_before_block(bb);
            // Paths that are defined before the loop.
            let defined_accesses: Vec<_> = accesses
                .iter()
                .filter(
                    |loops::PlaceAccess { place, kind, .. } |
                    definitely_initalised_paths.iter().any(
                        |initialised_place|
                        // If the prefix is definitely initialised, then this place is a potential
                        // loop invariant.
                        utils::is_prefix(place, initialised_place) ||
                        // If the access is store, then we only need the path to exist, which is
                        // guaranteed if we have at least some of the leaves still initialised.
                        //
                        // Note that the Rust compiler is even more permissive as explained in this
                        // issue: https://github.com/rust-lang/rust/issues/21232.
                        (
                            *kind == loops::PlaceAccessKind::Store &&
                            utils::is_prefix(initialised_place, place)
                        )
                    )
                )
                .map(|loops::PlaceAccess { place, kind, .. } | (place, kind))
                .collect();
            // Paths to whose leaves we need write permissions.
            let mut write_leaves: Vec<mir::Place> = Vec::new();
            for (_i, (place, kind)) in defined_accesses.iter().enumerate() {
                if kind.is_write_access() {
                    let has_prefix = defined_accesses
                        .iter()
                        .any(|(potential_prefix, kind)|
                             kind.is_write_access() &&
                             place != potential_prefix &&
                             utils::is_prefix(place, potential_prefix)
                         );
                    if !has_prefix && !write_leaves.contains(place) {
                        write_leaves.push((*place).clone());
                    }
                }
            }
            // Paths to whose leaves we need read permissions.
            let mut read_leaves: Vec<mir::Place> = Vec::new();
            for (_i, (place, kind)) in defined_accesses.iter().enumerate() {
                if !kind.is_write_access() {
                    let has_prefix = defined_accesses
                        .iter()
                        .any(|(potential_prefix, _kind)|
                             place != potential_prefix &&
                             utils::is_prefix(place, potential_prefix)
                         );
                    if !has_prefix && !read_leaves.contains(place) && !write_leaves.contains(place) {
                        read_leaves.push((*place).clone());
                    }
                }
            }
            // Construct the permission forest.
            let forest = PermissionForest::new(
                &write_leaves, &read_leaves, &definitely_initalised_paths);

            //write_graph!(self, "<tr>");
            //let accesses_str: Vec<_> = accesses
                //.iter()
                //.cloned()
                //.map(|loops::PlaceAccess { place, kind, .. } | (place, kind))
                //.collect();
            //write_graph!(self, "<td colspan=\"2\">Accessed paths (A1):</td>");
            //write_graph!(self, "<td colspan=\"7\">{}</td>", to_sorted_string!(accesses_str));
            //write_graph!(self, "</tr>");

            write_graph!(self, "<tr>");
            write_graph!(self, "<td colspan=\"2\">Def. before loop (A2):</td>");
            write_graph!(self, "<td colspan=\"7\">{}</td>",
                         to_sorted_string!(defined_accesses));
            write_graph!(self, "</tr>");

            write_graph!(self, "<tr>");
            write_graph!(self, "<td colspan=\"2\">Write paths (A3):</td>");
            write_graph!(self, "<td colspan=\"7\">{}</td>",
                         to_sorted_string!(write_leaves));
            write_graph!(self, "</tr>");

            write_graph!(self, "<tr>");
            write_graph!(self, "<td colspan=\"2\">Read paths (A3):</td>");
            write_graph!(self, "<td colspan=\"7\">{}</td>",
                         to_sorted_string!(read_leaves));
            write_graph!(self, "</tr>");

            write_graph!(self, "<tr>");
            write_graph!(self, "<td colspan=\"2\">Invariant:</td>");
            write_graph!(self, "<td colspan=\"7\">{}</td>", to_html_display!(forest));
            write_graph!(self, "</tr>");
        }
        write_graph!(self, "<th>");
        if self.show_statement_indices() {
            write_graph!(self, "<td>Nr</td>");
        }
        write_graph!(self, "<td>statement</td>");
        write_graph!(self, "<td colspan=\"2\">Loans</td>");
        write_graph!(self, "<td colspan=\"2\">Borrow Regions</td>");
        write_graph!(self, "<td colspan=\"2\">Regions</td>");
        write_graph!(self, "<td>{}</td>", self.get_definitely_initialized_before_block(bb));
        write_graph!(self, "</th>");

        let mir::BasicBlockData { ref statements, ref terminator, .. } = self.mir[bb];
        let mut location = mir::Location { block: bb, statement_index: 0 };
        let terminator_index = statements.len();

        while location.statement_index < terminator_index {
            self.visit_statement(location, &statements[location.statement_index])?;
            location.statement_index += 1;
        }
        let terminator = terminator.clone();
        let term_str = if let Some(ref term) = &terminator {
            to_html!(term.kind)
        } else {
            String::from("")
        };
        write_graph!(self, "<tr>");
        if self.show_statement_indices() {
            write_graph!(self, "<td></td>");
        }
        write_graph!(self, "<td>{}</td>", term_str);
        write_graph!(self, "<td colspan=\"6\"></td>");
        write_graph!(self, "<td>{}</td>",
                     self.get_definitely_initialized_after_statement(location));
        write_graph!(self, "</tr>");
        if let Some(ref term) = &terminator {
            if let mir::TerminatorKind::Return = term.kind {
                self.write_magic_wands(true, location);
            }
        }
        write_graph!(self, "</table>> ];");

        if let Some(ref terminator) = &terminator {
            self.visit_terminator(bb, terminator)?;
        }

        if self.loops.loop_heads.contains(&bb) {
            let start_location = mir::Location { block: bb, statement_index: 0 };
            let start_point = self.get_point(start_location, facts::PointType::Start);
            let restricts_map = &self.borrowck_out_facts.restricts;
            if let Some(ref restricts_relation) = restricts_map.get(&start_point).as_ref() {
                for (region, all_loans) in restricts_relation.iter() {
                    // Filter out reborrows.
                    let loans: Vec<_> = all_loans
                        .iter()
                        .filter(|l2| {
                            !all_loans
                                .iter()
                                .map(move |&l1| (**l2, l1))
                                .any(|r| self.additional_facts.reborrows.contains(&r))
                        })
                        .cloned()
                        .collect();


                    // This assertion would fail if instead of reborrow we happen to have a move
                    // like `let mut current = head;`. See issue #18.
                    // TODO: display if we reborrowing an argument.
                    // assert!(all_loans.is_empty() || !loans.is_empty());
                    write_graph!(self, "{:?}_{:?} [shape=box color=green]", bb, region);
                    write_graph!(self, "{:?}_0_{:?} -> {:?}_{:?} [dir=none]",
                                 bb, region, bb, region);
                    for loan in loans.iter() {

                        // The set of regions used in edges. We need to
                        // create nodes for these regions.
                        let mut used_regions = HashSet::new();

                        // Write out all loans that are kept alive by ``region``.
                        write_graph!(self, "{:?}_{:?} -> {:?}_{:?}",
                                     bb, region, bb, loan);

                        write_graph!(self, "subgraph cluster_{:?}_{:?} {{", bb, loan);
                        for (region, l, point) in self.borrowck_in_facts.borrow_region.iter() {
                            if loan == l {

                                // Write the original loan's region.
                                write_graph!(self, "{:?}_{:?} -> {:?}_{:?}_{:?}",
                                             bb, loan, bb, loan, region);
                                used_regions.insert(region);

                                // Write out the subset relation at ``point``.
                                let subset_map = &self.borrowck_out_facts.subset;
                                if let Some(ref subset) = subset_map.get(&point).as_ref() {
                                    for (source_region, regions) in subset.iter() {
                                        used_regions.insert(source_region);
                                        for target_region in regions.iter() {
                                            if source_region == target_region {
                                                continue;
                                            }
                                            used_regions.insert(target_region);
                                            write_graph!(self, "{:?}_{:?}_{:?} -> {:?}_{:?}_{:?}",
                                                         bb, loan, source_region,
                                                         bb, loan, target_region);
                                        }
                                    }
                                }

                            }
                        }

                        for region in used_regions {
                            write_graph!(self, "{:?}_{:?}_{:?} [shape=box label=\"{:?}\n(region)\"]",
                                         bb, loan, region, region);
                            if let Some(local) = self.find_variable(*region) {
                                write_graph!(self, "{:?}_{:?}_{:?} [label=\"{:?}\n(var)\"]",
                                             bb, loan, local, local);
                                write_graph!(self, "{:?}_{:?}_{:?} -> {:?}_{:?}_{:?}",
                                             bb, loan, local, bb, loan, region);
                            }
                        }
                        write_graph!(self, "}}");
                    }

                }
            }

            for (region, point) in self.borrowck_in_facts.region_live_at.iter() {
                if *point == start_point {
                    // TODO: the unwrap_or is a temporary workaround
                    // See issue prusti-internal/issues/14
                    let variable = self.find_variable(*region).unwrap_or(mir::Local::new(1000));
                    self.print_blocked(variable, start_location);
                }
            }

            self.print_subsets(start_location);
        }

        Ok(())
    }

    fn visit_statement(&self, location: mir::Location,
                       statement: &mir::Statement) -> Result<(),io::Error> {
        write_graph!(self, "<tr>");
        if self.show_statement_indices() {
            write_graph!(self, "<td>{}</td>", location.statement_index);
        }
        write_graph!(self, "<td>{}</td>", to_html!(statement));

        let start_point = self.get_point(location, facts::PointType::Start);
        let mid_point = self.get_point(location, facts::PointType::Mid);

        // Loans.
        if let Some(ref blas) = self.borrowck_out_facts.borrow_live_at.get(&start_point).as_ref() {
            write_graph!(self, "<td>{}</td>", to_sorted_string!(blas));
        } else {
            write_graph!(self, "<td></td>");
        }
        if let Some(ref blas) = self.borrowck_out_facts.borrow_live_at.get(&mid_point).as_ref() {
            // Get the loans that dye in this statement.
            let dying_loans = self.get_dying_loans(location);

            // Format the loans and mark the dying ones.
            let mut blas = (**blas).clone();
            blas.sort();
            let blas: Vec<_> = blas.into_iter()
                .map(|loan| {
                    if dying_loans.contains(&loan) {
                        format!("<b><font color=\"red\">{:?}</font></b>", loan)
                    } else {
                        format!("{:?}", loan)
                    }
                })
                .collect();

            write_graph!(self, "<td>{}", blas.join(", "));
            self.write_reborrowing_trees(&dying_loans);
            write_graph!(self, "</td>");
        } else {
            write_graph!(self, "<td></td>");
        }

        // Borrow regions (loan start points).
        let borrow_regions: Vec<_> = self.borrowck_in_facts
            .borrow_region
            .iter()
            .filter(|(_, _, point)| *point == start_point)
            .cloned()
            .map(|(region, loan, _)| (region, loan))
            .collect();
        write_graph!(self, "<td>{}</td>", to_sorted_string!(borrow_regions));
        let borrow_regions: Vec<_> = self.borrowck_in_facts
            .borrow_region
            .iter()
            .filter(|(_, _, point)| *point == mid_point)
            .cloned()
            .map(|(region, loan, _)| (region, loan))
            .collect();
        write_graph!(self, "<td>{}</td>", to_sorted_string!(borrow_regions));

        // Regions alive at this program point.
        let regions: Vec<_> = self.borrowck_in_facts
            .region_live_at
            .iter()
            .filter(|(_, point)| *point == start_point)
            .cloned()
            // TODO: Understand why we cannot unwrap here:
            .map(|(region, _)| (region, self.find_variable(region)))
            .collect();
        write_graph!(self, "<td>{}</td>", to_sorted_string!(regions));
        let regions: Vec<_> = self.borrowck_in_facts
            .region_live_at
            .iter()
            .filter(|(_, point)| *point == mid_point)
            .cloned()
            // TODO: Understand why we cannot unwrap here:
            .map(|(region, _)| (region, self.find_variable(region)))
            .collect();
        write_graph!(self, "<td>{}</td>", to_sorted_string!(regions));

        write_graph!(self, "<td>{}</td>",
                     self.get_definitely_initialized_after_statement(location));

        write_graph!(self, "</tr>");
        Ok(())
    }

    fn get_point(&self, location: mir::Location, point_type: facts::PointType) -> facts::PointIndex {
        let point = facts::Point {
            location: location,
            typ: point_type,
        };
        self.interner.get_point_index(&point)
    }

    fn visit_terminator(&self, bb: mir::BasicBlock, terminator: &mir::Terminator) -> Result<(),io::Error> {
        use rustc::mir::TerminatorKind;
        match terminator.kind {
            TerminatorKind::Goto { target } => {
                write_edge!(self, bb, target);
            }
            TerminatorKind::SwitchInt { ref targets, .. } => {
                for target in targets {
                    write_edge!(self, bb, target);
                }
            }
            TerminatorKind::Resume => {
                write_edge!(self, bb, str resume);
            }
            TerminatorKind::Abort => {
                write_edge!(self, bb, str abort);
            }
            TerminatorKind::Return => {
                write_edge!(self, bb, str return);
            }
            TerminatorKind::Unreachable => {}
            TerminatorKind::DropAndReplace { ref target, unwind, .. } |
            TerminatorKind::Drop { ref target, unwind, .. } => {
                write_edge!(self, bb, target);
                if let Some(target) = unwind {
                    write_edge!(self, bb, unwind target);
                }
            }
            TerminatorKind::Call { ref destination, cleanup, .. } => {
                if let &Some((_, target)) = destination {
                    write_edge!(self, bb, target);
                }
                if let Some(target) = cleanup {
                    write_edge!(self, bb, unwind target);
                }
            }
            TerminatorKind::Assert { target, cleanup, .. } => {
                write_edge!(self, bb, target);
                if let Some(target) = cleanup {
                    write_edge!(self, bb, unwind target);
                }
            }
            TerminatorKind::Yield { .. } => { unimplemented!() }
            TerminatorKind::GeneratorDrop => { unimplemented!() }
            TerminatorKind::FalseEdges { ref real_target, ref imaginary_targets } => {
                write_edge!(self, bb, real_target);
                for target in imaginary_targets {
                    write_edge!(self, bb, imaginary target);
                }
            }
            TerminatorKind::FalseUnwind { real_target, unwind } => {
                write_edge!(self, bb, real_target);
                if let Some(target) = unwind {
                    write_edge!(self, bb, imaginary target);
                }
            }
        };
        Ok(())
    }

    fn show_statement_indices(&self) -> bool {
        get_config_option("PRUSTI_DUMP_SHOW_STATEMENT_INDICES", true)
    }

    fn show_temp_variables(&self) -> bool {
        get_config_option("PRUSTI_DUMP_SHOW_TEMP_VARIABLES", true)
    }

    fn show_borrow_regions(&self) -> bool {
        get_config_option("PRUSTI_DUMP_SHOW_BORROW_REGIONS", false)
    }

    fn show_restricts(&self) -> bool {
        get_config_option("PRUSTI_DUMP_SHOW_RESTRICTS", false)
    }
}

/// Definitely initialized analysis.
impl<'a, 'tcx> MirInfoPrinter<'a, 'tcx> {

    fn get_definitely_initialized_before_block(&self, bb: mir::BasicBlock) -> String {
        let place_set = self.initialization.get_before_block(bb);
        to_sorted_string!(place_set)
    }


    fn get_definitely_initialized_after_statement(&self, location: mir::Location) -> String {
        let place_set = self.initialization.get_after_statement(location);
        to_sorted_string!(place_set)
    }
}

/// Maybe blocking analysis.
impl<'a, 'tcx> MirInfoPrinter<'a, 'tcx> {

    /// Print the subset relation at a given program point.
    fn print_subset_at_start(&self, location: mir::Location) -> Result<(),io::Error> {
        let point = self.get_point(location, facts::PointType::Start);
        let subset_map = &self.borrowck_out_facts.subset;
        if let Some(ref subset) = subset_map.get(&point).as_ref() {
            write_graph!(self, "subgraph cluster_{:?} {{", point);
            let mut used_regions = HashSet::new();
            for (from_region, to_regions) in subset.iter() {
                used_regions.insert(*from_region);
                for to_region in to_regions.iter() {
                    used_regions.insert(*to_region);
                    write_graph!(self, "{:?}_{:?} -> {:?}_{:?}",
                                 point, from_region, point, to_region);
                }
            }
            for region in used_regions {
                if let Some(local) = self.find_variable(region) {
                    write_graph!(self, "{:?}_{:?} [shape=box label=\"{:?}:{:?}\"]",
                                 point, region, local, region);
                } else {
                    write_graph!(self, "{:?}_{:?} [shape=box label=\"{:?}\"]",
                                 point, region, region);
                }
            }
            write_graph!(self, "}}");
        }
        Ok(())
    }

    /// Print variables that are maybe blocked by the given variable at
    /// the start of the given location.
    fn print_blocked(&self, blocker: mir::Local, location: mir::Location) -> Result<(),io::Error> {
        let bb = location.block;
        let start_point = self.get_point(location, facts::PointType::Start);
        if let Some(region) = self.variable_regions.get(&blocker) {
            write_graph!(self, "{:?} -> {:?}_{:?}_{:?}", bb, bb, blocker, region);
            write_graph!(self, "{:?}_{:?}_{:?} [label=\"{:?}:{:?}\n(blocking variable)\"]",
                         bb, blocker, region, blocker, region);
            write_graph!(self, "subgraph cluster_{:?} {{", bb);
            let subset_map = &self.borrowck_out_facts.subset;
            if let Some(ref subset) = subset_map.get(&start_point).as_ref() {
                if let Some(blocked_regions) = subset.get(&region) {
                    for blocked_region in blocked_regions.iter() {
                        if blocked_region == region {
                            continue;
                        }
                        if let Some(blocked) = self.find_variable(*blocked_region) {
                            write_graph!(self, "{:?}_{:?}_{:?} -> {:?}_{:?}_{:?}",
                                         bb, blocker, region,
                                         bb, blocked, blocked_region);
                        }
                    }
                }
            }
            write_graph!(self, "}}");
        }
        Ok(())
    }

    /// Find a variable that has the given region in its type.
    fn find_variable(&self, region: facts::Region) -> Option<mir::Local> {
        let mut local = None;
        for (key, value) in self.variable_regions.iter() {
            if *value == region {
                assert!(local.is_none());
                local = Some(*key);
            }
        }
        local
    }
}

/// Loan end analysis.
impl<'a, 'tcx> MirInfoPrinter<'a, 'tcx> {

    /// Get locations that are reachable from this location in one step.
    fn get_successors(&self, location: mir::Location) -> Vec<mir::Location> {
        let statements_len = self.mir[location.block].statements.len();
        if location.statement_index < statements_len {
            vec![mir::Location {
                statement_index: location.statement_index + 1,
                .. location
            }]
        } else {
            let mut successors = Vec::new();
            for successor in self.mir[location.block].terminator.as_ref().unwrap().successors() {
                successors.push(mir::Location {
                    block: *successor,
                    statement_index: 0,
                });
            }
            successors
        }
    }

    /// Get loans that dye at the given location.
    fn get_dying_loans(&self, location: mir::Location) -> Vec<facts::Loan> {
        let start_point = self.get_point(location, facts::PointType::Start);
        let mid_point = self.get_point(location, facts::PointType::Mid);

        if let Some(mid_loans) = self.borrowck_out_facts.borrow_live_at.get(&mid_point) {
            let mut mid_loans = mid_loans.clone();
            mid_loans.sort();
            let default_vec = vec![];
            let start_loans = self.borrowck_out_facts
                .borrow_live_at
                .get(&start_point)
                .unwrap_or(&default_vec);
            let mut start_loans = start_loans.clone();
            start_loans.sort();
            debug!("start_loans = {:?}", start_loans);
            debug!("mid_loans = {:?}", mid_loans);
            // Loans are created in mid point, so mid_point may contain more loans than the start
            // point.
            assert!(start_loans.iter().all(|loan| mid_loans.contains(loan)));

            let mir: &mir::Mir = &self.mir;
            let successors = self.get_successors(location);

            // Filter loans that are not missing in all successors.
            mid_loans
                .into_iter()
                .filter(|loan| {
                    !successors
                        .iter()
                        .any(|successor_location| {
                            let point = self.get_point(*successor_location, facts::PointType::Start);
                            self.borrowck_out_facts
                                .borrow_live_at
                                .get(&point)
                                .map_or(false, |successor_loans| {
                                    successor_loans.contains(loan)
                                })
                        })
                })
                .collect()
        } else {
            assert!(self.borrowck_out_facts.borrow_live_at.get(&start_point).is_none());
            vec![]
        }
    }

    /// `package` – should it also try to compute the package statements?
    fn write_magic_wands(&mut self, package: bool,
                         location: mir::Location) -> Result<(), io::Error> {
        // TODO: Refactor out this code that computes magic wands.
        let blocker = mir::RETURN_PLACE;
        //TODO: Check if it really is always start and not the mid point.
        let start_point = self.get_point(location, facts::PointType::Start);

        if let Some(region) = self.variable_regions.get(&blocker) {
            write_graph!(self, "<tr>");
            write_graph!(self, "<td colspan=\"2\">Magic wand</td>");
            let subset_map = &self.borrowck_out_facts.subset;
            if let Some(ref subset) = subset_map.get(&start_point).as_ref() {
                let mut blocked_variables = Vec::new();
                if let Some(blocked_regions) = subset.get(&region) {
                    for blocked_region in blocked_regions.iter() {
                        if blocked_region == region {
                            continue;
                        }
                        if let Some(local) = self.find_variable(*blocked_region) {
                            blocked_variables.push(format!("{:?}:{:?}", local, blocked_region));
                        }
                    }
                    write_graph!(self, "<td colspan=\"7\">{:?}:{:?} --* {}</td>",
                                 blocker, region, to_sorted_string!(blocked_variables));
                } else {
                    write_graph!(self, "<td colspan=\"7\">BUG: no blocked region</td>");
                }
            } else {
                write_graph!(self, "<td colspan=\"7\">BUG: no subsets</td>");
            }
            write_graph!(self, "</tr>");
            if package {
                let restricts_map = &self.borrowck_out_facts.restricts;
                write_graph!(self, "<tr>");
                write_graph!(self, "<td colspan=\"2\">Package</td>");
                if let Some(ref restricts) = restricts_map.get(&start_point).as_ref() {
                    if let Some(loans) = restricts.get(&region) {
                        let loans: Vec<_> = loans.iter().cloned().collect();
                        write_graph!(self, "<td colspan=\"7\">{}", to_sorted_string!(loans));
                        self.write_reborrowing_trees(&loans)?;
                        write_graph!(self, "</td>");
                    } else {
                        write_graph!(self, "<td colspan=\"7\">BUG: no loans</td>");
                    }
                } else {
                    write_graph!(self, "<td colspan=\"7\">BUG: no restricts</td>");
                }
                write_graph!(self, "</tr>");
            }
        }
        Ok(())
    }

    fn write_reborrowing_trees(&self, loans: &[facts::Loan]) -> Result<(), io::Error> {
        // Find minimal elements that are the tree roots.
        let mut roots = Vec::new();
        for &loan in loans.iter() {
            let is_smallest = !loans
                .iter()
                .any(|&other_loan| {
                    self.additional_facts.reborrows.contains(&(other_loan, loan))
                });
            if is_smallest {
                roots.push(loan);
            }
        }
        // Reconstruct the tree from each root.
        for &root in roots.iter() {
            write_graph!(self, "<br />");
            self.write_reborrowing_tree(loans, root)?;
        }
        Ok(())
    }

    fn write_reborrowing_tree(&self, loans: &[facts::Loan],
                              node: facts::Loan) -> Result<(), io::Error> {
        if let Some(local) = self.call_magic_wands.get(&node) {
            let var_region = self.variable_regions[&local];
            write_graph!(self, "apply({:?}, {:?}:{:?})", node, local, var_region);
        } else {
            write_graph!(self, "{:?}", node);
        }
        let mut children = Vec::new();
        for &loan in loans.iter() {
            if self.additional_facts.reborrows_direct.contains(&(node, loan)) {
                children.push(loan);
            }
        }
        if children.len() == 1 {
            write_graph!(self, "→");
            let child = children.pop().unwrap();
            self.write_reborrowing_tree(loans, child);
        } else if children.len() > 1 {
            write_graph!(self, "→«");
            for child in children {
                self.write_reborrowing_tree(loans, child);
                write_graph!(self, ",");
            }
            write_graph!(self, "»");
        }
        Ok(())
    }
}

fn get_config_option(name: &str, default: bool) -> bool {
    match env::var_os(name).and_then(|value| value.into_string().ok()).as_ref() {
        Some(value) => {
            match value as &str {
                "true" => true,
                "false" => false,
                "1" => true,
                "0" => false,
                _ => unreachable!("Uknown configuration value “{}” for “{}”.", value, name),
            }
        },
        None => {
            default
        },
    }
}
