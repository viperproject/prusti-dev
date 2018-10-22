// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::borrowck::facts;
use super::loops;
use super::loops_utils::*;
use super::mir_analyses::initialization::{
    compute_definitely_initialized,
    DefinitelyInitializedAnalysisResult
};
use super::mir_analyses::liveness::{
    compute_liveness,
    LivenessAnalysisResult
};
use super::polonius_info::PoloniusInfo;
use crate::utils;
use std::cell;
use std::env;
use std::collections::HashSet;
use std::fs::File;
use std::io::{self, Write, BufWriter};
use std::path::PathBuf;
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

        let mir = self.tcx.mir_validated(def_id).borrow();

        let loop_info = loops::ProcedureLoops::new(&mir);

        let graph_path = PathBuf::from("nll-facts")
            .join(def_path.to_filename_friendly_no_crate())
            .join("graph.dot");
        let graph_file = File::create(graph_path).expect("Unable to create file");
        let graph = BufWriter::new(graph_file);

        let initialization = compute_definitely_initialized(&mir, self.tcx, def_path);
        let liveness = compute_liveness(&mir);

        let mut mir_info_printer = MirInfoPrinter {
            tcx: self.tcx,
            mir: &mir,
            graph: cell::RefCell::new(graph),
            loops: loop_info,
            initialization: initialization,
            liveness: liveness,
            polonius_info: PoloniusInfo::new(self.tcx, def_id, &mir),
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


struct MirInfoPrinter<'a, 'tcx: 'a> {
    pub tcx: TyCtxt<'a, 'tcx, 'tcx>,
    pub mir: &'a mir::Mir<'tcx>,
    pub graph: cell::RefCell<BufWriter<File>>,
    pub loops: loops::ProcedureLoops,
    pub initialization: DefinitelyInitializedAnalysisResult<'tcx>,
    pub liveness: LivenessAnalysisResult,
    pub polonius_info: PoloniusInfo<'a, 'tcx>,
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
                let region = self.polonius_info.variable_regions
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
        for &(region, loan, point) in self.polonius_info.borrowck_in_facts.borrow_region.iter() {
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
            let position = self.polonius_info
                .additional_facts
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
            if let Some(restricts_map) = self.polonius_info.borrowck_out_facts.restricts.get(&point) {
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
        for &(loan1, loan2) in self.polonius_info.additional_facts.reborrows.iter() {
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
        let subset_map = &self.polonius_info.borrowck_out_facts.subset;
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
        for (region, point) in self.polonius_info.borrowck_in_facts.region_live_at.iter() {
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
        for (region, loan, point) in self.polonius_info.borrowck_in_facts.borrow_region.iter() {
            write_graph!(self, "subgraph cluster_{:?} {{", loan);
            let subset_map = &self.polonius_info.borrowck_out_facts.subset;
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
        write_graph!(self, "<td>Liveness</td>");
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
            //write_graph!(self, "<td colspan=\"8\">{}</td>", to_sorted_string!(accesses_str));
            //write_graph!(self, "</tr>");

            write_graph!(self, "<tr>");
            write_graph!(self, "<td colspan=\"2\">Def. before loop (A2):</td>");
            write_graph!(self, "<td colspan=\"8\">{}</td>",
                         to_sorted_string!(defined_accesses));
            write_graph!(self, "</tr>");

            write_graph!(self, "<tr>");
            write_graph!(self, "<td colspan=\"2\">Write paths (A3):</td>");
            write_graph!(self, "<td colspan=\"8\">{}</td>",
                         to_sorted_string!(write_leaves));
            write_graph!(self, "</tr>");

            write_graph!(self, "<tr>");
            write_graph!(self, "<td colspan=\"2\">Read paths (A3):</td>");
            write_graph!(self, "<td colspan=\"8\">{}</td>",
                         to_sorted_string!(read_leaves));
            write_graph!(self, "</tr>");

            write_graph!(self, "<tr>");
            write_graph!(self, "<td colspan=\"2\">Invariant:</td>");
            write_graph!(self, "<td colspan=\"8\">{}</td>", to_html_display!(forest));
            write_graph!(self, "</tr>");

            let mut reborrows: Vec<(mir::Local, facts::Region)> = write_leaves
                .iter()
                .flat_map(|place| {
                    // Only locals – we do not support references in fields.
                    match place {
                        mir::Place::Local(local) => Some(local),
                        _ => None,
                    }
                })
                .flat_map(|local| {
                    // Only references (variables that have regions).
                    self.polonius_info.variable_regions.get(&local).map(|region| (*local, *region))
                })
                // Note: With our restrictions these two checks are sufficient to ensure
                // that we have reborrowing. For example, we do not need to check that
                // at least one of the loans is coming from inside of the loop body.
                .collect();

            write_graph!(self, "<tr>");
            write_graph!(self, "<td colspan=\"2\">Reborrows:</td>");
            write_graph!(self, "<td colspan=\"8\">{}</td>", to_sorted_string!(reborrows));
            write_graph!(self, "</tr>");

            for &(local, _) in reborrows.iter() {
                self.polonius_info.add_loop_magic_wand(bb, &self.loops, local);
            }

            if let Some(ref magic_wands) = self.polonius_info.loop_magic_wands.get(&bb) {
                write_graph!(self, "<tr>");
                write_graph!(self, "<td colspan=\"2\">Magic wands:</td>");
                write_graph!(self, "<td colspan=\"8\">{}</td>", to_sorted_string!(magic_wands));
                write_graph!(self, "</tr>");

                let location = mir::Location {
                    block: bb,
                    statement_index: 0,
                };
                let point = self.get_point(location, facts::PointType::Start);
                let restricts_map = &self.polonius_info.borrowck_out_facts.restricts;
                let restricts = restricts_map.get(&point);
                let restricts = restricts.as_ref().unwrap();

                for magic_wand in magic_wands.iter() {
                    let (all_loans, zombie_loans) = self.polonius_info.get_all_loans_kept_alive_by(
                        point, magic_wand.region);
                    write_graph!(self, "<tr>");
                    write_graph!(self, "<td colspan=\"2\">{:?} (all loans):</td>",
                                 magic_wand.variable);
                    write_graph!(self, "<td colspan=\"8\">{}</td>", to_sorted_string!(all_loans));
                    write_graph!(self, "</tr>");

                    let loop_loans: Vec<_> = all_loans
                        .iter()
                        .filter(|loan| {
                            let location = self.polonius_info.loan_position[loan];
                            let loop_body = &self.loops.loop_bodies[&magic_wand.loop_id];
                            loop_body.contains(&location.block)
                        })
                        .cloned()
                        .collect();
                    write_graph!(self, "<tr>");
                    write_graph!(self, "<td colspan=\"2\">{:?} (loop loans):</td>",
                                 magic_wand.variable);
                    write_graph!(self, "<td colspan=\"8\">{}</td>", to_sorted_string!(loop_loans));
                    write_graph!(self, "</tr>");

                    let not_loop_loans: Vec<_> = all_loans
                        .iter()
                        .filter(|loan| {
                            let location = self.polonius_info.loan_position[loan];
                            let loop_body = &self.loops.loop_bodies[&magic_wand.loop_id];
                            !loop_body.contains(&location.block)
                        })
                        .cloned()
                        .collect();
                    write_graph!(self, "<tr>");
                    write_graph!(self, "<td colspan=\"2\">{:?} (not loop loans):</td>",
                                 magic_wand.variable);
                    write_graph!(self, "<td colspan=\"8\">{}</td>", to_sorted_string!(not_loop_loans));
                    write_graph!(self, "</tr>");

                    //let intersect = || {
                        //for &loop_loan in loop_loans.iter() {
                            //for &not_loop_loan in not_loop_loans.iter() {
                                //if self.polonius_info.additional_facts
                                        //.reborrows_direct.contains(&(not_loop_loan, loop_loan)) {
                                    //return (loop_loan, not_loop_loan);
                                //}
                                //debug!("Check: {:?} {:?}", loop_loan, not_loop_loan);
                            //}
                        //}
                        //for (l1, l2) in self.polonius_info.additional_facts.reborrows_direct.iter() {
                            //debug!("reborrows_direct: {:?} {:?}", l1, l2);
                        //}
                        //unreachable!();
                    //};
                    //let (loop_loan, not_loop_loan) = intersect();
                    //write_graph!(self, "<tr>");
                    //write_graph!(self, "<td colspan=\"2\">{:?} (intersection):</td>",
                                 //magic_wand.variable);
                    //write_graph!(self, "<td colspan=\"8\">{:?} {:?}</td>", loop_loan, not_loop_loan);
                    //write_graph!(self, "</tr>");

                    let forest = self.polonius_info.construct_reborrowing_forest(
                        &loop_loans, &zombie_loans);
                    let dag = self.polonius_info.construct_reborrowing_dag(
                        &loop_loans, &zombie_loans, location);
                    // TODO: Need to find the loan at which to cut the cycle.
                    // Idea: do not allow to propage via back_edges.
                    write_graph!(self, "<tr>");
                    write_graph!(self, "<td colspan=\"2\">{:?} (package end loop body):</td>",
                                 magic_wand.variable);
                    write_graph!(self, "<td colspan=\"8\">");
                    write_graph!(self, "{}", forest.to_string().replace(";", "<br />"));
                    write_graph!(self, "<br />{}", dag.to_string());
                    write_graph!(self, "</td>");
                    write_graph!(self, "</tr>");
                }
            }
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
        write_graph!(self, "<td>{}</td>", self.get_live_before_block(bb));
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
        write_graph!(self, "<td></td>");
        self.write_mid_point_blas(location);
        write_graph!(self, "<td colspan=\"4\"></td>");
        write_graph!(self, "<td>{}</td>",
                     self.get_definitely_initialized_after_statement(location));
        write_graph!(self, "<td>{}</td>",
                     self.get_live_after_statement(location));
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
            let restricts_map = &self.polonius_info.borrowck_out_facts.restricts;
            if let Some(ref restricts_relation) = restricts_map.get(&start_point).as_ref() {
                for (region, all_loans) in restricts_relation.iter() {
                    // Filter out reborrows.
                    let loans: Vec<_> = all_loans
                        .iter()
                        .filter(|l2| {
                            !all_loans
                                .iter()
                                .map(move |&l1| (**l2, l1))
                                .any(|r| self.polonius_info.additional_facts.reborrows.contains(&r))
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
                        let borrow_region = &self.polonius_info.borrowck_in_facts.borrow_region;
                        for (region, l, point) in borrow_region.iter() {
                            if loan == l {

                                // Write the original loan's region.
                                write_graph!(self, "{:?}_{:?} -> {:?}_{:?}_{:?}",
                                             bb, loan, bb, loan, region);
                                used_regions.insert(region);

                                // Write out the subset relation at ``point``.
                                let subset_map = &self.polonius_info.borrowck_out_facts.subset;
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

            for (region, point) in self.polonius_info.borrowck_in_facts.region_live_at.iter() {
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
        if let Some(ref blas) = self.polonius_info.borrowck_out_facts.borrow_live_at.get(&start_point).as_ref() {
            write_graph!(self, "<td>{}</td>", to_sorted_string!(blas));
        } else {
            write_graph!(self, "<td></td>");
        }
        self.write_mid_point_blas(location);

        // Borrow regions (loan start points).
        let borrow_regions: Vec<_> = self.polonius_info.borrowck_in_facts
            .borrow_region
            .iter()
            .filter(|(_, _, point)| *point == start_point)
            .cloned()
            .map(|(region, loan, _)| (region, loan))
            .collect();
        write_graph!(self, "<td>{}</td>", to_sorted_string!(borrow_regions));
        let borrow_regions: Vec<_> = self.polonius_info.borrowck_in_facts
            .borrow_region
            .iter()
            .filter(|(_, _, point)| *point == mid_point)
            .cloned()
            .map(|(region, loan, _)| (region, loan))
            .collect();
        write_graph!(self, "<td>{}</td>", to_sorted_string!(borrow_regions));

        // Regions alive at this program point.
        let regions: Vec<_> = self.polonius_info.borrowck_in_facts
            .region_live_at
            .iter()
            .filter(|(_, point)| *point == start_point)
            .cloned()
            // TODO: Understand why we cannot unwrap here:
            .map(|(region, _)| (region, self.find_variable(region)))
            .collect();
        write_graph!(self, "<td>{}</td>", to_sorted_string!(regions));
        let regions: Vec<_> = self.polonius_info.borrowck_in_facts
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
        write_graph!(self, "<td>{}</td>",
                     self.get_live_after_statement(location));

        write_graph!(self, "</tr>");
        Ok(())
    }

    fn get_point(&self, location: mir::Location, point_type: facts::PointType) -> facts::PointIndex {
        let point = facts::Point {
            location: location,
            typ: point_type,
        };
        self.polonius_info.interner.get_point_index(&point)
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

/// Liveness analysis.
impl<'a, 'tcx> MirInfoPrinter<'a, 'tcx> {

    fn get_live_before_block(&self, bb: mir::BasicBlock) -> String {
        let set = self.liveness.get_before_block(bb);
        to_sorted_string!(set)
    }


    fn get_live_after_statement(&self, location: mir::Location) -> String {
        let set = self.liveness.get_after_statement(location);
        to_sorted_string!(set)
    }
}

/// Maybe blocking analysis.
impl<'a, 'tcx> MirInfoPrinter<'a, 'tcx> {

    /// Print the subset relation at a given program point.
    fn print_subset_at_start(&self, location: mir::Location) -> Result<(),io::Error> {
        let point = self.get_point(location, facts::PointType::Start);
        let subset_map = &self.polonius_info.borrowck_out_facts.subset;
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
        if let Some(region) = self.polonius_info.variable_regions.get(&blocker) {
            write_graph!(self, "{:?} -> {:?}_{:?}_{:?}", bb, bb, blocker, region);
            write_graph!(self, "{:?}_{:?}_{:?} [label=\"{:?}:{:?}\n(blocking variable)\"]",
                         bb, blocker, region, blocker, region);
            write_graph!(self, "subgraph cluster_{:?} {{", bb);
            let subset_map = &self.polonius_info.borrowck_out_facts.subset;
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
        for (key, value) in self.polonius_info.variable_regions.iter() {
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

    /// Print the HTML cell with loans at given location.
    fn write_mid_point_blas(&self, location: mir::Location) -> Result<(),io::Error> {
        let mid_point = self.get_point(location, facts::PointType::Mid);
        let borrow_live_at_map = &self.polonius_info.borrowck_out_facts.borrow_live_at;
        let mut blas = if let Some(ref blas) = borrow_live_at_map.get(&mid_point).as_ref() {
            (**blas).clone()
        } else {
            Vec::new()
        };
        let zombie_borrow_live_at_map = &self.polonius_info.additional_facts.zombie_borrow_live_at;
        let mut zombie_blas = if let Some(ref zombie_blas) =
            zombie_borrow_live_at_map.get(&mid_point).as_ref() {
            (**zombie_blas).clone()
        } else {
            Vec::new()
        };

        // Get the loans that dye in this statement.
        let dying_loans = self.polonius_info.get_dying_loans(location);
        let dying_zombie_loans = self.polonius_info.get_dying_zombie_loans(location);
        let becoming_zombie_loans = self.polonius_info
            .additional_facts
            .borrow_become_zombie_at
            .get(&mid_point)
            .cloned()
            .unwrap_or(Vec::new());

        // Format the loans and mark the dying ones.
        blas.sort();
        let mut blas: Vec<_> = blas.into_iter()
            .map(|loan| {
                if becoming_zombie_loans.contains(&loan) {
                    format!("<b><font color=\"orchid\">{:?}</font></b>", loan)
                } else if dying_loans.contains(&loan) {
                    format!("<b><font color=\"red\">{:?}</font></b>", loan)
                } else {
                    format!("{:?}", loan)
                }
            })
            .collect();
        zombie_blas.sort();
        blas.extend(
            zombie_blas
                .iter()
                .map(|loan| {
                    if dying_zombie_loans.contains(&loan) {
                        format!("<b><font color=\"brown\">{:?}</font></b>", loan)
                    } else {
                        format!("<b><font color=\"forestgreen\">{:?}</font></b>", loan)
                    }
                })
        );

        write_graph!(self, "<td>{}", blas.join(", "));
        let mut all_dying_loans: Vec<_> = dying_loans
            .iter()
            .filter(|loan| {
                !becoming_zombie_loans.contains(loan)
            })
            .cloned()
            .collect();
        all_dying_loans.extend(dying_zombie_loans.iter().cloned());
        let dag = self.polonius_info.construct_reborrowing_dag(
            &all_dying_loans, &dying_zombie_loans, location);
        let forest = self.polonius_info.construct_reborrowing_forest(
            &all_dying_loans, &dying_zombie_loans);
        if !all_dying_loans.is_empty() {
            write_graph!(self, "<br />{}", forest.to_string().replace(";", "<br />"));
            write_graph!(self, "<br />{}", dag.to_string());
        }
        write_graph!(self, "</td>");

        Ok(())
    }

    /// `package` – should it also try to compute the package statements?
    fn write_magic_wands(&mut self, package: bool,
                         location: mir::Location) -> Result<(), io::Error> {
        // TODO: Refactor out this code that computes magic wands.
        let blocker = mir::RETURN_PLACE;
        //TODO: Check if it really is always start and not the mid point.
        let start_point = self.get_point(location, facts::PointType::Start);

        if let Some(region) = self.polonius_info.variable_regions.get(&blocker) {
            write_graph!(self, "<tr>");
            write_graph!(self, "<td colspan=\"2\">Magic wand</td>");
            let subset_map = &self.polonius_info.borrowck_out_facts.subset;
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
                let (all_loans, zombie_loans) = self.polonius_info.get_all_loans_kept_alive_by(
                    start_point, *region);
                let forest = self.polonius_info.construct_reborrowing_forest(
                    &all_loans, &zombie_loans);
                let dag = self.polonius_info.construct_reborrowing_dag(
                    &all_loans, &zombie_loans, location);
                //let restricts_map = &self.polonius_info.borrowck_out_facts.restricts;
                write_graph!(self, "<tr>");
                write_graph!(self, "<td colspan=\"2\">Package</td>");
                write_graph!(self, "<td colspan=\"7\">{}", to_sorted_string!(all_loans));
                if !all_loans.is_empty() {
                    write_graph!(self, "<br />{}", forest.to_string().replace(";", "<br />"));
                    write_graph!(self, "<br />{}", dag.to_string());
                }
                write_graph!(self, "</td>");
                write_graph!(self, "</tr>");
            }
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
