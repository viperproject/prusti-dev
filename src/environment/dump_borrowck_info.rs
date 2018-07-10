// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use environment::borrowck::{facts, regions};
use environment::loops;
use datafrog::{Iteration, Relation};
use std::cell;
use std::env;
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, Write, BufWriter};
use std::path::PathBuf;
use polonius_engine::{Algorithm, Output};
use rustc::hir::{self, intravisit};
use rustc::mir;
use rustc::ty::{self, TyCtxt};
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

        let all_facts = facts_loader.facts;
        let output = Output::compute(&all_facts, Algorithm::Naive, true);
        let additional_facts = compute_additional_facts(&all_facts, &output);

        let mir = self.tcx.mir_validated(def_id).borrow();
        let loop_info = loops::ProcedureLoops::new(&mir);

        let graph_path = PathBuf::from("nll-facts")
            .join(def_path.to_filename_friendly_no_crate())
            .join("graph.dot");
        let graph_file = File::create(graph_path).expect("Unable to create file");
        let mut graph = BufWriter::new(graph_file);

        let interner = facts_loader.interner;
        let loan_position = all_facts.borrow_region
            .iter()
            .map(|&(_, loan, point_index)| {
                let point = interner.get_point(point_index);
                (loan, point.location)
            })
            .collect();

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
        };
        mir_info_printer.print_info();

        trace!("[visit_fn] exit");
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
    /// ```
    /// reborrows(Loan, Loan);
    /// reborrows(L1, L2) :-
    ///     borrow_region(R, L1, P),
    ///     restricts(R, P, L2).
    /// reborrows(L1, L3) :-
    ///     reborrows(L1, L2),
    ///     reborrows(L2, L3).
    /// ```
    pub reborrows: Vec<(facts::Loan, facts::Loan)>,
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
        //self.print_borrow_regions();
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
        let start_point = self.get_point(location, facts::PointType::Start);
        let subset_map = &self.borrowck_out_facts.subset;
        if let Some(ref subset) = subset_map.get(&start_point).as_ref() {
            for (source_region, regions) in subset.iter() {
                for target_region in regions.iter() {
                    write_graph!(self, "{:?}_{:?} -> {:?}_{:?}",
                                 bb, source_region, bb, target_region);
                }
            }
        }
        for (region, point) in self.borrowck_in_facts.region_live_at.iter() {
            if *point == start_point {
                write_graph!(self, "{:?} -> {:?}_{:?}", bb, bb, region);
            }
        }
        Ok(())
    }

    fn print_borrow_regions(&self) -> Result<(),io::Error> {
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
        write_graph!(self, "<th><td>{:?}</td></th>", bb);
        write_graph!(self, "<th>");
        if self.show_statement_indices() {
            write_graph!(self, "<td>Nr</td>");
        }
        write_graph!(self, "<td>statement</td>");
        write_graph!(self, "<td colspan=\"2\">Loans</td>");
        write_graph!(self, "<td colspan=\"2\">Borrow Regions</td>");
        write_graph!(self, "<td colspan=\"2\">Regions</td>");
        write_graph!(self, "</th>");

        let mir::BasicBlockData { ref statements, ref terminator, .. } = self.mir[bb];
        let mut location = mir::Location { block: bb, statement_index: 0 };
        let terminator_index = statements.len();

        while location.statement_index < terminator_index {
            self.visit_statement(location, &statements[location.statement_index])?;
            location.statement_index += 1;
        }
        let term_str = if let Some(ref term) = *terminator {
            to_html!(term.kind)
        } else {
            String::from("")
        };
        write_graph!(self, "<tr>");
        if self.show_statement_indices() {
            write_graph!(self, "<td></td>");
        }
        write_graph!(self, "<td>{}</td></tr>", term_str);
        write_graph!(self, "</table>> ];");

        if let Some(ref terminator) = *terminator {
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
                    assert!(all_loans.is_empty() || !loans.is_empty());
                    for loan in loans.iter() {
                        write_graph!(self, "{:?}_{:?} -> {:?}_{:?}",
                                     bb, region, bb, loan);
                        write_graph!(self, "subgraph cluster_{:?}_{:?} {{", bb, loan);
                        for (region, l, point) in self.borrowck_in_facts.borrow_region.iter() {
                            if loan == l {
                                write_graph!(self, "{:?}_{:?} -> {:?}_{:?}",
                                             bb, loan, bb, region);
                                let subset_map = &self.borrowck_out_facts.subset;
                                if let Some(ref subset) = subset_map.get(&point).as_ref() {
                                    for (source_region, regions) in subset.iter() {
                                        if let Some(local) = self.find_variable(*source_region) {
                                            write_graph!(self, "{:?}_{:?} -> {:?}_{:?}",
                                                         bb, local, bb, source_region);
                                        }
                                        for target_region in regions.iter() {
                                            write_graph!(self, "{:?}_{:?} -> {:?}_{:?}",
                                                         bb, source_region, bb, target_region);
                                            if let Some(local) = self.find_variable(*target_region) {
                                                write_graph!(self, "{:?}_{:?} -> {:?}_{:?}",
                                                             bb, local, bb, target_region);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        write_graph!(self, "}}");
                    }
                }
            }

            for (region, point) in self.borrowck_in_facts.region_live_at.iter() {
                if *point == start_point {
                    let variable = self.find_variable(*region).unwrap();
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
            write_graph!(self, "<td>{}</td>", to_sorted_string!(blas));
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
            TerminatorKind::Assert { target, .. } => {
                write_edge!(self, bb, target);
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
            _ => {}
        };
        Ok(())
    }

    fn show_statement_indices(&self) -> bool {
        get_config_option("PRUSTI_DUMP_SHOW_STATEMENT_INDICES", true)
    }

    fn show_temp_variables(&self) -> bool {
        get_config_option("PRUSTI_DUMP_SHOW_TEMP_VARIABLES", true)
    }
}

/// Maybe blocking analysis.
impl<'a, 'tcx> MirInfoPrinter<'a, 'tcx> {

    /// Print variables that are maybe blocked by the given variable at
    /// the start of the given location.
    fn print_blocked(&self, blocker: mir::Local, location: mir::Location) -> Result<(),io::Error> {
        let bb = location.block;
        let start_point = self.get_point(location, facts::PointType::Start);
        if let Some(region) = self.variable_regions.get(&blocker) {
            write_graph!(self, "{:?} -> {:?}_{:?}_{:?}", bb, bb, blocker, region);
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
