// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A module that invokes the verifier `prusti-viper`

use specifications::TypedSpecificationMap;
use prusti_viper::verifier::VerifierBuilder as ViperVerifierBuilder;
//use prusti_interface::verifier::VerifierBuilder;
//use prusti_interface::verifier::VerificationContext;
//use prusti_interface::verifier::Verifier;
//use prusti_interface::data::VerificationTask;
//use prusti_interface::data::VerificationResult;
use rustc_driver::driver;
use rustc::hir::{self, intravisit};
use rustc::ty::TyCtxt;
use syntax::{self, ast, parse, ptr};
use syntax::codemap::Span;
use environment::Environment;
use hir_visitor::HirVisitor;
use rustc::ty::TyCtxt;
use rustc::hir;

/// Verify a (typed) specification on compiler state.
pub fn verify<'r, 'a: 'r, 'tcx: 'a>(
    state: &'r mut driver::CompileState<'a, 'tcx>,
    spec: TypedSpecificationMap,
) {
    trace!("[verify] enter");

    debug!("Specification consists of {} elements.", spec.len());

    let tcx = state.tcx.unwrap();
    assert!(tcx.sess.nll());
    let mut printer = InfoPrinter {
        tcx: tcx,
    };
    intravisit::walk_crate(&mut printer, tcx.hir.krate());

    let tcx: TyCtxt = env.tcx();

    let krate: &hir::Crate = tcx.hir.krate();

    let mut hir_visitor = HirVisitor::new(tcx, &spec);
    krate.visit_all_item_likes(&mut hir_visitor);

    //env.dump();

    //let verification_task = VerificationTask { procedures: vec![] };

    //debug!("Prepare verifier...");
    //let verifier_builder = ViperVerifierBuilder::new();
    //let verification_context = verifier_builder.new_verification_context();
    //let mut verifier = verification_context.new_verifier();

    //debug!("Run verifier...");
    //let verification_result = verifier.verify(&mut env, &verification_task);
    //debug!("Verifier returned {:?}", verification_result);

    //match verification_result {
    //VerificationResult::Success => info!("Prusti verification succeded"),
    //VerificationResult::Failure => env.err("Prusti verification failed"),
    //};

    trace!("[verify] exit");
}


struct InfoPrinter<'a, 'tcx: 'a> {
    pub tcx: TyCtxt<'a, 'tcx, 'tcx>,
}


use rustc::mir::{Mir, Mutability, Operand, Projection, ProjectionElem, Rvalue};
use rustc_mir::borrow_check::{MirBorrowckCtxt, do_mir_borrowck};
use rustc_mir::borrow_check::flows::Flows;
use rustc_mir::borrow_check::prefixes::*;
use rustc_mir::dataflow::FlowsAtLocation;
use rustc::mir::{BasicBlockData, VisibilityScope, ARGUMENT_VISIBILITY_SCOPE};
use rustc::mir::Location;
use rustc::mir::Place;
use rustc::mir::BorrowKind;
use rustc_mir::dataflow::move_paths::HasMoveData;
use rustc_mir::dataflow::move_paths::MovePath;
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::indexed_vec::Idx;
use std::fs::File;
use std::io::{Write, BufWriter};
use rustc_mir::dataflow::move_paths::MoveOut;
use std::collections::HashSet;
use rustc_mir::dataflow::BorrowData;
use rustc::ty::Region;
use std::fmt;

fn write_scope_tree(
    tcx: TyCtxt,
    mir: &Mir,
    scope_tree: &FxHashMap<VisibilityScope, Vec<VisibilityScope>>,
    w: &mut Write,
    parent: VisibilityScope,
    depth: usize,
) {
    let children = match scope_tree.get(&parent) {
        Some(childs) => childs,
        None => return,
    };

    for &child in children {
        let data = &mir.visibility_scopes[child];
        assert_eq!(data.parent_scope, Some(parent));
        writeln!(w, "subgraph clusterscope{} {{", child.index()).unwrap();

        // User variable types (including the user's name in a comment).
        for local in mir.vars_iter() {
            let var = &mir.local_decls[local];
            let (name, source_info) = if var.source_info.scope == child {
                (var.name.unwrap(), var.source_info)
            } else {
                // Not a variable or not declared in this scope.
                continue;
            };

            let mut_str = if var.mutability == Mutability::Mut {
                "mut "
            } else {
                ""
            };

            writeln!(w,
                     "\"// {} in scope {} at {}\\nlet {}{:?}: {:?};\"",
                     name,
                     source_info.scope.index(),
                     tcx.sess.codemap().span_to_string(source_info.span),
                     mut_str, local, var.ty,
            ).unwrap();
        }

        write_scope_tree(tcx, mir, scope_tree, w, child, depth + 1);

        writeln!(w, "}}").unwrap();
    }
}

use std::hash::{Hash, Hasher, SipHasher};

#[derive(Clone, PartialEq, Eq)]
struct OurBorrowData<'tcx> {
    kind: BorrowKind,
    region: Region<'tcx>,
    borrowed_place: Place<'tcx>,
    assigned_place: Place<'tcx>,
}

impl<'tcx> OurBorrowData<'tcx> {
    fn kind_str(&self) -> String {
        match self.kind {
            BorrowKind::Shared => "",
            BorrowKind::Unique => "uniq ",
            BorrowKind::Mut { .. } => "mut ",
        }.to_string()
    }
}

impl<'tcx> fmt::Debug for OurBorrowData<'tcx> {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        write!(w, "&{}{}{:?}", self.region, self.kind_str(), self.borrowed_place)
    }
}

impl<'tcx> Hash for OurBorrowData<'tcx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.region.hash(state);
        self.kind_str().hash(state);
        self.borrowed_place.hash(state);
    }
}

fn callback<'s>(mbcx: &'s mut MirBorrowckCtxt, flows: &'s mut Flows) {
    trace!("[callback] enter");
    debug!("flows: {}", flows);
    //debug!("MIR: {:?}", mbcx.mir);
    let mut graph = File::create("graph.dot").expect("Unable to create file");
    let mut graph = BufWriter::new(graph);
    graph.write_all(b"digraph G {\n").unwrap();
    writeln!(graph, "graph [compound=true];").unwrap();

    let show_source = false;
    let show_definitely_init = false;
    let show_unknown_init = false;
    let show_reserved_borrows = true;
    let show_active_borrows = true;
    let show_move_out = true;
    let show_ever_init = false;

    // Scope tree.
    let mut scope_tree: FxHashMap<VisibilityScope, Vec<VisibilityScope>> = FxHashMap();
    for (index, scope_data) in mbcx.mir.visibility_scopes.iter().enumerate() {
        if let Some(parent) = scope_data.parent_scope {
            scope_tree
                .entry(parent)
                .or_insert(vec![])
                .push(VisibilityScope::new(index));
        } else {
            // Only the argument scope has no parent, because it's the root.
            assert_eq!(index, ARGUMENT_VISIBILITY_SCOPE.index());
        }
    }
    writeln!(graph, "subgraph clusterscopes {{ style=filled;").unwrap();
    writeln!(graph, "SCOPE_TREE").unwrap();
    write_scope_tree(mbcx.tcx, &mbcx.mir, &scope_tree, &mut graph, ARGUMENT_VISIBILITY_SCOPE, 1);
    writeln!(graph, "}}").unwrap();

    // Temporary variables.
    writeln!(graph, "VARIABLES [ style=filled shape = \"record\"").unwrap();
    writeln!(graph, "label =<<table>").unwrap();
    writeln!(graph, "<tr><td>VARIABLES</td></tr>").unwrap();
    writeln!(graph, "<tr><td>Name</td><td>Temporary</td><td>Type</td></tr>").unwrap();
    for temp in mbcx.mir.vars_and_temps_iter() {
        let var = &mbcx.mir.local_decls[temp];
        let name = var.name.map(|s| s.to_string()).unwrap_or(String::from(""));
        let typ = escape_html(format!("{}", mbcx.mir.local_decls[temp].ty));
        writeln!(graph, "<tr><td>{}</td><td>{:?}</td><td>{}</td></tr>", name, temp, typ).unwrap();
    }
    writeln!(graph, "</table>>];").unwrap();

    // CFG
    graph.write_all(format!("Resume\n").as_bytes()).unwrap();
    graph.write_all(format!("Abort\n").as_bytes()).unwrap();
    graph.write_all(format!("Return\n").as_bytes()).unwrap();
    for bb in mbcx.mir.basic_blocks().indices() {
        flows.reset_to_entry_of(bb);

        graph.write_all(format!("\"{:?}\" [ shape = \"record\" \n", bb).as_bytes()).unwrap();
        graph.write_all(format!("label =<<table>\n").as_bytes()).unwrap();
        graph.write_all(format!("<th><td>{:?}</td></th>\n", bb).as_bytes()).unwrap();
        graph.write_all(format!("<th><td>statement</td>").as_bytes()).unwrap();
        if show_source { graph.write_all(format!("<td>source</td>").as_bytes()).unwrap(); }
        if show_definitely_init { graph.write_all(format!("<td>definitely init</td>").as_bytes()).unwrap(); }
        if show_unknown_init { graph.write_all(format!("<td>unknown init</td>").as_bytes()).unwrap(); }
        if show_reserved_borrows { graph.write_all(format!("<td>reserved borrows</td>").as_bytes()).unwrap(); }
        if show_active_borrows { graph.write_all(format!("<td>active borrows</td>").as_bytes()).unwrap(); }
        if show_move_out { graph.write_all(format!("<td>move out</td>").as_bytes()).unwrap(); }
        if show_ever_init { graph.write_all(format!("<td>ever init</td>").as_bytes()).unwrap(); }
        graph.write_all(format!("</th>\n").as_bytes()).unwrap();

        let BasicBlockData { ref statements, ref terminator, is_cleanup: _ } =
            mbcx.mir[bb];
        let mut location = Location { block: bb, statement_index: 0 };
        let mut first_run = true;

        debug!("--------------------");
        debug!("--------------------");
        debug!("--------------------");
        debug!("--------------------");

        let terminator_index = statements.len();

        while first_run || location.statement_index <= terminator_index {
            if first_run {
                debug!("location={:?}", bb);
            } else {
                debug!("location={:?}", location);
            }
            graph.write_all(format!("<tr>").as_bytes()).unwrap();

            if first_run {
                graph.write_all(format!("<td colspan=\"{}\">(initial state)</td>", if show_source { 2 } else { 1 }).as_bytes()).unwrap();
            } else if location.statement_index == terminator_index {
                debug!("term={:?}", terminator);
                flows.reconstruct_terminator_effect(location);
                flows.apply_local_effect(location);
                let term_str = if let Some(ref term) = *terminator {
                    escape_html(format!("{:?}", term.kind))
                } else {
                    String::from("")
                };
                graph.write_all(format!("<td colspan=\"{}\">{}</td>", if show_source { 2 } else { 1 }, term_str).as_bytes()).unwrap();
            } else {
                let stmt = &statements[location.statement_index];
                debug!("stmt={:?}", stmt);
                flows.reconstruct_statement_effect(location);
                flows.apply_local_effect(location);
                //self.visit_statement_entry(location, stmt, flow_state);
                let source_info = stmt.source_info;
                let stmt_str = escape_html(format!("{:?}", stmt));
                graph.write_all(format!("<td>{}</td>", stmt_str).as_bytes()).unwrap();

                if show_source {
                    let snippet = if let Some(snippet) = mbcx.tcx.sess.codemap().span_to_snippet(source_info.span).ok() {
                        escape_html(snippet)
                    } else {
                        String::from("")
                    };
                    graph.write_all(format!("<td>{}</td>", snippet).as_bytes()).unwrap();
                }
            }

            let mut maybe_init: HashSet<Place> = HashSet::new();
            let mut maybe_uninit: HashSet<Place> = HashSet::new();

            debug!("maybe initialised:");
            flows.inits.each_state_bit(|mpi_init| {
                let move_data = &flows.inits.operator().move_data();
                let move_path = &move_data.move_paths[mpi_init];
                let place = &move_path.place;
                maybe_init.insert(place.clone());
                debug!("  state: {:?} - {:?}", place, move_path);
            });

            debug!("maybe uninitialised:");
            flows.uninits.each_state_bit(|mpi_uninit| {
                let move_data = &flows.uninits.operator().move_data();
                let move_path = &move_data.move_paths[mpi_uninit];
                let place = &move_path.place;
                maybe_uninit.insert(place.clone());
                debug!("  state: {:?} - {:?}", place, move_path);
            });

            let definitely_init: HashSet<Place> = maybe_init.difference(&maybe_uninit).cloned().collect();
            let unknown_init: HashSet<Place> = maybe_init.intersection(&maybe_uninit).cloned().collect();
            let definitely_uninit: HashSet<Place> = maybe_uninit.difference(&maybe_init).cloned().collect();

            debug!("definitely initialised:");
            for place in &definitely_init {
                debug!("  state: {:?}", place);
            }
            if show_definitely_init {
                graph.write_all(format!("<td>").as_bytes()).unwrap();
                graph.write_all(escape_html(
                    definitely_init.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
                ).as_bytes()).unwrap();
                graph.write_all(format!("</td>").as_bytes()).unwrap();
            }

            debug!("unknown initialisation:");
            for place in &unknown_init {
                debug!("  state: {:?}", place);
            }
            if show_unknown_init {
                graph.write_all(format!("<td>").as_bytes()).unwrap();
                graph.write_all(escape_html(
                    unknown_init.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
                ).as_bytes()).unwrap();
                graph.write_all(format!("</td>").as_bytes()).unwrap();
            }

            let mut borrows_gen: HashSet<Place> = HashSet::new();
            let mut borrows_kill: HashSet<Place> = HashSet::new();
            let mut reserved_borrows: HashSet<OurBorrowData> = HashSet::new();
            let mut active_borrows: HashSet<OurBorrowData> = HashSet::new();

            debug!("borrows:");
            flows.borrows.each_gen_bit(|borrow| {
                let borrow_data = &flows.borrows.operator().borrows()[borrow.borrow_index()];
                debug!("  gen: {}", &borrow_data);
                borrows_gen.insert(borrow_data.borrowed_place.clone());
            });
            flows.borrows.each_kill_bit(|borrow| {
                let borrow_data = &flows.borrows.operator().borrows()[borrow.borrow_index()];
                debug!("  kill: {}", &borrow_data);
                borrows_kill.insert(borrow_data.borrowed_place.clone());
            });

            flows.borrows.each_state_bit(|borrow| {
                let borrows = &flows.borrows.operator();
                //debug!("  assigned_map: {:?}", &borrows.0.assigned_map);
                let borrow_data = &borrows.borrows()[borrow.borrow_index()];
                let our_borrow_data = OurBorrowData {
                    kind: borrow_data.kind.clone(),
                    region: borrow_data.region,
                    borrowed_place: borrow_data.borrowed_place.clone(),
                    assigned_place: borrow_data.assigned_place.clone(),
                };
                if borrow.is_activation() {
                    debug!("  state: ({:?} =) {} @active", &borrow_data.assigned_place, &borrow_data);
                    active_borrows.insert(our_borrow_data);
                } else {
                    debug!("  state: ({:?} =) {}", &borrow_data.assigned_place, &borrow_data);
                    reserved_borrows.insert(our_borrow_data);
                }
            });

            if show_reserved_borrows {
                graph.write_all(format!("<td>").as_bytes()).unwrap();
                graph.write_all(escape_html(
                    reserved_borrows.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
                ).as_bytes()).unwrap();
                graph.write_all(format!("</td>").as_bytes()).unwrap();
            }

            if show_active_borrows {
                graph.write_all(format!("<td>").as_bytes()).unwrap();
                graph.write_all(escape_html(
                    active_borrows.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
                ).as_bytes()).unwrap();
                graph.write_all(format!("</td>").as_bytes()).unwrap();
            }

            let mut move_out: HashSet<Place> = HashSet::new();
            let mut ever_init: HashSet<Place> = HashSet::new();

            debug!("moved out:");
            flows.move_outs.each_state_bit(|mpi_move_out| {
                let move_data = &flows.move_outs.operator().move_data();
                let move_out_data = &move_data.moves[mpi_move_out];
                let mut move_path_index = move_out_data.path;
                let mut move_path = &move_data.move_paths[move_path_index];
                let place = &move_path.place;
                debug!("  state: {:?} - {:?}", place, move_out_data);
                move_out.insert(place.clone());
            });

            debug!("ever init:");
            flows.ever_inits.each_state_bit(|mpi_ever_init| {
                let move_data = &flows.ever_inits.operator().move_data();
                let ever_init_data = move_data.inits[mpi_ever_init];
                let move_path = &move_data.move_paths[ever_init_data.path];
                let place = &move_path.place;
                debug!("  state: {:?} - {:?}", place, ever_init_data);
                ever_init.insert(place.clone());
            });

            assert!(places_leq(&maybe_init, &ever_init), "maybe_init <= ever_init does not hold");

            if show_move_out {
                graph.write_all(format!("<td>").as_bytes()).unwrap();
                graph.write_all(escape_html(
                    move_out.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
                ).as_bytes()).unwrap();
                graph.write_all(format!("</td>").as_bytes()).unwrap();
            }

            if show_ever_init {
                graph.write_all(format!("<td>").as_bytes()).unwrap();
                graph.write_all(escape_html(
                    ever_init.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
                ).as_bytes()).unwrap();
                graph.write_all(format!("</td>").as_bytes()).unwrap();
            }

            graph.write_all(format!("</tr>\n").as_bytes()).unwrap();

            if first_run {
                first_run = false;
            } else {
                location.statement_index += 1;
            }
        }

        graph.write_all(format!("</table>> ];\n").as_bytes()).unwrap();

        if let Some(ref term) = *terminator {
            use rustc::mir::TerminatorKind;
            match term.kind {
                TerminatorKind::Goto { target } => {
                    graph.write_all(format!("\"{:?}\" -> \"{:?}\"\n", bb, target).as_bytes()).unwrap();
                }
                TerminatorKind::SwitchInt { ref targets, .. } => {
                    for target in targets {
                        graph.write_all(format!("\"{:?}\" -> \"{:?}\"\n", bb, target).as_bytes()).unwrap();
                    }
                }
                TerminatorKind::Resume => {
                    graph.write_all(format!("\"{:?}\" -> \"Resume\"\n", bb).as_bytes()).unwrap();
                }
                TerminatorKind::Abort => {
                    graph.write_all(format!("\"{:?}\" -> \"Abort\"\n", bb).as_bytes()).unwrap();
                }
                TerminatorKind::Return => {
                    graph.write_all(format!("\"{:?}\" -> \"Return\"\n", bb).as_bytes()).unwrap();
                }
                TerminatorKind::Unreachable => {}
                TerminatorKind::DropAndReplace { ref target, unwind, .. } |
                TerminatorKind::Drop { ref target, unwind, .. } => {
                    graph.write_all(format!("\"{:?}\" -> \"{:?}\"\n", bb, target).as_bytes()).unwrap();
                    if let Some(target) = unwind {
                        graph.write_all(format!("\"{:?}\" -> \"{:?}\" [color=red]\n",
                                                bb, target).as_bytes()).unwrap();
                    }
                }

                TerminatorKind::Call { ref destination, cleanup, .. } => {
                    if let &Some((_, target)) = destination {
                        graph.write_all(format!("\"{:?}\" -> \"{:?}\"\n", bb, target).as_bytes()).unwrap();
                    }
                    if let Some(target) = cleanup {
                        graph.write_all(format!("\"{:?}\" -> \"{:?}\" [color=red]\n",
                                                bb, target).as_bytes()).unwrap();
                    }
                }
                TerminatorKind::Assert { target, .. } => {
                    graph.write_all(format!("\"{:?}\" -> \"{:?}\"\n", bb, target).as_bytes()).unwrap();
                }
                TerminatorKind::Yield { .. } => { unimplemented!() }
                TerminatorKind::GeneratorDrop => { unimplemented!() }
                TerminatorKind::FalseEdges { ref real_target, ref imaginary_targets } => {
                    graph.write_all(format!("\"{:?}\" -> \"{:?}\"\n", bb, real_target).as_bytes()).unwrap();
                    for target in imaginary_targets {
                        graph.write_all(format!("\"{:?}\" -> \"{:?}\" [style=\"dashed\"]\n", bb, target).as_bytes()).unwrap();
                    }
                }
                TerminatorKind::FalseUnwind { real_target, unwind } => {
                    graph.write_all(format!("\"{:?}\" -> \"{:?}\"\n", bb, real_target).as_bytes()).unwrap();
                    if let Some(target) = unwind {
                        graph.write_all(format!("\"{:?}\" -> \"{:?}\" [style=\"dashed\"]\n",
                                                bb, target).as_bytes()).unwrap();
                    }
                }
            };
        }
    }
    graph.write_all(b"}").unwrap();
    trace!("[callback] exit");
}

fn escape_html<S: Into<String>>(s: S) -> String {
    s.into()
        .replace("{", "\\{")
        .replace("}", "\\}")
        .replace("&", "&amp;")
        .replace(">", "&gt;")
        .replace("<", "&lt;")
        .replace("\n", "<br/>")
}

/// Returns true if place `a` is contained in place `b`.
/// That is, if `b` is a prefix of `a`.
fn place_leq(a: &Place, b: &Place) -> bool {
    b.is_prefix_of(a)
}

/// Returns true if place `x` is contained in one of the places of `places`.
/// That is, if some place of `places` is a prefix of `x`.
/// That is, if `{x} <= places`.
fn is_place_in_set(x: &Place, places: &HashSet<Place>) -> bool {
    for place in places.iter() {
        if place.is_prefix_of(x) {
            return true;
        }
    }
    return false;
}

/// Returns true if the places `a` are contained in the places `b`.
/// That is, if each place of `a` is contained in some place of `b`.
/// That is, if `a <= b`.
fn places_leq(a: &HashSet<Place>, b: &HashSet<Place>) -> bool {
    for item in a.iter() {
        if !is_place_in_set(item, b) {
            return false;
        }
    }
    return true;
}

impl<'a, 'tcx: 'a, 'hir> intravisit::Visitor<'tcx> for InfoPrinter<'a, 'tcx> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'tcx> {
        let map = &self.tcx.hir;
        intravisit::NestedVisitorMap::All(map)
    }

    fn visit_fn(&mut self, fk: intravisit::FnKind<'tcx>, _fd: &'tcx hir::FnDecl,
                _b: hir::BodyId, _s: Span, node_id: ast::NodeId) {
        let name = match fk {
            intravisit::FnKind::ItemFn(name, ..) => name,
            _ => unimplemented!(),
        };
        if name != "main" {
            return;
        }
        trace!("[visit_fn] enter name={:?}", name);
        let def_id = self.tcx.hir.local_def_id(node_id);
        //self.tcx.mir_borrowck(def_id);

//        let input_mir = self.tcx.mir_validated(def_id);
        let input_mir = self.tcx.optimized_mir(def_id);
        let opt_closure_req = self.tcx.infer_ctxt().enter(|infcx| {
            let input_mir: &Mir = &input_mir;
            //let callback: for<'s> Fn(&'s _, &'s _) = |_mbcx, _state| {};
            do_mir_borrowck(&infcx, input_mir, def_id, Some(box
                callback))
        });

        //let mir = self.tcx.mir_validated(def_id);
        //let mir = mir.borrow();
        trace!("[visit_fn] exit");
    }
}
