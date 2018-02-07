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
use rustc_mir::borrow_check::flows::{Flows};
use rustc_mir::dataflow::FlowsAtLocation;
use rustc::mir::{BasicBlockData, VisibilityScope, ARGUMENT_VISIBILITY_SCOPE};
use rustc::mir::Location;
use rustc_mir::dataflow::move_paths::HasMoveData;
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::indexed_vec::Idx;
use std::fs::File;
use std::io::{Write, BufWriter};

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
                "\"let {}{:?}: {:?}; // {} in scope {} at {}\"",
                mut_str, local, var.ty,
                name,
                source_info.scope.index(),
                tcx.sess.codemap().span_to_string(source_info.span),
            ).unwrap();
        }

        write_scope_tree(tcx, mir, scope_tree, w, child, depth + 1);

        writeln!(w, "}}").unwrap();
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
        let typ = format!("{}", mbcx.mir.local_decls[temp].ty)
            .replace("&", "&amp;")
            .replace("{", "\\{")
            .replace("}", "\\}");
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
        graph.write_all(format!("<tr><td>{:?}</td></tr>\n", bb).as_bytes()).unwrap();
        graph.write_all(format!("<tr><td>statements</td><td>original</td><td>borrows</td><td>inits</td><td>uninits</td><td>move out</td><td>ever init</td></tr>\n"
                                ).as_bytes()).unwrap();

        let BasicBlockData { ref statements, ref terminator, is_cleanup: _ } =
            mbcx.mir[bb];
        let mut location = Location { block: bb, statement_index: 0 };

        debug!("--------------------");
        debug!("--------------------");
        debug!("--------------------");
        debug!("--------------------");

        for stmt in statements.iter() {
            flows.reconstruct_statement_effect(location);
            //self.visit_statement_entry(location, stmt, flow_state);
            debug!("location={:?} stmt={:?}", location, stmt);
            let source_info = stmt.source_info;
            let stmt_str = format!("{:?}", stmt).replace("&", "&amp;").replace("{", "\\{").replace("}", "\\}");
            graph.write_all(format!("<tr><td>{}</td>", stmt_str).as_bytes()).unwrap();

            let snippet = if let Some(snippet) = mbcx.tcx.sess.codemap().span_to_snippet(source_info.span).ok() {
                snippet.replace("{", "\\{").replace("}", "\\}").replace("&", "&amp;")
            } else {
                String::from("")
            };
            graph.write_all(format!("<td>{}</td>", snippet).as_bytes()).unwrap();

            debug!("borrows in effect:");
            graph.write_all(format!("<td>").as_bytes()).unwrap();
            flows.borrows.each_state_bit(|borrow| {
                let borrow_data = &flows.borrows.operator().borrows()[borrow.borrow_index()];
                debug!("{}{}", borrow_data,
                       if borrow.is_activation() { "@active" } else { "" });
                let borrow = format!(" {}, ", borrow_data).replace("&", "&amp;");
                graph.write_all(borrow.as_bytes()).unwrap();
            });

            graph.write_all(format!("\\|").as_bytes()).unwrap();
            flows.borrows.each_gen_bit(|borrow| {
                let borrow_data = &flows.borrows.operator().borrows()[borrow.borrow_index()];
                debug!("{}", borrow_data);
                let borrow = format!(" {}, ", borrow_data).replace("&", "&amp;");
                graph.write_all(borrow.as_bytes()).unwrap();
            });
            graph.write_all(format!("</td>").as_bytes()).unwrap();

            debug!("inits:");
            graph.write_all(format!("<td>").as_bytes()).unwrap();
            flows.inits.each_state_bit(|mpi_init| {
                let move_path = &flows.inits.operator().move_data().move_paths[mpi_init];
                debug!("{}", move_path);
                graph.write_all(format!(" {}, ", move_path).as_bytes()).unwrap();
            });
            graph.write_all(format!("</td>").as_bytes()).unwrap();

            debug!("uninits:");
            graph.write_all(format!("<td>").as_bytes()).unwrap();
            flows.uninits.each_state_bit(|mpi_uninit| {
                let move_path =
                    &flows.uninits.operator().move_data().move_paths[mpi_uninit];
                debug!("{}", move_path);
                graph.write_all(format!(" {}, ", move_path).as_bytes()).unwrap();
            });
            graph.write_all(format!("</td>").as_bytes()).unwrap();

            debug!("move_out:");
            graph.write_all(format!("<td>").as_bytes()).unwrap();
            flows.move_outs.each_state_bit(|mpi_move_out| {
                let move_out = &flows.move_outs.operator().move_data().moves[mpi_move_out];
                debug!("{:?}", move_out);
                graph.write_all(format!(" {:?}, ", move_out).as_bytes()).unwrap();
            });
            graph.write_all(format!("</td>").as_bytes()).unwrap();

            debug!("ever_init:");
            graph.write_all(format!("<td>").as_bytes()).unwrap();
            flows.ever_inits.each_state_bit(|mpi_ever_init| {
                let ever_init =
                    &flows.ever_inits.operator().move_data().inits[mpi_ever_init];
                debug!("{:?}", ever_init);
                graph.write_all(format!(" {:?}, ", ever_init).as_bytes()).unwrap();
            });
            graph.write_all(format!("</td>").as_bytes()).unwrap();

            graph.write_all(format!("</tr>\n").as_bytes()).unwrap();

            flows.apply_local_effect(location);
            location.statement_index += 1;
        }
        graph.write_all(format!("</table>> ];\n").as_bytes()).unwrap();

        if let Some(ref term) = *terminator {
            flows.reconstruct_terminator_effect(location);
            //self.visit_terminator_entry(location, term, flow_state);
            debug!("location={:?} term={:?} flows={}", location, term, flows);
            use rustc::mir::TerminatorKind;
            match term.kind {
                TerminatorKind::Goto { target } => {
                    graph.write_all(format!("\"{:?}\" -> \"{:?}\"\n", bb, target).as_bytes()).unwrap();
                },
                TerminatorKind::SwitchInt { ref targets, ..} => {
                    for target in targets {
                        graph.write_all(format!("\"{:?}\" -> \"{:?}\"\n", bb, target).as_bytes()).unwrap();
                    }
                },
                TerminatorKind::Resume => {
                    graph.write_all(format!("\"{:?}\" -> \"Resume\"\n", bb).as_bytes()).unwrap();
                },
                TerminatorKind::Abort => {
                    graph.write_all(format!("\"{:?}\" -> \"Abort\"\n", bb).as_bytes()).unwrap();
                },
                TerminatorKind::Return => {
                    graph.write_all(format!("\"{:?}\" -> \"Return\"\n", bb).as_bytes()).unwrap();
                },
                TerminatorKind::Unreachable => {unimplemented!()},
                TerminatorKind::Drop {..} => {unimplemented!()},
                TerminatorKind::DropAndReplace {..} => {unimplemented!()},
                TerminatorKind::Call { ref destination, cleanup, ..} => {
                    if let &Some((_, target)) = destination {
                        graph.write_all(format!("\"{:?}\" -> \"{:?}\"\n", bb, target).as_bytes()).unwrap();
                    }
                    if let Some(target) = cleanup {
                        graph.write_all(format!("\"{:?}\" -> \"{:?}\" [color=red]\n",
                                                bb, target).as_bytes()).unwrap();
                    }
                },
                TerminatorKind::Assert { target, .. } => {
                    graph.write_all(format!("\"{:?}\" -> \"{:?}\"\n", bb, target).as_bytes()).unwrap();
                },
                TerminatorKind::Yield {..} => {unimplemented!()},
                TerminatorKind::GeneratorDrop => {unimplemented!()},
                TerminatorKind::FalseEdges {..} => {unimplemented!()},
            };
        }
    }
    graph.write_all(b"}").unwrap();
    trace!("[callback] exit");
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

        let input_mir = self.tcx.mir_validated(def_id);
        let opt_closure_req = self.tcx.infer_ctxt().enter(|infcx| {
            let input_mir: &Mir = &input_mir.borrow();
            //let callback: for<'s> Fn(&'s _, &'s _) = |_mbcx, _state| {};
            do_mir_borrowck(&infcx, input_mir, def_id, Some(box callback))
        });

        //let mir = self.tcx.mir_validated(def_id);
        //let mir = mir.borrow();
        trace!("[visit_fn] exit");
    }
}
