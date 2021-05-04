use log::{debug, trace};
use prusti_common::config;
use rustc_hir as hir;
use rustc_hir::{def_id::DefId, itemlikevisit::ItemLikeVisitor};
use rustc_middle::{mir, ty::TyCtxt};
use std::{
    collections::HashMap,
    fs::File,
    io::{self, BufWriter, Write},
    path::PathBuf,
};

pub(super) fn dump_lifetime_info<'tcx>(tcx: TyCtxt<'tcx>) {
    trace!("[dump_lifetime_info] enter");

    // Collect all procedures.
    let mut visitor = ProcedureCollector {
        tcx,
        procedures: Vec::new(),
    };
    tcx.hir().krate().visit_all_item_likes(&mut visitor);

    // Print info about each procedure.
    for def_id in visitor.procedures {
        print_info(tcx, def_id);
    }

    trace!("[dump_lifetime_info] exit");
}

struct ProcedureCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    procedures: Vec<DefId>,
}

impl<'tcx> ItemLikeVisitor<'tcx> for ProcedureCollector<'tcx> {
    fn visit_item(&mut self, item: &hir::Item) {
        if let hir::ItemKind::Fn(..) = item.kind {
            let def_id = self.tcx.hir().local_def_id(item.hir_id()).to_def_id();
            self.procedures.push(def_id);
        }
    }

    fn visit_trait_item(&mut self, trait_item: &hir::TraitItem) {
        // Skip associated types and other non-methods items
        if let hir::TraitItemKind::Fn(..) = trait_item.kind {
            // continue
        } else {
            return;
        }
        // Skip body-less trait methods
        if let hir::TraitItemKind::Fn(_, hir::TraitFn::Required(_)) = trait_item.kind {
            return;
        }
        let def_id = self.tcx.hir().local_def_id(trait_item.hir_id()).to_def_id();
        self.procedures.push(def_id);
    }

    fn visit_impl_item(&mut self, impl_item: &hir::ImplItem) {
        // Skip associated types and other non-methods items
        if let hir::ImplItemKind::Fn(..) = impl_item.kind {
            // continue
        } else {
            return;
        }
        let def_id = self.tcx.hir().local_def_id(impl_item.hir_id()).to_def_id();
        self.procedures.push(def_id);
    }

    fn visit_foreign_item(&mut self, _foreign_item: &hir::ForeignItem) {
        // Nothing
    }
}

/// Print info about the procedure with the given `def_id`.
fn print_info<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) {
    trace!("[print_info] enter {:?}", def_id);

    let local_def_id = def_id.expect_local();
    let def_path = tcx.hir().def_path(local_def_id);
    let output_path = PathBuf::from(config::log_dir())
        .join("nll-facts")
        .join(def_path.to_filename_friendly_no_crate())
        .join("output_lifetime.dot");
    debug!("Writing output to {:?}", output_path);
    let output_file = File::create(output_path).expect("Unable to create file");
    let output = std::cell::RefCell::new(BufWriter::new(output_file));

    let mir = tcx.optimized_mir(def_id);

    let info_printer = InfoPrinter { tcx, output, mir };
    info_printer.print_info().unwrap();

    trace!("[print_info] exit {:?}", def_id);
}

struct InfoPrinter<'a, 'tcx: 'a> {
    tcx: TyCtxt<'tcx>,
    output: std::cell::RefCell<BufWriter<File>>,
    mir: &'a mir::Body<'tcx>,
}

macro_rules! write_graph {
    ( $self:ident, $( $x:expr ),* ) => {
        writeln!($self.output.borrow_mut(), $( $x ),*)?;
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
        write_graph!(
            $self,
            "\"{:?}\" -> \"{:?}\" [color=red]\n",
            $source,
            $target
        );
    }};
    ( $self:ident, $source:ident, imaginary $target:ident ) => {{
        write_graph!(
            $self,
            "\"{:?}\" -> \"{:?}\" [style=\"dashed\"]\n",
            $source,
            $target
        );
    }};
    ( $self:ident, $source:ident, $target:ident ) => {{
        write_graph!($self, "\"{:?}\" -> \"{:?}\"\n", $source, $target);
    }};
}

impl<'a, 'tcx> InfoPrinter<'a, 'tcx> {
    pub fn print_info(mut self) -> Result<(), io::Error> {
        write_graph!(self, "digraph G {{\n");

        for bb in self.mir.basic_blocks().indices() {
            self.visit_basic_block(bb)?;
        }
        self.print_temp_variables()?;

        write_graph!(self, "}}\n");

        // flush
        self.output.into_inner().into_inner().unwrap();

        Ok(())
    }

    fn print_temp_variables(&self) -> Result<(), io::Error> {
        write_graph!(self, "Variables [ style=filled shape = \"record\"");
        write_graph!(self, "label =<<table>");
        write_graph!(self, "<tr><td>VARIABLES</td></tr>");
        write_graph!(
            self,
            "<tr><td>Name</td><td>Temporary</td><td>Type</td><td>Region</td></tr>"
        );
        let mut var_names = HashMap::new();
        for info in &self.mir.var_debug_info {
            if let mir::VarDebugInfoContents::Place(place) = info.value {
                if let Some(local) = place.as_local() {
                    var_names.insert(local, info.name);
                } else {
                    unimplemented!();
                }
            } else {
                unimplemented!();
            }
        }
        for (temp, var) in self.mir.local_decls.iter_enumerated() {
            let name = var_names
                .get(&temp)
                .map(|s| s.to_string())
                .unwrap_or(String::from(""));
            let region = "todo";
            //self
            // .polonius_info
            // .place_regions
            // .for_local(temp)
            // .map(|region| format!("{:?}", region))
            // .unwrap_or(String::from(""));
            let typ = to_html!(var.ty);
            write_graph!(
                self,
                "<tr><td>{}</td><td>{:?}</td><td>{}</td><td>{}</td></tr>",
                name,
                temp,
                typ,
                region
            );
        }
        write_graph!(self, "</table>>];");
        Ok(())
    }

    fn visit_basic_block(&mut self, bb: mir::BasicBlock) -> Result<(), io::Error> {
        write_graph!(self, "\"{:?}\" [ shape = \"record\"", bb);
        write_graph!(self, "label =<<table>");
        write_graph!(self, "<th>");
        write_graph!(self, "<td>{:?}</td>", bb);
        write_graph!(self, "<td></td>");
        write_graph!(self, "</th>");

        write_graph!(self, "<th>");
        write_graph!(self, "<td>Nr</td>");
        write_graph!(self, "<td>statement</td>");
        write_graph!(self, "</th>");

        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = self.mir[bb];
        let mut location = mir::Location {
            block: bb,
            statement_index: 0,
        };
        let terminator_index = statements.len();

        while location.statement_index < terminator_index {
            self.visit_statement(location, &statements[location.statement_index])?;
            location.statement_index += 1;
        }
        let term_str = if let Some(ref term) = &terminator {
            to_html!(term.kind)
        } else {
            String::from("")
        };
        write_graph!(self, "<tr>");
        write_graph!(self, "<td></td>");
        write_graph!(self, "<td>{}</td>", term_str);
        write_graph!(self, "</tr>");
        write_graph!(self, "</table>> ];");

        if let Some(terminator) = terminator {
            self.visit_terminator(bb, terminator)?;
        }

        Ok(())
    }

    fn visit_statement(
        &self,
        location: mir::Location,
        statement: &mir::Statement,
    ) -> Result<(), io::Error> {
        write_graph!(self, "<tr>");
        write_graph!(self, "<td>{}</td>", location.statement_index);
        write_graph!(self, "<td>{}</td>", to_html!(statement));
        write_graph!(self, "</tr>");
        Ok(())
    }

    fn visit_terminator(
        &self,
        bb: mir::BasicBlock,
        terminator: &mir::Terminator,
    ) -> Result<(), io::Error> {
        use rustc_middle::mir::TerminatorKind;
        match terminator.kind {
            TerminatorKind::Goto { target } => {
                write_edge!(self, bb, target);
            }
            TerminatorKind::SwitchInt { ref targets, .. } => {
                for target in targets.all_targets() {
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
            TerminatorKind::DropAndReplace {
                ref target, unwind, ..
            }
            | TerminatorKind::Drop {
                ref target, unwind, ..
            } => {
                write_edge!(self, bb, target);
                if let Some(target) = unwind {
                    write_edge!(self, bb, unwind target);
                }
            }
            TerminatorKind::Call {
                ref destination,
                cleanup,
                ..
            } => {
                if let &Some((_, target)) = destination {
                    write_edge!(self, bb, target);
                }
                if let Some(target) = cleanup {
                    write_edge!(self, bb, unwind target);
                }
            }
            TerminatorKind::Assert {
                target, cleanup, ..
            } => {
                write_edge!(self, bb, target);
                if let Some(target) = cleanup {
                    write_edge!(self, bb, unwind target);
                }
            }
            TerminatorKind::Yield { .. } => unimplemented!(),
            TerminatorKind::GeneratorDrop => unimplemented!(),
            TerminatorKind::FalseEdge {
                ref real_target,
                ref imaginary_target,
            } => {
                write_edge!(self, bb, real_target);
                write_edge!(self, bb, imaginary_target);
            }
            TerminatorKind::FalseUnwind {
                real_target,
                unwind,
            } => {
                write_edge!(self, bb, real_target);
                if let Some(target) = unwind {
                    write_edge!(self, bb, imaginary target);
                }
            }
            TerminatorKind::InlineAsm { .. } => unimplemented!(),
        };
        Ok(())
    }
}
