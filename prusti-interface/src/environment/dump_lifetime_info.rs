use log::{debug, trace};
use prusti_common::config;
use rustc_hir as hir;
use rustc_hir::{def_id::DefId, itemlikevisit::ItemLikeVisitor};
use rustc_middle::{mir, ty, ty::TyCtxt};
use std::{
    collections::{HashMap, HashSet},
    fs::File,
    io::{self, BufWriter, Write},
    path::PathBuf,
};
use rustc_infer::infer::{InferCtxt, TyCtxtInferExt};

use crate::environment::borrowck2::obtain_mir_body;

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
        // eprintln!("def_id: {:?}", def_id);
        print_info(tcx, def_id);
        // let outlives = gather_outlives(tcx.param_env(def_id));
        // eprintln!("outlives: {:?}", outlives);
        // eprintln!("inferred_outlives_of: {:?}", tcx.inferred_outlives_of(def_id));
        // eprintln!("implied_outlives_bounds: {:?}", tcx.implied_outlives_bounds(def_id));
    }

    trace!("[dump_lifetime_info] exit");
}

// fn gather_outlives(param_env: ty::ParamEnv) -> HashMap<ty::Region, HashSet<ty::Region>> {
//     let mut result = HashMap::<ty::Region, HashSet<ty::Region>>::new();
//     let outlives = param_env.caller_bounds().iter()
//         .filter_map(|b| match b.kind().skip_binder() {
//             ty::PredicateKind::RegionOutlives(ty::OutlivesPredicate(a, b)) => Some((a, b)),
//             _ => None
//         });
//     for (a, b) in outlives {
//         result.entry(a).or_default().insert(b);
//     }
//     result
// }

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

    let body = obtain_mir_body(tcx, def_id);

    let local_def_id = def_id.expect_local();
    let def_path = tcx.hir().def_path(local_def_id);
    let output_path = PathBuf::from(config::log_dir())
        .join("nll-facts")
        .join(def_path.to_filename_friendly_no_crate())
        .join("output_lifetime.dot");
    debug!("Writing output to {:?}", output_path);
    body.to_graphviz(&output_path).unwrap();

    trace!("[print_info] exit {:?}", def_id);
}

// fn do_print_info<'tcx>(infcx: &InferCtxt<'_, 'tcx>, input_body: &mir::Body<'tcx>, def_id: DefId) {
//     let tcx = infcx.tcx;

//     let local_def_id = def_id.expect_local();
//     let def_path = tcx.hir().def_path(local_def_id);
//     let output_path = PathBuf::from(config::log_dir())
//         .join("nll-facts")
//         .join(def_path.to_filename_friendly_no_crate())
//         .join("output_lifetime.dot");
//     debug!("Writing output to {:?}", output_path);
//     let output_file = File::create(output_path).expect("Unable to create file");
//     let output = std::cell::RefCell::new(BufWriter::new(output_file));

//     let def = input_body.source.with_opt_param().as_local().unwrap();
//     let param_env = tcx.param_env(def.did);
//     eprintln!("param_env: {:?}", param_env);
//     let mut body = input_body.clone();
//     let universal_regions = std::rc::Rc::new(rustc_mir::borrow_check::universal_regions::UniversalRegions::new(infcx, def, param_env));
//     eprintln!("universal_regions: {:?}", universal_regions);
//     rustc_mir::borrow_check::renumber::renumber_mir(infcx, &mut body, &mut rustc_index::vec::IndexVec::new());
//     let body = &body;

//     {
//         use rustc_mir::borrow_check::type_check::free_region_relations::CreateResult;
//         use rustc_mir::borrow_check::member_constraints::MemberConstraintSet;
//         use rustc_mir::borrow_check::type_check::MirTypeckRegionConstraints;
//         use rustc_mir::borrow_check::constraints::OutlivesConstraintSet;
//         use rustc_mir::borrow_check::region_infer::values::LivenessValues;
//         use rustc_index::vec::IndexVec;
//         use rustc_mir::borrow_check::region_infer::values::PlaceholderIndices;
//         use rustc_mir::borrow_check::type_check::free_region_relations;
//         use rustc_mir::borrow_check::region_infer::values::RegionValueElements;

//         let elements = &std::rc::Rc::new(RegionValueElements::new(&body));

//         let mut constraints = MirTypeckRegionConstraints {
//             placeholder_indices: PlaceholderIndices::default(),
//             placeholder_index_to_region: IndexVec::default(),
//             liveness_constraints: LivenessValues::new(elements.clone()),
//             outlives_constraints: OutlivesConstraintSet::default(),
//             member_constraints: MemberConstraintSet::default(),
//             closure_bounds_mapping: Default::default(),
//             type_tests: Vec::default(),
//         };

//         let implicit_region_bound = infcx.tcx.mk_region(ty::ReVar(universal_regions.fr_fn_body));

//         let CreateResult {
//             universal_region_relations,
//             region_bound_pairs,
//             normalized_inputs_and_output,
//         } = free_region_relations::create(
//             infcx,
//             param_env,
//             Some(implicit_region_bound),
//             &universal_regions,
//             &mut constraints,
//         );

//         // eprintln!("universal_region_relations: {:?}", universal_region_relations);
//         eprintln!("universal_regions.universal_regions: {:?}",
//             universal_regions.universal_regions().collect::<Vec<_>>());
//         eprintln!("universal_region_relations.known_outlives: {:?}",
//             universal_region_relations.known_outlives().collect::<Vec<_>>());
//         eprintln!("region_bound_pairs: {:?}", region_bound_pairs);
//         eprintln!("normalized_inputs_and_output: {:?}", normalized_inputs_and_output);

//         let mut all_facts = Some(Default::default());
//         use rustc_mir::borrow_check::location::LocationTable;
//         let location_table = &LocationTable::new(&body);

//         use rustc_mir::borrow_check::borrow_set::BorrowSet;
//         use rustc_mir::dataflow::MoveDataParamEnv;
//         use rustc_mir::dataflow::move_paths::MoveData;
//         use rustc_middle::mir::Place;
//         use rustc_mir::dataflow::move_paths::MoveError;
//         let (move_data, _move_errors): (MoveData<'tcx>, Vec<(Place<'tcx>, MoveError<'tcx>)>) =
//         match MoveData::gather_moves(&body, tcx, param_env) {
//             Ok(move_data) => (move_data, Vec::new()),
//             Err((move_data, move_errors)) => (move_data, move_errors),
//         };
//         let mdpe = MoveDataParamEnv { move_data, param_env };
//         let id = tcx.hir().local_def_id_to_hir_id(def.did);
//         let locals_are_invalidated_at_exit = tcx.hir().body_owner_kind(id).is_fn_or_closure();
//         let borrow_set =
//         BorrowSet::build(tcx, body, locals_are_invalidated_at_exit, &mdpe.move_data);

//         use rustc_mir::borrow_check::constraint_generation;
//         constraint_generation::generate_constraints(
//             infcx,
//             &mut constraints.liveness_constraints,
//             &mut all_facts,
//             location_table,
//             &body,
//             &borrow_set,
//         );
//     }


//     let info_printer = InfoPrinter { tcx, output, body };
//     info_printer.print_info().unwrap();
// }

// mod renumber {
//     // Copied from
//     // https://github.com/rust-lang/rust/blob/master/compiler/rustc_mir/src/borrow_check/renumber.rs
//     // TODO: create a PR that makes this module public so that I do not need to
//     // copy-paste code.
//     use log::{debug, trace};
//     use rustc_index::vec::IndexVec;
//     use rustc_infer::infer::{InferCtxt, NllRegionVariableOrigin};
//     use rustc_middle::mir::visit::{MutVisitor, TyContext};
//     use rustc_middle::mir::{Body, Location, PlaceElem, Promoted};
//     use rustc_middle::ty::subst::SubstsRef;
//     use rustc_middle::ty::{self, Ty, TyCtxt, TypeFoldable};

//     pub fn renumber_mir<'tcx>(
//         infcx: &InferCtxt<'_, 'tcx>,
//         body: &mut Body<'tcx>,
//     ) {
//         debug!("renumber_mir()");
//         debug!("renumber_mir: body.arg_count={:?}", body.arg_count);

//         let mut visitor = NllVisitor { infcx };

//         visitor.visit_body(body);
//     }

//     /// Replaces all regions appearing in `value` with fresh inference
//     /// variables.
//     pub fn renumber_regions<'tcx, T>(infcx: &InferCtxt<'_, 'tcx>, value: T) -> T
//     where
//         T: TypeFoldable<'tcx>,
//     {
//         debug!("renumber_regions(value={:?})", value);

//         infcx.tcx.fold_regions(value, &mut false, |_region, _depth| {
//             let origin = NllRegionVariableOrigin::Existential { from_forall: false };
//             infcx.next_nll_region_var(origin)
//         })
//     }

//     struct NllVisitor<'a, 'tcx> {
//         infcx: &'a InferCtxt<'a, 'tcx>,
//     }

//     impl<'a, 'tcx> NllVisitor<'a, 'tcx> {
//         fn renumber_regions<T>(&mut self, value: T) -> T
//         where
//             T: TypeFoldable<'tcx>,
//         {
//             renumber_regions(self.infcx, value)
//         }
//     }

//     impl<'a, 'tcx> MutVisitor<'tcx> for NllVisitor<'a, 'tcx> {
//         fn tcx(&self) -> TyCtxt<'tcx> {
//             self.infcx.tcx
//         }

//         fn visit_ty(&mut self, ty: &mut Ty<'tcx>, ty_context: TyContext) {
//             debug!("visit_ty(ty={:?}, ty_context={:?})", ty, ty_context);

//             *ty = self.renumber_regions(ty);

//             debug!("visit_ty: ty={:?}", ty);
//         }

//         fn process_projection_elem(
//             &mut self,
//             elem: PlaceElem<'tcx>,
//             _: Location,
//         ) -> Option<PlaceElem<'tcx>> {
//             if let PlaceElem::Field(field, ty) = elem {
//                 let new_ty = self.renumber_regions(ty);

//                 if new_ty != ty {
//                     return Some(PlaceElem::Field(field, new_ty));
//                 }
//             }

//             None
//         }

//         fn visit_substs(&mut self, substs: &mut SubstsRef<'tcx>, location: Location) {
//             debug!("visit_substs(substs={:?}, location={:?})", substs, location);

//             *substs = self.renumber_regions(*substs);

//             debug!("visit_substs: substs={:?}", substs);
//         }

//         fn visit_region(&mut self, region: &mut ty::Region<'tcx>, location: Location) {
//             debug!("visit_region(region={:?}, location={:?})", region, location);

//             let old_region = *region;
//             *region = self.renumber_regions(&old_region);

//             debug!("visit_region: region={:?}", region);
//         }

//         fn visit_const(&mut self, constant: &mut &'tcx ty::Const<'tcx>, _location: Location) {
//             *constant = self.renumber_regions(&*constant);
//         }
//     }
// }

struct InfoPrinter<'a, 'tcx: 'a> {
    tcx: TyCtxt<'tcx>,
    output: std::cell::RefCell<BufWriter<File>>,
    body: &'a mir::Body<'tcx>,
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

        for bb in self.body.basic_blocks().indices() {
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
        for info in &self.body.var_debug_info {
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
        for (temp, var) in self.body.local_decls.iter_enumerated() {
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
        } = self.body[bb];
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
