// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::env;
use specifications::TypedSpecificationMap;
use prusti_viper::verifier::VerifierBuilder as ViperVerifierBuilder;
use prusti_interface::verifier::VerifierBuilder;
use prusti_interface::verifier::VerificationContext;
use prusti_interface::verifier::Verifier;
use prusti_interface::data::VerificationTask;
use prusti_interface::data::VerificationResult;
use rustc_driver::driver;
use rustc::hir::intravisit;
use syntax::{self, ast, parse, ptr, attr};
use syntax::codemap::Span;
use environment::Environment;
use hir_visitor::HirVisitor;
use rustc::hir;
use rustc::mir::{Mir, Mutability, Operand, Projection, ProjectionElem, Rvalue};
use rustc_mir::borrow_check::{MirBorrowckCtxt, do_mir_borrowck};
use rustc_mir::borrow_check::flows::Flows;
use rustc_mir::borrow_check::prefixes::*;
use rustc_mir::dataflow::FlowsAtLocation;
use rustc::mir::{BasicBlock, BasicBlockData, VisibilityScope, ARGUMENT_VISIBILITY_SCOPE};
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
use std::collections::{HashSet, HashMap};
use rustc_mir::dataflow::BorrowData;
use rustc::ty::{Region, RegionKind, FreeRegion, BoundRegion, RegionVid, TypeVariants};
use std::fmt;
use rustc_mir::borrow_check::nll::ToRegionVid;
use std::hash::{Hash, Hasher, SipHasher};
use rustc_mir::borrow_check::nll::region_infer::{RegionDefinition, Constraint};
use std::collections::hash_map::DefaultHasher;
use rustc::hir::def_id::DefId;
use rustc::hir::itemlikevisit::ItemLikeVisitor;
use rustc::ty::{self, Ty, TyCtxt};

pub fn dump_borrowck_info<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>) {
    trace!("[dump_useful_info] enter");

    assert!(tcx.sess.nll());
    let mut printer = InfoPrinter {
        tcx: tcx,
    };
    intravisit::walk_crate(&mut printer, tcx.hir.krate());

    trace!("[dump_useful_info] exit");
}

struct InfoPrinter<'a, 'tcx: 'a> {
    pub tcx: TyCtxt<'a, 'tcx, 'tcx>,
}


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
        write!(w, "{:?} = &{}{}{:?}", self.assigned_place, self.region, self.kind_str(), self.borrowed_place)
    }
}

impl<'tcx> Hash for OurBorrowData<'tcx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.assigned_place.hash(state);
        self.region.hash(state);
        self.kind_str().hash(state);
        self.borrowed_place.hash(state);
    }
}

fn get_hash<T>(obj: T) -> u64
    where
        T: Hash,
{
    let mut hasher = DefaultHasher::new();
    obj.hash(&mut hasher);
    hasher.finish()
}

fn get_type_def_id<'tcx>(ty: Ty<'tcx>) -> Option<DefId> {
    match ty.sty {
        ty::TyAdt(def, _) => Some(def.did),
        _ => None
    }
}

fn clean_type<'a, 'gcx, 'tcx>(tcx: TyCtxt<'a, 'gcx, 'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
    match get_type_def_id(ty) {
        Some(def_id) => tcx.type_of(def_id),
        None => ty
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

fn callback<'s, 'g, 'gcx, 'tcx>(mbcx: &'s mut MirBorrowckCtxt<'g, 'gcx, 'tcx>, flows: &'s mut Flows<'g, 'gcx, 'tcx>) {
    trace!("[callback] enter");
    debug!("flows: {}", flows);
    //debug!("MIR: {:?}", mbcx.mir);
    let mut graph = File::create("graph.dot").expect("Unable to create file");
    let mut graph = BufWriter::new(graph);
    graph.write_all(b"digraph G {\n").unwrap();
    writeln!(graph, "graph [compound=true];").unwrap();

    let mut loop_heads = Vec::new();
    let mut forward_edges = HashMap::new();
    let mut back_edges = HashMap::new();

    let show_statement_indices = get_config_option("PRUSTI_DUMP_SHOW_STATEMENT_INDICES", true);
    let show_source = get_config_option("PRUSTI_DUMP_SHOW_SOURCE", false);
    let show_definitely_init = get_config_option("PRUSTI_DUMP_SHOW_DEFINITELY_INIT", false);
    let show_unknown_init = get_config_option("PRUSTI_DUMP_SHOW_UNKNOWN_INIT", false);
    let show_reserved_borrows = get_config_option("PRUSTI_DUMP_SHOW_RESERVED_BORROWS", true);
    let show_active_borrows = get_config_option("PRUSTI_DUMP_SHOW_ACTIVE_BORROWS", true);
    let show_move_out = get_config_option("PRUSTI_DUMP_SHOW_MOVE_OUT", true);
    let show_ever_init = get_config_option("PRUSTI_DUMP_SHOW_EVER_INIT", false);
    let show_lifetime_regions = get_config_option("PRUSTI_DUMP_SHOW_LIFETIME_REGIONS", true);
    let show_scope_tree =  get_config_option("PRUSTI_DUMP_SHOW_SCOPE_TREE", true);
    let show_temp_variables =  get_config_option("PRUSTI_DUMP_SHOW_TEMP_VARIABLES", true);
    let show_lifetimes =  get_config_option("PRUSTI_DUMP_SHOW_LIFETIMES", true);
    let show_lifetime_constraints =  get_config_option("PRUSTI_DUMP_SHOW_LIFETIME_CONSTRAINTS", true);
    let show_types =  get_config_option("PRUSTI_DUMP_SHOW_TYPES", true);

    let regioncx = mbcx.nonlexical_regioncx.as_ref().unwrap();
    let region_values = regioncx.inferred_values();

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
    if show_scope_tree {
        writeln!(graph, "subgraph clusterscopes {{ style=filled;").unwrap();
        writeln!(graph, "SCOPE_TREE").unwrap();
        write_scope_tree(mbcx.tcx, &mbcx.mir, &scope_tree, &mut graph, ARGUMENT_VISIBILITY_SCOPE, 1);
        writeln!(graph, "}}").unwrap();
    }

    // Temporary variables.
    if show_temp_variables {
        writeln!(graph, "Variables [ style=filled shape = \"record\"").unwrap();
        writeln!(graph, "label =<<table>").unwrap();
        writeln!(graph, "<tr><td>VARIABLES</td></tr>").unwrap();
        writeln!(graph, "<tr><td>Name</td><td>Temporary</td><td>Type</td></tr>").unwrap();
        for (temp, var) in mbcx.mir.local_decls.iter_enumerated() {
            let name = var.name.map(|s| s.to_string()).unwrap_or(String::from(""));
            let typ = escape_html(format!("{}", var.ty));
            writeln!(graph, "<tr><td>{}</td><td>{:?}</td><td>{}</td></tr>", name, temp, typ).unwrap();
        }
        writeln!(graph, "</table>>];").unwrap();
    }

    // Lifetimes
    if show_lifetimes {
        writeln!(graph, "Lifetimes [ style=filled shape = \"record\"").unwrap();
        writeln!(graph, "label =<<table>").unwrap();
        writeln!(graph, "<tr><td>Lifetimes</td></tr>").unwrap();
        writeln!(graph, "<tr><td>Name</td><td>Temporary</td></tr>").unwrap();
        for (region_vid, region_definition) in regioncx.definitions.iter_enumerated() {
            let name = match region_definition.external_name {
                Some(&RegionKind::ReStatic) => String::from("'static"),
                Some(&RegionKind::ReFree(FreeRegion { bound_region: BoundRegion::BrNamed(_, name), .. })) => escape_html(format!("{}", name)),
                Some(region) => escape_html(format!("{}", region)),
                None => String::from("")
            };
            let temp = escape_html(format!("{:?}", region_vid));
            writeln!(graph, "<tr><td>{}</td><td>{}</td></tr>", name, temp).unwrap();
        }
        writeln!(graph, "</table>>];").unwrap();
    }

    // Lifetime constraints
    if show_lifetime_constraints {
        writeln!(graph, "subgraph clusterconstraints {{").unwrap();
        writeln!(graph, "label = \"Lifetime constraints\";").unwrap();
        writeln!(graph, "node[shape=box];").unwrap();
        for (region_vid, region_definition) in regioncx.definitions.iter_enumerated() {
            let region_name = escape_html(format!("{:?}", region_vid));
            writeln!(graph, "\"{}\";", region_name).unwrap();
        }
        for constraint in &regioncx.constraints {
            let from_name = escape_html(format!("{:?}", constraint.sub));
            let edge_name = escape_html(format!("{:?}", constraint.point));
            let to_name = escape_html(format!("{:?}", constraint.sup));
            writeln!(graph, "\"{}\" -> \"{}\" [label=\"{}\"];", from_name, to_name, edge_name).unwrap();
        }
        writeln!(graph, "}}").unwrap();
    }

    // Types
    if show_types {
        let mut types: HashSet<ty::Ty> = HashSet::new();
        for var in &mbcx.mir.local_decls {
            for ty in var.ty.walk() {
                let cleaned_ty = clean_type(mbcx.tcx, ty);
                //let cleaned_ty = mbcx.tcx.erase_regions(&ty);
                types.insert(cleaned_ty);
            }
        }
        writeln!(graph, "subgraph clustertypes {{").unwrap();
        writeln!(graph, "label = \"Types\";").unwrap();
        writeln!(graph, "node[shape=box];").unwrap();
        for ty in &types {
            let ty_name = escape_html(format!("{}", ty));
            writeln!(graph, "\"type_{}\" [label=\"{}\"];", get_hash(ty), ty_name).unwrap();
        }
        for ty in &types {
            for subty in ty.walk_shallow() {
                let cleaned_subty = clean_type(mbcx.tcx, subty);
                //let cleaned_subty = mbcx.tcx.erase_regions(&subty);
                let subty_name = escape_html(format!("{}", subty));
                writeln!(graph, "\"type_{:?}\" -> \"type_{:?}\" [label=\"{}\"];", get_hash(ty), get_hash(cleaned_subty), subty_name).unwrap();
            }
        }
        writeln!(graph, "}}").unwrap();
    }

    // CFG
    graph.write_all(format!("Resume\n").as_bytes()).unwrap();
    graph.write_all(format!("Abort\n").as_bytes()).unwrap();
    graph.write_all(format!("Return\n").as_bytes()).unwrap();
    for bb in mbcx.mir.basic_blocks().indices() {
        flows.reset_to_entry_of(bb);

        graph.write_all(format!("\"{:?}\" [ shape = \"record\" \n", bb).as_bytes()).unwrap();
        graph.write_all(format!("label =<<table>\n").as_bytes()).unwrap();
        graph.write_all(format!("<th><td>{:?}</td></th>\n", bb).as_bytes()).unwrap();
        graph.write_all(format!("<th>").as_bytes()).unwrap();
        if show_statement_indices { graph.write_all(format!("<td>Nr</td>").as_bytes()).unwrap(); }
        graph.write_all(format!("<td>statement</td>").as_bytes()).unwrap();
        if show_source { graph.write_all(format!("<td>source</td>").as_bytes()).unwrap(); }
        if show_definitely_init { graph.write_all(format!("<td>definitely init</td>").as_bytes()).unwrap(); }
        if show_unknown_init { graph.write_all(format!("<td>unknown init</td>").as_bytes()).unwrap(); }
        if show_reserved_borrows { graph.write_all(format!("<td>reserved borrows</td>").as_bytes()).unwrap(); }
        if show_active_borrows { graph.write_all(format!("<td>active borrows</td>").as_bytes()).unwrap(); }
        if show_move_out { graph.write_all(format!("<td>move out</td>").as_bytes()).unwrap(); }
        if show_ever_init { graph.write_all(format!("<td>ever init</td>").as_bytes()).unwrap(); }
        if show_lifetime_regions { graph.write_all(format!("<td>gen lifetimes</td>").as_bytes()).unwrap(); }
        if show_lifetime_regions { graph.write_all(format!("<td>kill lifetimes</td>").as_bytes()).unwrap(); }
        graph.write_all(format!("</th>\n").as_bytes()).unwrap();

        let BasicBlockData { ref statements, ref terminator, is_cleanup: _ } =
            mbcx.mir[bb];
        let mut location = Location { block: bb, statement_index: 0 };
        let mut first_run = true;
        let mut lifetime_regions_state: HashSet<RegionVid> = HashSet::new();
        let mut gen_lifetime_regions: HashSet<RegionVid> = HashSet::new();
        let mut kill_lifetime_regions: HashSet<RegionVid> = HashSet::new();

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
                lifetime_regions_state.clear();
                for region_vid in regioncx.definitions.indices() {
                    let contains = regioncx.region_contains_point(region_vid, location);
                    if contains {
                        lifetime_regions_state.insert(region_vid);
                    }
                }
            } else {
                let mut new_lifetime_regions_state: HashSet<RegionVid> = HashSet::new();
                for region_vid in regioncx.definitions.indices() {
                    let contains = regioncx.region_contains_point(region_vid, location);
                    if contains {
                        new_lifetime_regions_state.insert(region_vid);
                    }
                }
                gen_lifetime_regions = new_lifetime_regions_state.difference(&lifetime_regions_state).cloned().collect();
                kill_lifetime_regions = lifetime_regions_state.difference(&new_lifetime_regions_state).cloned().collect();
                lifetime_regions_state = new_lifetime_regions_state;
            }

            if show_statement_indices {
                if first_run {
                    graph.write_all("<td></td>".as_bytes()).unwrap();
                } else {
                    graph.write_all(format!("<td>{}</td>", location.statement_index).as_bytes()).unwrap();
                }
            }

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
                graph.write_all(as_sorted_string(&definitely_init).as_bytes()).unwrap();
                graph.write_all(format!("</td>").as_bytes()).unwrap();
            }

            debug!("unknown initialisation:");
            for place in &unknown_init {
                debug!("  state: {:?}", place);
            }
            if show_unknown_init {
                graph.write_all(format!("<td>").as_bytes()).unwrap();
                graph.write_all(as_sorted_string(&unknown_init).as_bytes()).unwrap();
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
                graph.write_all(as_sorted_string(&reserved_borrows).as_bytes()).unwrap();
                graph.write_all(format!("</td>").as_bytes()).unwrap();
            }

            if show_active_borrows {
                graph.write_all(format!("<td>").as_bytes()).unwrap();
                graph.write_all(as_sorted_string(&active_borrows).as_bytes()).unwrap();
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
                graph.write_all(as_sorted_string(&move_out).as_bytes()).unwrap();
                graph.write_all(format!("</td>").as_bytes()).unwrap();
            }

            if show_ever_init {
                graph.write_all(format!("<td>").as_bytes()).unwrap();
                graph.write_all(as_sorted_string(&ever_init).as_bytes()).unwrap();
                graph.write_all(format!("</td>").as_bytes()).unwrap();
            }

            if show_lifetime_regions {
                debug!("lifetime regions:");

                if first_run {
                    graph.write_all(format!("<td>").as_bytes()).unwrap();
                    for region_vid in &lifetime_regions_state {
                        let region_definition = &regioncx.definitions[*region_vid];
                        let cause = regioncx.why_region_contains_point(*region_vid, location).unwrap();
                        let root_cause = cause.root_cause();
                        debug!("  state: {:?} - {:?}", region_vid, root_cause);
                        graph.write_all(escape_html(format!("{:?}, ", region_vid)).as_bytes()).unwrap();
                    }
                    graph.write_all(format!("</td>").as_bytes()).unwrap();
                } else {
                    graph.write_all(format!("<td>").as_bytes()).unwrap();
                    for region_vid in &gen_lifetime_regions {
                        let region_definition = &regioncx.definitions[*region_vid];
                        let cause = regioncx.why_region_contains_point(*region_vid, location).unwrap();
                        let root_cause = cause.root_cause();
                        debug!("  gen: {:?} - {:?}", region_vid, root_cause);
                        graph.write_all(escape_html(format!("{:?}, ", region_vid)).as_bytes()).unwrap();
                    }
                    graph.write_all(format!("</td>").as_bytes()).unwrap();

                    graph.write_all(format!("<td>").as_bytes()).unwrap();
                    for region_vid in &kill_lifetime_regions {
                        let region_definition = &regioncx.definitions[*region_vid];
                        debug!("  kill: {:?}", region_vid);
                        graph.write_all(escape_html(format!("{:?}, ", region_vid)).as_bytes()).unwrap();
                    }
                    graph.write_all(format!("</td>").as_bytes()).unwrap();
                }
            }

            graph.write_all(format!("</tr>\n").as_bytes()).unwrap();

            if first_run {
                first_run = false;
            } else {
                location.statement_index += 1;
            }
        }

        graph.write_all(format!("</table>> ];\n").as_bytes()).unwrap();

        fn write_normal_edge_str_target(graph: &mut BufWriter<File>, source: BasicBlock, target: &str) {
            graph.write_all(format!("\"{:?}\" -> \"{}\"\n", source, target).as_bytes()).unwrap();
        };
        fn write_unwind_edge(graph: &mut BufWriter<File>, source: BasicBlock, target: BasicBlock) {
            graph.write_all(format!("\"{:?}\" -> \"{:?}\" [color=red]\n", source, target).as_bytes()).unwrap();
        };
        fn write_imaginary_edge(graph: &mut BufWriter<File>, source: BasicBlock, target: BasicBlock) {
            graph.write_all(format!("\"{:?}\" -> \"{:?}\" [style=\"dashed\"]\n", source, target).as_bytes()).unwrap();
        };

        if let Some(ref term) = *terminator {
            let mut write_normal_edge = |graph: &mut BufWriter<File>, source: BasicBlock, target: BasicBlock| {
                forward_edges.entry(source).or_insert(Vec::new()).push(target);
                back_edges.entry(target).or_insert(Vec::new()).push(source);
                let dominators = mbcx.mir.dominators();
                if dominators.is_dominated_by(source, target) {
                    loop_heads.push(target);
                    graph.write_all(format!("\"{:?}\" -> \"{:?}\" [color=green]\n", source, target).as_bytes()).unwrap();
                } else {
                    graph.write_all(format!("\"{:?}\" -> \"{:?}\"\n", source, target).as_bytes()).unwrap();
                }
            };
            use rustc::mir::TerminatorKind;
            match term.kind {
                TerminatorKind::Goto { target } => {
                    write_normal_edge(&mut graph, bb, target);
                }
                TerminatorKind::SwitchInt { ref targets, .. } => {
                    for target in targets {
                        write_normal_edge(&mut graph, bb, *target);
                    }
                }
                TerminatorKind::Resume => {
                    write_normal_edge_str_target(&mut graph, bb, "Resume");
                }
                TerminatorKind::Abort => {
                    write_normal_edge_str_target(&mut graph, bb, "Abort");
                }
                TerminatorKind::Return => {
                    write_normal_edge_str_target(&mut graph, bb, "Return");
                }
                TerminatorKind::Unreachable => {}
                TerminatorKind::DropAndReplace { ref target, unwind, .. } |
                TerminatorKind::Drop { ref target, unwind, .. } => {
                    write_normal_edge(&mut graph, bb, *target);
                    if let Some(target) = unwind {
                        write_unwind_edge(&mut graph, bb, target);
                    }
                }

                TerminatorKind::Call { ref destination, cleanup, .. } => {
                    if let &Some((_, target)) = destination {
                        write_normal_edge(&mut graph, bb, target);
                    }
                    if let Some(target) = cleanup {
                        write_unwind_edge(&mut graph, bb, target);
                    }
                }
                TerminatorKind::Assert { target, .. } => {
                    write_normal_edge(&mut graph, bb, target);
                }
                TerminatorKind::Yield { .. } => { unimplemented!() }
                TerminatorKind::GeneratorDrop => { unimplemented!() }
                TerminatorKind::FalseEdges { ref real_target, ref imaginary_targets } => {
                    write_normal_edge(&mut graph, bb, *real_target);
                    for target in imaginary_targets {
                        write_imaginary_edge(&mut graph, bb, *target);
                    }
                }
                TerminatorKind::FalseUnwind { real_target, unwind } => {
                    write_normal_edge(&mut graph, bb, real_target);
                    if let Some(target) = unwind {
                        write_imaginary_edge(&mut graph, bb, target);
                    }
                }
            };
        }
    }

    // Lifetime constraints
    let mut is_reachable = |from: BasicBlock, to: BasicBlock| {
        let mut work_list = vec![from];
        let mut visited = HashSet::new();
        visited.insert(from);
        while let Some(current) = work_list.pop() {
            if current == to {
                return true;
            }
            for target in forward_edges.entry(current).or_insert(Vec::new()) {
                if !visited.contains(target) {
                    work_list.push(*target);
                    visited.insert(*target);
                }
            }
        }
        false
    };
    fn tarjan(nodes: &Vec<RegionVid>, edges: &Vec<Constraint>) -> HashMap<RegionVid, u32> {
        struct State<'a> {
            nodes: Vec<RegionVid>,
            edges: &'a Vec<Constraint>,
            low_link: HashMap<RegionVid, u32>,
            indices: HashMap<RegionVid, u32>,
            index: u32,
            stack: Vec<RegionVid>,
        };

        impl<'a> State<'a> {

            fn min(&self, node1: RegionVid, node2: RegionVid) -> u32 {
                trace!("[min] node1={:?} node2={:?}", node1, node2);
                let low_link1 = self.low_link.get(&node1).unwrap();
                let low_link2 = self.low_link.get(&node2).unwrap();
                if low_link1 < low_link2 {
                    *low_link1
                } else {
                    *low_link2
                }
            }

            fn strong_connect(&mut self, node: RegionVid) {
                trace!("[strong_connect] enter node={:?}", node);
                self.indices.insert(node, self.index);
                self.low_link.insert(node, self.index);
                self.index += 1;
                self.stack.push(node);
                for edge in self.edges.iter() {
                    if edge.sub == node {
                        if !self.indices.contains_key(&edge.sup) {
                            self.strong_connect(edge.sup);
                            let min = self.min(node, edge.sup);
                            self.low_link.insert(node, min);
                        } else if self.stack.contains(&edge.sup) {
                            let min = self.min(node, edge.sup);
                            self.low_link.insert(node, min);
                        }
                    }
                }
                trace!("[strong_connect] exit");
            }

        };

        let mut state = State {
            nodes: nodes.clone(),
            edges: edges,
            low_link: HashMap::new(),
            indices: HashMap::new(),
            index: 0,
            stack: Vec::new(),
        };

        while let Some(initial) = state.nodes.pop() {
            if !state.indices.contains_key(&initial) {
                state.strong_connect(initial);
            }
        }

        state.low_link
    };
    for loop_head in loop_heads {
        writeln!(graph, "subgraph clusterconstraints{:?} {{", loop_head).unwrap();
        writeln!(graph, "label = \"Lifetime constraints for {:?}\";", loop_head).unwrap();
        writeln!(graph, "node[shape=box];").unwrap();
        let mut nodes = Vec::new();
        for (region_vid, region_definition) in regioncx.definitions.iter_enumerated() {
            nodes.push(region_vid);
        }
        let mut edges = Vec::new();
        for constraint in &regioncx.constraints {
            if constraint.point.block != loop_head &&
                is_reachable(constraint.point.block, loop_head) {
                edges.push(*constraint);
            }
        }
        let cluster_assignment = tarjan(&nodes, &edges);
        let mut clusters = HashMap::new();
        for (node, cluster) in &cluster_assignment {
            clusters.entry(cluster).or_insert(Vec::new()).push(node)
        }
        for (cluster_id, nodes) in &clusters {
            let mut nodes: Vec<_> = nodes.iter().map(|node| escape_html(format!("{:?}", node))).collect();
            nodes.sort();
            writeln!(graph, "\"{:?}__{}\" [label=\"{}\"];", loop_head, cluster_id, nodes.join(", ")).unwrap();
        }
        for edge in edges {
            let from_name = escape_html(format!("{:?}__{}", loop_head, cluster_assignment.get(&edge.sub).unwrap()));
            let to_name = escape_html(format!("{:?}__{}", loop_head, cluster_assignment.get(&edge.sup).unwrap()));
            writeln!(graph, "\"{}\" -> \"{}\";", from_name, to_name).unwrap();
        }
        debug!("clusters: {:?}", clusters);
        writeln!(graph, "}}").unwrap();
    }

    graph.write_all(b"}").unwrap();
    trace!("[callback] exit");
}

fn as_sorted_string<T>(set: &HashSet<T>) -> String
    where
        T: Eq,
        T: Hash,
        T: fmt::Debug,
{
    let mut vector = set.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>();
    vector.sort();
    escape_html(vector.join(", "))
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

/// Returns true if all the places of `a` are contained in the places of `b`.
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

fn has_prusti_with(attrs: &[ast::Attribute], name: &str) -> bool {
    for attr in attrs {
        if attr.check_name(name) {
            return true;
        }
    }
    false
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
            _ => unimplemented!(),
        };

        trace!("[visit_fn] enter name={:?}", name);
        let def_id = self.tcx.hir.local_def_id(node_id);
        let attributes = self.tcx.get_attrs(def_id);

        match env::var_os("PRUSTI_DUMP_PROC").and_then(|value| value.into_string().ok()) {
            Some(value) => {
                if name == value {
                    debug!("dump mir for fn {:?}", name);

                    let input_mir = &self.tcx.mir_validated(def_id).borrow();
                    let opt_closure_req = self.tcx.infer_ctxt().enter(|infcx| {
                        do_mir_borrowck(&infcx, input_mir, def_id, Some(box callback))
                    });
                }
            },
            _ => {},
        }

        trace!("[visit_fn] exit");
    }
}
