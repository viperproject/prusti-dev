use prusti_rustc_interface::ast::ast;
use prusti_rustc_interface::errors::MultiSpan;
use prusti_rustc_interface::hir::intravisit;
use prusti_rustc_interface::middle::{hir::map::Map, ty::TyCtxt};
use prusti_rustc_interface::span::Span;

use crate::{
    environment::Environment,
    PrustiError,
    utils::{
        has_abstract_predicate_attr, has_extern_spec_attr, has_prusti_attr, read_prusti_attr,
        read_prusti_attrs,
    },
};
use log::debug;
use prusti_rustc_interface::hir::def_id::{CrateNum, DefId, LocalDefId, LOCAL_CRATE};
use std::{collections::HashMap, convert::TryInto, fmt::Debug, path::PathBuf};

pub mod checker;
pub mod external;
pub mod typed;
pub mod for_export;
pub mod encoder;
pub mod decoder;

use typed::SpecIdRef;

use crate::specs::{
    external::ExternSpecResolver,
    typed::{ProcedureSpecification, ProcedureSpecificationKind, SpecGraph, SpecificationItem},
};
use prusti_specs::specifications::common::SpecificationId;

use std::path::Path;
use for_export::{DefSpecificationMapForExport, DefSpecificationMapForExportOwned};

#[derive(Debug)]
struct ProcedureSpecRefs {
    spec_id_refs: Vec<SpecIdRef>,
    pure: bool,
    abstract_predicate: bool,
    trusted: bool,
}

#[derive(Debug, Default)]
struct TypeSpecRefs {
    invariants: Vec<LocalDefId>,
    trusted: bool,
}

/// Specification collector, intended to be applied as a visitor over the crate
/// HIR. After the visit, [SpecCollector::build_def_specs] can be used to get back
/// a mapping of DefIds (which may not be local due to extern specs) to their
/// [typed::SpecificationSet], i.e. procedures, loop invariants, and structs.
pub struct SpecCollector<'a, 'tcx: 'a> {
    tcx: TyCtxt<'tcx>,
    env: &'a Environment<'tcx>,
    extern_resolver: ExternSpecResolver<'a, 'tcx>,

    /// Map from specification IDs to their typed expressions.
    spec_functions: HashMap<SpecificationId, LocalDefId>,

    /// Map from functions/loops/types to their specifications.
    procedure_specs: HashMap<LocalDefId, ProcedureSpecRefs>,
    loop_specs: Vec<LocalDefId>,
    type_specs: HashMap<LocalDefId, TypeSpecRefs>,
    prusti_assertions: Vec<LocalDefId>,
    prusti_assumptions: Vec<LocalDefId>,
    ghost_begin: Vec<LocalDefId>,
    ghost_end: Vec<LocalDefId>,
}

impl<'a, 'tcx> SpecCollector<'a, 'tcx> {
    pub fn new(env: &'a Environment<'tcx>) -> Self {
        let tcx = env.tcx();
        Self {
            tcx,
            env,
            extern_resolver: ExternSpecResolver::new(env),
            spec_functions: HashMap::new(),
            procedure_specs: HashMap::new(),
            loop_specs: vec![],
            type_specs: HashMap::new(),
            prusti_assertions: vec![],
            prusti_assumptions: vec![],
            ghost_begin: vec![],
            ghost_end: vec![],
        }
    }

    pub fn build_def_specs(&self, build_output_dir: &Option<PathBuf>) -> typed::DefSpecificationMap<'tcx> {
        let mut def_spec = typed::DefSpecificationMap::new();
        self.determine_procedure_specs(&mut def_spec);
        self.determine_extern_specs(&mut def_spec);
        self.determine_loop_specs(&mut def_spec);
        self.determine_type_specs(&mut def_spec);
        self.determine_prusti_assertions(&mut def_spec);
        self.determine_prusti_assumptions(&mut def_spec);
        self.determine_ghost_begin_ends(&mut def_spec);
        // TODO: remove spec functions (make sure none are duplicated or left over)

        self.fetch_local_mirs(&mut def_spec);

        if let Some(build_output_dir) = build_output_dir {
            self.write_specs_to_file(&def_spec, build_output_dir);
            self.merge_specs_from_dependencies(&mut def_spec, build_output_dir);
        }

        def_spec
    }

    fn get_crate_specs_path(&self, build_output_dir: &Path, crate_num: CrateNum) -> Box<PathBuf> {
        let mut path = Box::new(build_output_dir.to_path_buf());
        path.push("serialized_specs");
        path.push(format!("{}-{:x}.bin",
                          self.tcx.crate_name(crate_num),
                          self.tcx.stable_crate_id(crate_num).to_u64(),
        ));
        path
    }

    fn write_specs_to_file(&self, def_spec: &typed::DefSpecificationMap<'tcx>, build_output_dir: &Path) {
        let def_spec_for_export = DefSpecificationMapForExport::from_def_spec(def_spec);
        let target_filename = self.get_crate_specs_path(build_output_dir, LOCAL_CRATE);
        def_spec_for_export.write_into_file(
            self.tcx,
            &target_filename,
        ).unwrap()
    }

    fn merge_specs_from_dependencies(&self, def_spec: &mut typed::DefSpecificationMap<'tcx>, build_output_dir: &Path) {
        for crate_num in self.tcx.crates(()) {
            if *crate_num == LOCAL_CRATE {
                continue;
            }

            let file = self.get_crate_specs_path(build_output_dir, *crate_num);
            if file.is_file() {
                self.merge_specs_from_file(def_spec, &file);
            }
        }
    }

    fn merge_specs_from_file(&self, def_spec: &mut typed::DefSpecificationMap<'tcx>, path: &Path) {
        let def_spec_for_export = DefSpecificationMapForExportOwned::read_from_file(
            self.tcx,
            path,
        ).unwrap();

        def_spec_for_export.extend(def_spec);
    }

    fn determine_procedure_specs(&self, def_spec: &mut typed::DefSpecificationMap) {
        for (local_id, refs) in self.procedure_specs.iter() {
            let mut spec = SpecGraph::new(ProcedureSpecification::empty());
            spec.set_span(self.env.get_def_span(local_id.to_def_id()));

            let mut kind = if refs.abstract_predicate {
                ProcedureSpecificationKind::Predicate(None)
            } else if refs.pure {
                ProcedureSpecificationKind::Pure
            } else {
                ProcedureSpecificationKind::Impure
            };

            for spec_id_ref in &refs.spec_id_refs {
                match spec_id_ref {
                    SpecIdRef::Precondition(spec_id) => {
                        spec.add_precondition(*self.spec_functions.get(spec_id).unwrap(), self.env);
                    }
                    SpecIdRef::Postcondition(spec_id) => {
                        spec.add_postcondition(
                            *self.spec_functions.get(spec_id).unwrap(),
                            self.env,
                        );
                    }
                    SpecIdRef::Pledge { lhs, rhs } => {
                        spec.add_pledge(typed::Pledge {
                            reference: None, // FIXME: Currently only `result` is supported.
                            lhs: lhs
                                .as_ref()
                                .map(|spec_id| *self.spec_functions.get(spec_id).unwrap()),
                            rhs: *self.spec_functions.get(rhs).unwrap(),
                        });
                    }
                    SpecIdRef::Predicate(spec_id) => {
                        kind = ProcedureSpecificationKind::Predicate(Some(
                            (*self.spec_functions.get(spec_id).unwrap()).to_def_id(),
                        ));
                    }
                }
            }

            spec.set_trusted(refs.trusted);

            // We do not want to create an empty kind.
            // This would lead to refinement inheritance if there is a trait involved.
            // Instead, we require the user to explicitly make annotations.
            spec.set_kind(kind);

            if !spec.specs_with_constraints.is_empty()
                && !prusti_common::config::enable_ghost_constraints()
            {
                let span = self.env.tcx().def_span(*local_id);
                PrustiError::unsupported(
                    "Ghost constraints need to be enabled with a feature flag",
                    MultiSpan::from(span),
                )
                .emit(self.env);
            } else if !spec.specs_with_constraints.is_empty()
                && !*spec.base_spec.trusted.expect_inherent()
            {
                let span = self.env.tcx().def_span(*local_id);
                PrustiError::unsupported(
                    "Ghost constraints can only be used on trusted functions",
                    MultiSpan::from(span),
                )
                .emit(self.env);
            } else {
                def_spec.proc_specs.insert(local_id.to_def_id(), spec);
            }
        }
    }

    fn determine_extern_specs(&self, def_spec: &mut typed::DefSpecificationMap) {
        self.extern_resolver.check_errors(self.env);
        for (extern_spec_decl, spec_id) in self.extern_resolver.extern_fn_map.iter() {
            let target_def_id = extern_spec_decl.get_target_def_id();

            if def_spec.proc_specs.contains_key(&target_def_id) {
                PrustiError::incorrect(
                    format!(
                        "external specification provided for {}, which already has a specification",
                        self.env.get_item_name(target_def_id)
                    ),
                    MultiSpan::from_span(self.env.get_def_span(*spec_id)),
                )
                .emit(self.env);
            }

            let spec = def_spec.proc_specs.remove(spec_id).unwrap();
            def_spec.proc_specs.insert(target_def_id, spec);
        }
    }

    fn determine_loop_specs(&self, def_spec: &mut typed::DefSpecificationMap) {
        for local_id in self.loop_specs.iter() {
            def_spec.loop_specs.insert(
                local_id.to_def_id(),
                typed::LoopSpecification {
                    invariant: *local_id,
                },
            );
        }
    }

    fn determine_type_specs(&self, def_spec: &mut typed::DefSpecificationMap) {
        for (type_id, refs) in self.type_specs.iter() {
            if !refs.invariants.is_empty() && !prusti_common::config::enable_type_invariants() {
                let span = self.env.tcx().def_span(type_id.to_def_id());
                PrustiError::unsupported(
                    "Type invariants need to be enabled with a feature flag",
                    MultiSpan::from(span),
                )
                .emit(self.env);
            }

            def_spec.type_specs.insert(
                type_id.to_def_id(),
                typed::TypeSpecification {
                    invariant: SpecificationItem::Inherent(
                        refs.invariants.clone().into_iter().map(LocalDefId::to_def_id).collect()
                    ),
                    trusted: SpecificationItem::Inherent(refs.trusted),
                },
            );
        }
    }
    fn determine_prusti_assertions(&self, def_spec: &mut typed::DefSpecificationMap) {
        for local_id in self.prusti_assertions.iter() {
            def_spec.prusti_assertions.insert(
                local_id.to_def_id(),
                typed::PrustiAssertion {
                    assertion: *local_id,
                },
            );
        }
    }
    fn determine_prusti_assumptions(&self, def_spec: &mut typed::DefSpecificationMap) {
        for local_id in self.prusti_assumptions.iter() {
            def_spec.prusti_assumptions.insert(
                local_id.to_def_id(),
                typed::PrustiAssumption {
                    assumption: *local_id,
                },
            );
        }
    }
    fn determine_ghost_begin_ends(&self, def_spec: &mut typed::DefSpecificationMap) {
        for local_id in self.ghost_begin.iter() {
            def_spec.ghost_begin.insert(
                local_id.to_def_id(),
                typed::GhostBegin { marker: *local_id },
            );
        }
        for local_id in self.ghost_end.iter() {
            def_spec
                .ghost_end
                .insert(local_id.to_def_id(), typed::GhostEnd { marker: *local_id });
        }
    }

    fn fetch_local_mirs(&self, def_spec: &mut typed::DefSpecificationMap<'tcx>) {
        for def_id in def_spec.proc_specs
            // collect [DefId]s in specs of all procedures
            .values()
            // TODO: extend also to specs_with_constraints instead of base_spec only
            .map(|spec_graph| &spec_graph.base_spec)
            .flat_map(|proc_spec| {
                vec![&proc_spec.pres, &proc_spec.posts].into_iter().filter_map(|spec_item| {
                    spec_item.extract_with_selective_replacement()
                })
                    .flatten()
            }) {
            let base_mir = self.env.local_base_mir(def_id.expect_local());
            def_spec.mirs_of_specs.insert(*def_id,base_mir);
        }
    }
}

fn parse_spec_id(spec_id: String, def_id: DefId) -> SpecificationId {
    spec_id
        .try_into()
        .unwrap_or_else(|_| panic!("cannot parse the spec_id attached to {:?}", def_id))
}

fn get_procedure_spec_ids(def_id: DefId, attrs: &[ast::Attribute]) -> Option<ProcedureSpecRefs> {
    let mut spec_id_refs = vec![];

    spec_id_refs.extend(
        read_prusti_attrs("pre_spec_id_ref", attrs)
            .into_iter()
            .map(|raw_spec_id| SpecIdRef::Precondition(parse_spec_id(raw_spec_id, def_id))),
    );
    spec_id_refs.extend(
        read_prusti_attrs("post_spec_id_ref", attrs)
            .into_iter()
            .map(|raw_spec_id| SpecIdRef::Postcondition(parse_spec_id(raw_spec_id, def_id))),
    );
    spec_id_refs.extend(
        // TODO: pledges with LHS that is not "result" would need to carry the
        // LHS expression through typing
        read_prusti_attrs("pledge_spec_id_ref", attrs)
            .into_iter()
            .map(|raw_spec_id| SpecIdRef::Pledge {
                lhs: None,
                rhs: parse_spec_id(raw_spec_id, def_id),
            }),
    );
    match (
        read_prusti_attr("assert_pledge_spec_id_ref_lhs", attrs),
        read_prusti_attr("assert_pledge_spec_id_ref_rhs", attrs),
    ) {
        (Some(lhs_id), Some(rhs_id)) => {
            spec_id_refs.push(SpecIdRef::Pledge {
                lhs: Some(parse_spec_id(lhs_id, def_id)),
                rhs: parse_spec_id(rhs_id, def_id),
            });
        }
        (None, None) => {}
        _ => unreachable!(),
    }
    spec_id_refs.extend(
        read_prusti_attr("pred_spec_id_ref", attrs)
            .map(|raw_spec_id| SpecIdRef::Predicate(parse_spec_id(raw_spec_id, def_id))),
    );
    debug!(
        "Function {:?} has specification ids {:?}",
        def_id, spec_id_refs
    );

    let pure = has_prusti_attr(attrs, "pure");
    let trusted = has_prusti_attr(attrs, "trusted");
    let abstract_predicate = has_abstract_predicate_attr(attrs);

    if abstract_predicate || pure || trusted || !spec_id_refs.is_empty() {
        Some(ProcedureSpecRefs {
            spec_id_refs,
            pure,
            abstract_predicate,
            trusted,
        })
    } else {
        None
    }
}

impl<'a, 'tcx> intravisit::Visitor<'tcx> for SpecCollector<'a, 'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter =prusti_rustc_interface::middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_trait_item(&mut self, ti: &'tcx prusti_rustc_interface::hir::TraitItem) {
        intravisit::walk_trait_item(self, ti);

        let id = ti.hir_id();
        let local_id = self.tcx.hir().local_def_id(id);
        let def_id = local_id.to_def_id();
        let attrs = self.env.get_local_attributes(ti.def_id);

        // Collect procedure specifications
        if let Some(procedure_spec_ref) = get_procedure_spec_ids(def_id, attrs) {
            self.procedure_specs.insert(local_id, procedure_spec_ref);
        }
    }

    fn visit_fn(
        &mut self,
        fn_kind: intravisit::FnKind<'tcx>,
        fn_decl: &'tcx prusti_rustc_interface::hir::FnDecl,
        body_id: prusti_rustc_interface::hir::BodyId,
        span: Span,
        id: prusti_rustc_interface::hir::hir_id::HirId,
    ) {
        intravisit::walk_fn(self, fn_kind, fn_decl, body_id, span, id);

        let local_id = self.tcx.hir().local_def_id(id);
        let def_id = local_id.to_def_id();
        let attrs = self.tcx.hir().attrs(id);

        // Collect spec functions
        if let Some(raw_spec_id) = read_prusti_attr("spec_id", attrs) {
            let spec_id: SpecificationId = parse_spec_id(raw_spec_id, def_id);
            self.spec_functions.insert(spec_id, local_id);

            // Collect loop specifications
            if has_prusti_attr(attrs, "loop_body_invariant_spec") {
                self.loop_specs.push(local_id);
            }

            // TODO: (invariants and trusted flag) visit the struct itself?
            // For now, a method is used to mark the type as "trusted".

            // Collect type invariants
            if has_prusti_attr(attrs, "type_invariant_spec") {
                let self_id = fn_decl.inputs[0].hir_id;
                let hir = self.tcx.hir();
                let impl_id = hir.get_parent_node(hir.get_parent_node(self_id));
                let type_id = get_type_id_from_impl_node(hir.get(impl_id)).unwrap();
                self.type_specs
                    .entry(type_id.as_local().unwrap())
                    .or_default()
                    .invariants
                    .push(local_id);
            }

            // Collect trusted type flag
            if has_prusti_attr(attrs, "trusted_type") {
                let self_id = fn_decl.inputs[0].hir_id;
                let hir = self.tcx.hir();
                let impl_id = hir.get_parent_node(hir.get_parent_node(self_id));
                let type_id = get_type_id_from_impl_node(hir.get(impl_id)).unwrap();
                self.type_specs
                    .entry(type_id.as_local().unwrap())
                    .or_default()
                    .trusted = true;
            }

            if has_prusti_attr(attrs, "prusti_assertion") {
                self.prusti_assertions.push(local_id);
            }

            if has_prusti_attr(attrs, "prusti_assumption") {
                self.prusti_assumptions.push(local_id);
            }

            if has_prusti_attr(attrs, "ghost_begin") {
                self.ghost_begin.push(local_id);
            }

            if has_prusti_attr(attrs, "ghost_end") {
                self.ghost_end.push(local_id);
            }
        } else {
            // Don't collect specs "for" spec items

            // Collect external function specifications
            if has_extern_spec_attr(attrs) {
                let attr = read_prusti_attr("extern_spec", attrs).unwrap_or_default();
                let kind = prusti_specs::ExternSpecKind::try_from(attr).unwrap();
                self.extern_resolver
                    .add_extern_fn(fn_kind, fn_decl, body_id, span, id, kind);
            }

            // Collect procedure specifications
            if let Some(procedure_spec_ref) = get_procedure_spec_ids(def_id, attrs) {
                self.procedure_specs.insert(local_id, procedure_spec_ref);
            }
        }
    }

    fn visit_stmt(&mut self, stmt: &'tcx prusti_rustc_interface::hir::Stmt) {
        intravisit::walk_stmt(self, stmt);

        // Collect closure specifications
        if let prusti_rustc_interface::hir::StmtKind::Local(local) = stmt.kind {
            let attrs = self.tcx.hir().attrs(local.hir_id);
            if has_prusti_attr(attrs, "closure") {
                let init_expr = local.init.expect("closure on Local without assignment");
                let local_id = self.tcx.hir().local_def_id(init_expr.hir_id);
                let def_id = local_id.to_def_id();
                // Collect procedure specifications
                if let Some(procedure_spec_ref) = get_procedure_spec_ids(def_id, attrs) {
                    self.procedure_specs.insert(local_id, procedure_spec_ref);
                }
            }
        }
    }
}

fn get_type_id_from_impl_node(node: prusti_rustc_interface::hir::Node) -> Option<DefId> {
    if let prusti_rustc_interface::hir::Node::Item(item) = node {
        if let prusti_rustc_interface::hir::ItemKind::Impl(item_impl) = &item.kind {
            if let prusti_rustc_interface::hir::TyKind::Path(prusti_rustc_interface::hir::QPath::Resolved(_, path)) =
                item_impl.self_ty.kind
            {
                if let prusti_rustc_interface::hir::def::Res::Def(_, def_id) = path.res {
                    return Some(def_id);
                }
            }
        }
    }
    None
}
