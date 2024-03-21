use crate::{
    environment::Environment,
    utils::{
        has_abstract_predicate_attr, has_extern_spec_attr, has_prusti_attr, has_to_model_fn_attr,
        read_prusti_attr, read_prusti_attrs,
    },
    PrustiError,
};
use log::debug;
use prusti_utils::config;
use prusti_rustc_interface::{
    ast::ast,
    data_structures::fx::FxHashMap,
    errors::MultiSpan,
    hir::{
        self,
        def_id::{DefId, LocalDefId},
        intravisit, FnRetTy,
    },
    middle::{hir::map::Map, ty},
    span::Span,
};
use std::{convert::TryInto, fmt::Debug};

pub mod checker;
pub mod cross_crate;
pub mod decoder;
pub mod encoder;
pub mod external;
pub mod typed;

use typed::SpecIdRef;

use crate::specs::{
    external::ExternSpecResolver,
    typed::{ProcedureSpecification, ProcedureSpecificationKind, SpecGraph, SpecificationItem},
};
use prusti_specs::specifications::common::SpecificationId;

#[derive(Debug)]
struct ProcedureSpecRefs {
    spec_id_refs: Vec<SpecIdRef>,
    pure: bool,
    abstract_predicate: bool,
    trusted: bool,
}

impl From<&ProcedureSpecRefs> for ProcedureSpecificationKind {
    fn from(refs: &ProcedureSpecRefs) -> Self {
        if refs.abstract_predicate {
            ProcedureSpecificationKind::Predicate(None)
        } else if refs.pure {
            ProcedureSpecificationKind::Pure
        } else {
            ProcedureSpecificationKind::Impure
        }
    }
}

#[derive(Debug, Default)]
struct TypeSpecRefs {
    invariants: Vec<LocalDefId>,
    trusted: bool,
    model: Option<(String, LocalDefId)>,
    countexample_print: Vec<(Option<String>, LocalDefId)>,
}

/// Specification collector, intended to be applied as a visitor over the crate
/// HIR. After the visit, [SpecCollector::build_def_specs] can be used to get back
/// a mapping of DefIds (which may not be local due to extern specs) to their
/// [typed::SpecificationSet], i.e. procedures, loop invariants, and structs.
pub struct SpecCollector<'a, 'tcx> {
    env: &'a mut Environment<'tcx>,
    extern_resolver: ExternSpecResolver<'tcx>,

    /// Map from specification IDs to their typed expressions.
    spec_functions: FxHashMap<SpecificationId, LocalDefId>,

    /// Map from functions/loops/types to their specifications.
    procedure_specs: FxHashMap<LocalDefId, ProcedureSpecRefs>,
    loop_specs: Vec<LocalDefId>,
    loop_variants: Vec<LocalDefId>,
    type_specs: FxHashMap<LocalDefId, TypeSpecRefs>,
    prusti_assertions: Vec<LocalDefId>,
    prusti_assumptions: Vec<LocalDefId>,
    prusti_refutations: Vec<LocalDefId>,
    ghost_begin: Vec<LocalDefId>,
    ghost_end: Vec<LocalDefId>,
}

impl<'a, 'tcx> SpecCollector<'a, 'tcx> {
    pub fn new(env: &'a mut Environment<'tcx>) -> Self {
        Self {
            extern_resolver: ExternSpecResolver::new(env),
            env,
            spec_functions: FxHashMap::default(),
            procedure_specs: FxHashMap::default(),
            loop_specs: vec![],
            loop_variants: vec![],
            type_specs: FxHashMap::default(),
            prusti_assertions: vec![],
            prusti_assumptions: vec![],
            prusti_refutations: vec![],
            ghost_begin: vec![],
            ghost_end: vec![],
        }
    }

    #[tracing::instrument(level = "debug", skip_all)]
    pub fn collect_specs(&mut self, hir: Map<'tcx>) {
        hir.walk_toplevel_module(self);
        hir.walk_attributes(self);
    }

    #[tracing::instrument(level = "debug", skip_all)]
    pub fn build_def_specs(&mut self) -> typed::DefSpecificationMap {
        let mut def_spec = typed::DefSpecificationMap::new();
        self.determine_procedure_specs(&mut def_spec);
        self.determine_extern_specs(&mut def_spec);
        self.determine_loop_specs(&mut def_spec);
        self.determine_type_specs(&mut def_spec);
        self.determine_prusti_assertions(&mut def_spec);
        self.determine_prusti_assumptions(&mut def_spec);
        self.determine_prusti_refutations(&mut def_spec);
        self.determine_ghost_begin_ends(&mut def_spec);
        // TODO: remove spec functions (make sure none are duplicated or left over)
        // Load all local spec MIR bodies, for export and later use
        self.ensure_local_mirs_fetched(&def_spec);
        def_spec
    }

    fn determine_procedure_specs(&self, def_spec: &mut typed::DefSpecificationMap) {
        for (local_id, refs) in self.procedure_specs.iter() {
            let mut spec = SpecGraph::new(ProcedureSpecification::empty(local_id.to_def_id()));

            // We do not want to create an empty kind.
            // This would lead to refinement inheritance if there is a trait involved.
            // Instead, we require the user to explicitly make annotations.
            spec.set_kind(refs.into());
            let mut kind_override = None;

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
                    SpecIdRef::Purity(spec_id) => {
                        spec.add_purity(*self.spec_functions.get(spec_id).unwrap(), self.env);
                    }
                    SpecIdRef::Pledge { lhs, rhs } => {
                        spec.add_pledge(typed::Pledge {
                            reference: None, // FIXME: Currently only `result` is supported.
                            lhs: lhs.as_ref().map(|spec_id| {
                                self.spec_functions.get(spec_id).unwrap().to_def_id()
                            }),
                            rhs: self.spec_functions.get(rhs).unwrap().to_def_id(),
                        });
                    }
                    SpecIdRef::Predicate(spec_id) => {
                        kind_override = Some(ProcedureSpecificationKind::Predicate(Some(
                            self.spec_functions.get(spec_id).unwrap().to_def_id(),
                        )));
                    }
                    SpecIdRef::Terminates(spec_id) => {
                        spec.set_terminates(*self.spec_functions.get(spec_id).unwrap());
                    }
                }
            }

            spec.set_trusted(refs.trusted);

            if let Some(kind) = kind_override {
                spec.set_kind(kind);
            }

            if !spec.specs_with_constraints.is_empty() && !*spec.base_spec.trusted.expect_inherent()
            {
                let span = self.env.query.get_def_span(*local_id);
                PrustiError::unsupported(
                    "Type-conditional spec refinements can only be applied to trusted functions",
                    MultiSpan::from(span),
                )
                .emit(&self.env.diagnostic);
            } else {
                def_spec.proc_specs.insert(local_id.to_def_id(), spec);
            }
        }
    }

    fn determine_extern_specs(&self, def_spec: &mut typed::DefSpecificationMap) {
        self.extern_resolver.check_errors(&self.env.diagnostic);
        for (extern_spec_decl, spec_id) in self.extern_resolver.extern_fn_map.iter() {
            let target_def_id = extern_spec_decl.get_target_def_id();

            if def_spec.proc_specs.contains_key(&target_def_id) {
                PrustiError::incorrect(
                    format!(
                        "external specification provided for {}, which already has a specification",
                        self.env.name.get_item_name(target_def_id)
                    ),
                    MultiSpan::from_span(self.env.query.get_def_span(spec_id)),
                )
                .emit(&self.env.diagnostic);
            }

            let spec = def_spec.proc_specs.remove(spec_id).unwrap();
            def_spec.proc_specs.insert(target_def_id, spec);
        }
    }

    fn determine_loop_specs(&self, def_spec: &mut typed::DefSpecificationMap) {
        for local_id in self.loop_specs.iter() {
            def_spec.loop_specs.insert(
                local_id.to_def_id(),
                typed::LoopSpecification::Invariant(*local_id),
            );
        }
        for local_id in self.loop_variants.iter() {
            def_spec.loop_specs.insert(
                local_id.to_def_id(),
                typed::LoopSpecification::Variant(*local_id),
            );
        }
    }

    fn determine_type_specs(&self, def_spec: &mut typed::DefSpecificationMap) {
        for (type_id, refs) in self.type_specs.iter() {
            if !refs.invariants.is_empty() && !prusti_utils::config::enable_type_invariants() {
                let span = self.env.query.get_def_span(*type_id);
                PrustiError::unsupported(
                    "Type invariants need to be enabled with the feature flag `enable_type_invariants`",
                    MultiSpan::from(span),
                )
                .emit(&self.env.diagnostic);
            }

            def_spec.type_specs.insert(
                type_id.to_def_id(),
                typed::TypeSpecification {
                    source: type_id.to_def_id(),
                    invariant: SpecificationItem::Inherent(
                        refs.invariants
                            .clone()
                            .into_iter()
                            .map(LocalDefId::to_def_id)
                            .collect(),
                    ),
                    trusted: SpecificationItem::Inherent(refs.trusted),
                    model: refs.model.clone(),
                    counterexample_print: refs.countexample_print.clone(),
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
    fn determine_prusti_refutations(&self, def_spec: &mut typed::DefSpecificationMap) {
        for local_id in self.prusti_refutations.iter() {
            def_spec.prusti_refutations.insert(
                local_id.to_def_id(),
                typed::PrustiRefutation {
                    refutation: *local_id,
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

    fn ensure_local_mirs_fetched(&mut self, def_spec: &typed::DefSpecificationMap) {
        let (specs, pure_fns, predicates) = def_spec.defid_for_export();
        for def_id in &specs {
            self.env.body.load_spec_body(def_id.expect_local());
        }
        for def_id in pure_fns {
            if self.env.query.has_body(def_id) {
                self.env.body.load_pure_fn_body(def_id.expect_local());
            }
        }
        for def_id in &predicates {
            self.env.body.load_predicate_body(def_id.expect_local());
        }

        let mut cl_visitor = CollectAllClosureDefsVisitor {
            map: self.env.query.hir(),
            result: Vec::new(),
        };
        for def_id in specs.iter().chain(predicates.iter()) {
            let body_id = self.env.query.hir().body_owned_by(def_id.expect_local());
            intravisit::Visitor::visit_nested_body(&mut cl_visitor, body_id);
        }
        for def_id in cl_visitor.result {
            self.env.body.load_closure_body(def_id);
        }
    }
}

/// Collects the LocalDefId of all closures. This is used to find all
/// quantifiers/triggers inside specs and predicates, so they can be
/// exported.
struct CollectAllClosureDefsVisitor<'tcx> {
    map: Map<'tcx>,
    result: Vec<LocalDefId>,
}

impl<'tcx> intravisit::Visitor<'tcx> for CollectAllClosureDefsVisitor<'tcx> {
    type NestedFilter = prusti_rustc_interface::middle::hir::nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.map
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Closure(hir::Closure { def_id, .. }) = expr.kind {
            self.result.push(*def_id);
        }

        intravisit::walk_expr(self, expr)
    }
}

fn parse_spec_id(spec_id: String, def_id: DefId) -> SpecificationId {
    spec_id
        .try_into()
        .unwrap_or_else(|_| panic!("cannot parse the spec_id attached to {def_id:?}"))
}

/// Returns true iff def_id points to a spec function (i.e. a function for
/// which we don't need polonius/borrowck facts)
pub fn is_spec_fn(tcx: ty::TyCtxt, def_id: DefId) -> bool {
    let attrs = tcx.get_attrs_unchecked(def_id);
    read_prusti_attr("spec_id", attrs).is_some()
}

#[tracing::instrument(level = "trace")]
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
        read_prusti_attrs("pure_spec_id_ref", attrs)
            .into_iter()
            .map(|raw_spec_id| SpecIdRef::Purity(parse_spec_id(raw_spec_id, def_id))),
    );
    spec_id_refs.extend(
        read_prusti_attrs("terminates_spec_id_ref", attrs)
            .into_iter()
            .map(|raw_spec_id| SpecIdRef::Terminates(parse_spec_id(raw_spec_id, def_id))),
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
    let is_predicate = matches!(spec_id_refs.last(), Some(SpecIdRef::Predicate(..)));
    debug!(
        "Function {:?} has specification ids {:?}",
        def_id, spec_id_refs
    );

    let pure = has_prusti_attr(attrs, "pure");
    let trusted = has_prusti_attr(attrs, "trusted")
        || (!is_predicate && config::opt_in_verification() && !has_prusti_attr(attrs, "verified"));
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
    type NestedFilter = prusti_rustc_interface::middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.env.query.hir()
    }

    fn visit_trait_item(&mut self, ti: &'tcx prusti_rustc_interface::hir::TraitItem) {
        intravisit::walk_trait_item(self, ti);

        let id = ti.hir_id();
        let local_id = self.env.query.as_local_def_id(id);
        let def_id = local_id.to_def_id();
        let attrs = self.env.query.get_local_attributes(ti.owner_id.def_id);

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
        local_id: LocalDefId,
    ) {
        intravisit::walk_fn(self, fn_kind, fn_decl, body_id, local_id);

        let def_id = local_id.to_def_id();
        let attrs = self.env.query.get_local_attributes(local_id);

        // Collect spec functions
        if let Some(raw_spec_id) = read_prusti_attr("spec_id", attrs) {
            let spec_id: SpecificationId = parse_spec_id(raw_spec_id, def_id);
            self.spec_functions.insert(spec_id, local_id);

            // Collect loop specifications
            if has_prusti_attr(attrs, "loop_body_invariant_spec") {
                self.loop_specs.push(local_id);
            }
            if has_prusti_attr(attrs, "loop_body_variant_spec") {
                self.loop_variants.push(local_id);
            }

            // TODO: (invariants and trusted flag) visit the struct itself?
            // For now, a method is used to mark the type as "trusted".

            // Collect type invariants
            if has_prusti_attr(attrs, "type_invariant_spec") {
                let self_id = fn_decl.inputs[0].hir_id;
                let hir = self.env.query.hir();
                let impl_id = hir.parent_id(hir.parent_id(self_id));
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
                let hir = self.env.query.hir();
                let impl_id = hir.parent_id(hir.parent_id(self_id));
                let type_id = get_type_id_from_impl_node(hir.get(impl_id)).unwrap();
                self.type_specs
                    .entry(type_id.as_local().unwrap())
                    .or_default()
                    .trusted = true;
            }

            //collect counterexamples type flag
            if has_prusti_attr(attrs, "counterexample_print") {
                let self_id = fn_decl.inputs[0].hir_id;
                let name = read_prusti_attr("counterexample_print", attrs);
                let hir = self.env.query.hir();
                let impl_id = hir.parent_id(hir.parent_id(self_id));
                let type_id = get_type_id_from_impl_node(hir.get(impl_id)).unwrap();
                self.type_specs
                    .entry(type_id.as_local().unwrap())
                    .or_default()
                    .countexample_print
                    .push((name, local_id));
            }

            if has_prusti_attr(attrs, "prusti_assertion") {
                self.prusti_assertions.push(local_id);
            }

            if has_prusti_attr(attrs, "prusti_assumption") {
                self.prusti_assumptions.push(local_id);
            }

            if has_prusti_attr(attrs, "prusti_refutation") {
                self.prusti_refutations.push(local_id);
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
                    .add_extern_fn(fn_kind, fn_decl, body_id, span, local_id, kind);
            }

            // Collect procedure specifications
            if let Some(procedure_spec_ref) = get_procedure_spec_ids(def_id, attrs) {
                self.procedure_specs.insert(local_id, procedure_spec_ref);
            }

            // Collect model type flag
            if has_to_model_fn_attr(attrs) {
                if let FnRetTy::Return(ty) = fn_decl.output {
                    if let Some(node) = self.env.query.hir().find(ty.hir_id) {
                        if let Some(model_ty_id) =
                            get_type_id_from_ty_node(node).and_then(|x| x.as_local())
                        {
                            if let Some(attr) = read_prusti_attr("type_models_to_model_fn", attrs) {
                                let self_id = fn_decl.inputs[0].hir_id;
                                let hir = self.env.query.hir();
                                let impl_id = hir.parent_id(hir.parent_id(self_id));
                                let type_id = get_type_id_from_impl_node(hir.get(impl_id)).unwrap();
                                if let Some(local_id) = type_id.as_local() {
                                    self.type_specs.entry(local_id).or_default().model =
                                        Some((attr, model_ty_id));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn visit_stmt(&mut self, stmt: &'tcx prusti_rustc_interface::hir::Stmt) {
        intravisit::walk_stmt(self, stmt);

        // Collect closure specifications
        if let prusti_rustc_interface::hir::StmtKind::Local(local) = stmt.kind {
            let attrs = self.env.query.get_local_attributes(local.hir_id);
            if has_prusti_attr(attrs, "closure") {
                let init_expr = local.init.expect("closure on Local without assignment");
                let local_id = self.env.query.as_local_def_id(init_expr.hir_id);
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
            if let prusti_rustc_interface::hir::TyKind::Path(
                prusti_rustc_interface::hir::QPath::Resolved(_, path),
            ) = item_impl.self_ty.kind
            {
                if let prusti_rustc_interface::hir::def::Res::Def(_, def_id) = path.res {
                    return Some(def_id);
                }
            }
        }
    }
    None
}

fn get_type_id_from_ty_node(node: prusti_rustc_interface::hir::Node) -> Option<DefId> {
    if let prusti_rustc_interface::hir::Node::Ty(ty) = node {
        if let prusti_rustc_interface::hir::TyKind::Path(
            prusti_rustc_interface::hir::QPath::Resolved(_, path),
        ) = ty.kind
        {
            if let prusti_rustc_interface::hir::def::Res::Def(_, def_id) = path.res {
                return Some(def_id);
            }
        }
    }
    None
}
