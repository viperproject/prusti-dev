use super::common::*;
use crate::{
    environment::{EnvQuery, Environment},
    utils::{has_abstract_predicate_attr, has_prusti_attr},
    PrustiError,
};
use log::debug;
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    errors::MultiSpan,
    hir::{self as hir, def_id::DefId, intravisit},
    middle::{hir::map::Map, ty::TyCtxt},
    span::Span,
};

/// Checks for illegal predicate usages
pub struct IllegalPredicateUsagesChecker;

impl<'tcx> SpecCheckerStrategy<'tcx> for IllegalPredicateUsagesChecker {
    fn check(&self, env: &Environment<'tcx>) -> Vec<PrustiError> {
        let collected_predicates = self.collect_predicates(env.query);
        debug!("Predicate funcs: {:?}", collected_predicates.predicates);
        debug!(
            "Abstract predicates with bodies: {:?}",
            collected_predicates.abstract_predicate_with_bodies
        );
        let illegal_pred_usages =
            self.collect_illegal_predicate_usages(collected_predicates.predicates, env.query);
        debug!("Predicate usages: {:?}", illegal_pred_usages);

        // TODO: check behavioral subtyping of implemented predicates against default implementation

        let illegal_usage_errors = illegal_pred_usages
            .into_iter()
            .map(|(usage_span, def_span)| {
                PrustiError::incorrect(
                    "using predicate from non-specification code is not allowed".to_string(),
                    MultiSpan::from_span(usage_span),
                )
                .add_note(
                    "this is a specification-only predicate function",
                    Some(def_span),
                )
            });

        illegal_usage_errors.collect()
    }
}

impl IllegalPredicateUsagesChecker {
    /// Map of the `DefID`s to the `Span`s of `predicate!` functions found in the first pass.
    fn collect_predicates<'tcx>(
        &self,
        env_query: EnvQuery<'tcx>,
    ) -> CollectPredicatesVisitor<'tcx> {
        let mut collect = CollectPredicatesVisitor {
            env_query,
            predicates: FxHashMap::default(),
            abstract_predicate_with_bodies: FxHashSet::default(),
        };
        env_query.hir().walk_toplevel_module(&mut collect);
        env_query.hir().walk_attributes(&mut collect);

        collect
    }

    /// Span of use and definition of predicates used outside of specifications, collected in the second pass.
    fn collect_illegal_predicate_usages(
        &self,
        predicates: FxHashMap<DefId, Span>,
        env_query: EnvQuery,
    ) -> Vec<(Span, Span)> {
        let mut visit = CheckPredicatesVisitor {
            env_query,
            predicates,
            pred_usages: Vec::new(),
        }
        .wrap_as_visitor();

        env_query.hir().walk_toplevel_module(&mut visit);
        env_query.hir().walk_attributes(&mut visit);

        visit.wrapped.pred_usages
    }
}

/// First predicate checks visitor: collect all function items that originate
/// from predicates
struct CollectPredicatesVisitor<'tcx> {
    env_query: EnvQuery<'tcx>,
    predicates: FxHashMap<DefId, Span>,
    abstract_predicate_with_bodies: FxHashSet<DefId>,
}

impl<'tcx> intravisit::Visitor<'tcx> for CollectPredicatesVisitor<'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = prusti_rustc_interface::middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.env_query.hir()
    }

    fn visit_fn(
        &mut self,
        fk: intravisit::FnKind<'tcx>,
        fd: &'tcx hir::FnDecl<'tcx>,
        b: hir::BodyId,
        s: Span,
        id: hir::HirId,
    ) {
        // collect this fn's DefId if predicate function
        let attrs = self.env_query.get_local_attributes(id);
        if has_prusti_attr(attrs, "pred_spec_id_ref") {
            let def_id = self.env_query.as_local_def_id(id).to_def_id();
            self.predicates.insert(def_id, s);
        }

        intravisit::walk_fn(self, fk, fd, b, id);
    }

    fn visit_trait_item(&mut self, ti: &'tcx hir::TraitItem<'tcx>) {
        let def_id = ti.owner_id.def_id.to_def_id();
        let attrs = self.env_query.get_local_attributes(ti.owner_id.def_id);

        if has_abstract_predicate_attr(attrs) {
            let span = self.env_query.get_def_span(def_id);
            self.predicates.insert(def_id, span);
        } else if has_prusti_attr(attrs, "pred_spec_id_ref") {
            if let hir::TraitItemKind::Fn(_, hir::TraitFn::Provided(_)) = &ti.kind {
                self.abstract_predicate_with_bodies.insert(def_id);
            }
        }

        intravisit::walk_trait_item(self, ti);
    }
}

/// Second predicate checks visitor: check any references to predicate functions
/// from non-specification code
struct CheckPredicatesVisitor<'tcx> {
    env_query: EnvQuery<'tcx>,

    predicates: FxHashMap<DefId, Span>,
    pred_usages: Vec<(Span, Span)>,
}

impl<'v, 'tcx: 'v> NonSpecExprVisitor<'tcx> for CheckPredicatesVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.env_query.tcx()
    }

    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>) {
        let owner_def_id = ex.hir_id.owner.def_id;

        // General check: The "path" of a predicate doesn't appear anywhere
        // (e.g. as in a function call or an argument when we pass the predicate to another function)
        if let hir::ExprKind::Path(ref path) = ex.kind {
            if self.env_query.has_body(owner_def_id) {
                let res = self
                    .env_query
                    .tcx()
                    .typeck(owner_def_id)
                    .qpath_res(path, ex.hir_id);
                if let hir::def::Res::Def(_, def_id) = res {
                    if let Some(pred_def_span) = self.predicates.get(&def_id) {
                        self.pred_usages.push((ex.span, *pred_def_span));
                    }
                }
            }
        }

        // When we deal with predicates in impls, the above path resolving is not enough,
        // i.e. when Foo::bar is a predicate and we call `foo.bar()` on some `foo: Foo`,
        // we do not observe the called def id `bar` via path resolution.
        if self.env_query.has_body(owner_def_id) {
            let resolved_called_method = self
                .env_query
                .tcx()
                .typeck(owner_def_id)
                .type_dependent_def_id(ex.hir_id);
            if let Some(called_def_id) = resolved_called_method {
                if !self.env_query.tcx().is_constructor(called_def_id) {
                    if let Some(pred_def_span) = self.predicates.get(&called_def_id) {
                        self.pred_usages.push((ex.span, *pred_def_span));
                    }
                }
            }
        }
    }
}
