use prusti_rustc_interface::hir::{
    self as hir,
    def_id::DefId,
    intravisit,
};
use prusti_rustc_interface::middle::{hir::map::Map, ty::TyCtxt};
use prusti_rustc_interface::span::Span;
use prusti_rustc_interface::errors::MultiSpan;
use super::common::*;
use crate::{
    environment::Environment,
    utils::{has_prusti_attr},
    PrustiError,
};
use std::collections::{HashMap, HashSet};
use log::debug;
use crate::utils::has_abstract_predicate_attr;

/// Checks for illegal predicate usages
#[derive(Default)]
pub struct IllegalPredicateUsagesChecker;

impl<'tcx> SpecCheckerStrategy<'tcx> for IllegalPredicateUsagesChecker {
    fn check(&self, env: &Environment<'tcx>) -> Vec<PrustiError> {
        let collected_predicates = self.collect_predicates(env);
        debug!("Predicate funcs: {:?}", collected_predicates.predicates);
        debug!("Abstract predicates with bodies: {:?}", collected_predicates.abstract_predicate_with_bodies);
        let illegal_pred_usages = self.collect_illegal_predicate_usages(collected_predicates.predicates, env);
        debug!("Predicate usages: {:?}", illegal_pred_usages);

        let body_errors = collected_predicates.abstract_predicate_with_bodies.into_iter().map(|def_id| {
            let span = env.tcx().def_span(def_id);
            PrustiError::incorrect(
                "abstract predicates must not have bodies".to_string(),
                MultiSpan::from_span(span),
            )
        });

        let illegal_usage_errors = illegal_pred_usages.into_iter().map(|(usage_span, def_span)|
            PrustiError::incorrect(
                "using predicate from non-specification code is not allowed".to_string(),
                MultiSpan::from_span(usage_span),
            ).add_note(
                "this is a specification-only predicate function",
                Some(def_span),
            )
        );

        body_errors.chain(illegal_usage_errors).collect()
    }
}

impl IllegalPredicateUsagesChecker {
    /// Map of the `DefID`s to the `Span`s of `predicate!` functions found in the first pass.
    fn collect_predicates<'tcx>(&self, env: &Environment<'tcx>) -> CollectPredicatesVisitor<'tcx> {
        let mut collect = CollectPredicatesVisitor {
            tcx: env.tcx(),
            predicates: HashMap::new(),
            abstract_predicate_with_bodies: HashSet::new(),
        };
        env.tcx().hir().walk_toplevel_module(&mut collect);
        env.tcx().hir().walk_attributes(&mut collect);

        collect
    }

    /// Span of use and definition of predicates used outside of specifications, collected in the second pass.
    fn collect_illegal_predicate_usages<'tcx>(&self, predicates: HashMap<DefId, Span>, env: &Environment<'tcx>) -> Vec<(Span, Span)> {
        let mut visit = CheckPredicatesVisitor {
            tcx: env.tcx(),
            predicates,
            pred_usages: Vec::new(),
        }.wrap_as_visitor();

        env.tcx().hir().walk_toplevel_module(&mut visit);
        env.tcx().hir().walk_attributes(&mut visit);

        visit.wrapped.pred_usages
    }
}

/// First predicate checks visitor: collect all function items that originate
/// from predicates
struct CollectPredicatesVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    predicates: HashMap<DefId, Span>,
    abstract_predicate_with_bodies: HashSet<DefId>,
}

impl<'tcx> intravisit::Visitor<'tcx> for CollectPredicatesVisitor<'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter =prusti_rustc_interface::middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
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
        let attrs = self.tcx.hir().attrs(id);
        if has_prusti_attr(attrs, "pred_spec_id_ref") {
            let def_id = self.tcx.hir().local_def_id(id).to_def_id();
            self.predicates.insert(def_id, s);
        }

        intravisit::walk_fn(self, fk, fd, b, s, id);
    }

    fn visit_trait_item(&mut self, ti: &'tcx hir::TraitItem<'tcx>) {
        let def_id = ti.def_id.to_def_id();
        let attrs = crate::utils::get_local_attributes(self.tcx, ti.def_id);

        if has_abstract_predicate_attr(attrs) {
            let span = self.tcx.def_span(def_id);
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
    tcx: TyCtxt<'tcx>,

    predicates: HashMap<DefId, Span>,
    pred_usages: Vec<(Span, Span)>,
}

impl<'v, 'tcx: 'v> NonSpecExprVisitor<'tcx> for CheckPredicatesVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>) {
        let owner_def_id = ex.hir_id.owner;

        // General check: The "path" of a predicate doesn't appear anywhere
        // (e.g. as in a function call or an argument when we pass the predicate to another function)
        if let hir::ExprKind::Path(ref path) = ex.kind {
            if self.tcx.is_mir_available(owner_def_id) && !self.tcx.is_constructor(owner_def_id.to_def_id()) {
                let res = self.tcx.typeck(owner_def_id).qpath_res(path, ex.hir_id);
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
        if self.tcx.is_mir_available(owner_def_id) && !self.tcx.is_constructor(owner_def_id.to_def_id()) {
            let resolved_called_method = self.tcx.typeck(owner_def_id).type_dependent_def_id(ex.hir_id);
            if let Some(called_def_id) = resolved_called_method {
                if !self.tcx.is_constructor(called_def_id) {
                    if let Some(pred_def_span) = self.predicates.get(&called_def_id) {
                        self.pred_usages.push((ex.span, *pred_def_span));
                    }
                }
            }
        }
    }
}
