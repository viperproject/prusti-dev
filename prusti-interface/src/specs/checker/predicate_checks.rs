use rustc_hir::{
    self as hir,
    def_id::DefId,
    intravisit,
};
use rustc_middle::{hir::map::Map, ty::TyCtxt};
use rustc_span::Span;
use rustc_errors::MultiSpan;
use super::common::*;
use crate::{
    environment::Environment,
    utils::{has_prusti_attr},
    PrustiError,
};
use std::collections::HashMap;
use log::debug;

/// Checks for illegal predicate usages
#[derive(Default)]
pub struct IllegalPredicateUsagesChecker;

impl<'tcx> SpecCheckerStrategy<'tcx> for IllegalPredicateUsagesChecker {
    fn check(&self, env: &Environment<'tcx>) -> Vec<PrustiError> {
        let collected_predicates = self.collect_predicates(env);
        debug!("Predicate funcs: {:?}", collected_predicates);
        let illegal_pred_usages = self.collect_illegal_predicate_usages(collected_predicates, env);
        debug!("Predicate usages: {:?}", illegal_pred_usages);

        illegal_pred_usages.into_iter().map(|(usage_span, def_span)|
            PrustiError::incorrect(
                "using predicate from non-specification code is not allowed".to_string(),
                MultiSpan::from_span(usage_span),
            ).add_note(
                "this is a specification-only predicate function",
                Some(def_span),
            )
        ).collect()
    }
}

impl IllegalPredicateUsagesChecker {
    /// Map of the `DefID`s to the `Span`s of `predicate!` functions found in the first pass.
    fn collect_predicates<'tcx>(&self, env: &Environment<'tcx>) -> HashMap<DefId, Span> {
        let mut collect = CollectPredicatesVisitor {
            tcx: env.tcx(),
            predicates: HashMap::new(),
        };
        env.tcx().hir().walk_toplevel_module(&mut collect);
        env.tcx().hir().walk_attributes(&mut collect);

        collect.predicates
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
}

impl<'tcx> intravisit::Visitor<'tcx> for CollectPredicatesVisitor<'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = rustc_middle::hir::nested_filter::All;

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
        if let hir::ExprKind::Path(ref path) = ex.kind {
            let def_id = ex.hir_id.owner;
            if self.tcx.is_mir_available(def_id) && !self.tcx.is_constructor(def_id.to_def_id()) {
                let res = self.tcx.typeck(def_id).qpath_res(path, ex.hir_id);
                if let hir::def::Res::Def(_, def_id) = res {
                    if let Some(pred_def_span) = self.predicates.get(&def_id) {
                        self.pred_usages.push((ex.span, *pred_def_span));
                    }
                }
            }
        }
    }
}
