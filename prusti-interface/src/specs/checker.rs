use log::{debug};
use rustc_hir::{
    self as hir,
    def_id::{DefId},
    intravisit::{self, Visitor},
};
use rustc_middle::{hir::map::Map, ty::TyCtxt};
use rustc_span::{MultiSpan, Span};

use std::collections::{HashMap, HashSet};

use crate::{
    environment::Environment,
    utils::{has_prusti_attr, has_spec_only_attr},
    PrustiError,
};
use crate::utils::has_abstract_predicate_attr;

/// Checker visitor for the specifications. Currently checks that `predicate!`
/// functions are never used from non-specification code, but more checks may follow.
#[derive(Default)]
pub struct SpecChecker {
    /// Map of the `DefID`s to the `Span`s of `predicate!` functions found in the first pass.
    predicates: HashMap<DefId, Span>,

    /// Span of use and definition of predicates used outside of specifications, collected in the second pass.
    pred_usages: Vec<(Span, Span)>,

    /// Set of abstract predicates (appearing in traits) which have bodies
    abstract_predicate_with_bodies: HashSet<DefId>,
}

/// First predicate checks visitor: collect all function items that originate
/// from predicates
/// Additionally, this visitor collects all abstract trait predicates which have bodies
struct CollectPredicatesVisitor<'v, 'tcx> {
    tcx: TyCtxt<'tcx>,

    predicates: &'v mut HashMap<DefId, Span>,
    abstract_predicate_with_bodies: &'v mut HashSet<DefId>,
}

impl<'v, 'tcx> intravisit::Visitor<'tcx> for CollectPredicatesVisitor<'v, 'tcx> {
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

    fn visit_trait_item(&mut self, ti: &'tcx hir::TraitItem<'tcx>) {
        let def_id = ti.def_id.to_def_id();
        let attrs = self.tcx.get_attrs(def_id);

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
struct CheckPredicatesVisitor<'v, 'tcx> {
    tcx: TyCtxt<'tcx>,

    predicates: &'v HashMap<DefId, Span>,
    pred_usages: &'v mut Vec<(Span, Span)>,
}

impl<'v, 'tcx> Visitor<'tcx> for CheckPredicatesVisitor<'v, 'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_item(&mut self, i: &'tcx hir::Item<'tcx>) {
        // restrict to "interesting" sub-nodes to visit, i.e. anything that
        // could be or contain call (or other usage of predicate) expressions
        use hir::ItemKind::*;

        match i.kind {
            Static(_, _, _) | Fn(_, _, _) | Mod(_) | Impl { .. } => {
                intravisit::walk_item(self, i);
            }
            _ => {
                // don't recurse into e.g. struct decls, type aliases, consts etc.
            }
        }
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

        intravisit::walk_expr(self, ex);
    }

    fn visit_fn(
        &mut self,
        fk: intravisit::FnKind<'tcx>,
        fd: &'tcx hir::FnDecl<'tcx>,
        b: hir::BodyId,
        s: Span,
        id: hir::HirId,
    ) {
        // Stop checking inside `prusti::spec_only` functions
        let attrs = self.tcx.hir().attrs(id);
        if has_spec_only_attr(attrs) {
            return;
        }

        intravisit::walk_fn(self, fk, fd, b, s, id);
    }
}

impl<'tcx> SpecChecker {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn check_predicate_usages(&mut self, tcx: TyCtxt<'tcx>) {
        let mut collect = CollectPredicatesVisitor {
            tcx,
            predicates: &mut self.predicates,
            abstract_predicate_with_bodies: &mut self.abstract_predicate_with_bodies,
        };
        tcx.hir().walk_toplevel_module(&mut collect);
        tcx.hir().walk_attributes(&mut collect);

        let mut visit = CheckPredicatesVisitor {
            tcx: collect.tcx,
            predicates: &self.predicates,
            pred_usages: &mut self.pred_usages,
        };
        tcx.hir().walk_toplevel_module(&mut visit);
        tcx.hir().walk_attributes(&mut visit);

        debug!("Predicate funcs: {:?}", self.predicates);
        debug!("Abstract predicates with bodies: {:?}", self.abstract_predicate_with_bodies);
        debug!("Predicate usages: {:?}", self.pred_usages);
    }

    pub fn report_errors(&self, env: &Environment<'tcx>) {
        for def_id in &self.abstract_predicate_with_bodies {
            let span = env.tcx().def_span(def_id);
            PrustiError::incorrect(
                "abstract predicates must not have bodies".to_string(),
                MultiSpan::from_span(span),
            ).emit(env);
        }

        for &(usage_span, def_span) in &self.pred_usages {
            PrustiError::incorrect(
                "using predicate from non-specification code is not allowed".to_string(),
                MultiSpan::from_span(usage_span),
            )
            .add_note("this is a specification-only predicate function", Some(def_span))
            .emit(env);
        }
    }
}
