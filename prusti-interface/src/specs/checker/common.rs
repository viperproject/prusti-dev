use prusti_rustc_interface::hir::{
    self as hir,
    intravisit::{self, Visitor},
};
use prusti_rustc_interface::middle::{hir::map::Map, ty::TyCtxt};
use prusti_rustc_interface::span::Span;
use crate::{
    environment::Environment,
    utils::has_spec_only_attr,
    PrustiError,
};

/// A strategy to check specifications
pub trait SpecCheckerStrategy<'tcx> {
    fn check(&self, env: &Environment<'tcx>) -> Vec<PrustiError>;
}

/// An `instravisit::Visitor` like trait which visits expressions in non-spec code.
///
/// Call the [wrap_as_visitor()] method to convert this type to an `instravisit::Visitor`
pub trait NonSpecExprVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx>;

    /// Delegate method for `intravisit::Visitor::visit_expr`.
    /// Note: This is just a delegate method, no call to `intravisit::walk_expr` needed.
    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>);

    /// Wraps this delegate into a type which implements `intravisit::Visitor`, calling the
    /// [visit_expr] delegate method.
    fn wrap_as_visitor(self) -> NonSpecExprVisitorWrapper<'tcx, Self> where Self: Sized {
        NonSpecExprVisitorWrapper {
            wrapped: self,
            _marker: std::marker::PhantomData,
        }
    }
}

/// A newtype wrapper for a [NonSpecExprVisitor] implementing type which implements the `intravisit::Visitor` trait
pub struct NonSpecExprVisitorWrapper<'tcx, T: NonSpecExprVisitor<'tcx>> {
    pub wrapped: T,
    _marker: std::marker::PhantomData<&'tcx T>
}

/// An implementation for `intravisit::Visitor` for [NonSpecExprVisitor] implementing types
impl<'tcx, T: NonSpecExprVisitor<'tcx>> Visitor<'tcx> for NonSpecExprVisitorWrapper<'tcx, T> {
    type Map = Map<'tcx>;
    type NestedFilter =prusti_rustc_interface::middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.wrapped.tcx().hir()
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
        self.wrapped.visit_expr(ex);
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
        let attrs = self.wrapped.tcx().hir().attrs(id);
        if has_spec_only_attr(attrs) {
            return;
        }

        intravisit::walk_fn(self, fk, fd, b, s, id);
    }
}