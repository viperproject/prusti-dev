use super::common::*;
use crate::{environment::Environment, utils::has_model_attr, PrustiError};
use rustc_hir::{self as hir};
use rustc_middle::ty::TyCtxt;
use rustc_span::{MultiSpan, Span};

/// Checks the usage of the `.model()` method (induced by the `#[model]` macro) in non-spec code
pub struct IllegalModelUsagesChecker;

impl<'tcx> SpecCheckerStrategy<'tcx> for IllegalModelUsagesChecker {
    fn check(&self, env: &Environment<'tcx>) -> Vec<PrustiError> {
        let mut visit = ModelUsageVisitor {
            tcx: env.tcx(),
            model_usages_in_non_spec_code: Vec::default(),
        }
        .wrap_as_visitor();

        env.tcx().hir().walk_toplevel_module(&mut visit);

        let illegal_model_usages = visit.wrapped.model_usages_in_non_spec_code;
        illegal_model_usages
            .into_iter()
            .map(|model_span| {
                PrustiError::incorrect(
                    "using models in non-specification code is not allowed".to_string(),
                    MultiSpan::from_span(model_span),
                )
            })
            .collect()
    }
}

/// Checks for the usage of models in non-specification code
struct ModelUsageVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    model_usages_in_non_spec_code: Vec<Span>,
}

impl<'tcx> ModelUsageVisitor<'tcx> {
    fn get_called_method(&self, expr: &'tcx hir::Expr<'tcx>) -> Option<hir::HirId> {
        let maybe_method_def_id = self
            .tcx
            .typeck(expr.hir_id.owner)
            .type_dependent_def_id(expr.hir_id);
        if let Some(method_def_id) = maybe_method_def_id {
            let maybe_local_def_id = method_def_id.as_local();
            if let Some(local_def_id) = maybe_local_def_id {
                let decl_hir_id = self.tcx.hir().local_def_id_to_hir_id(local_def_id);
                return Some(decl_hir_id);
            }
        }
        None
    }
}

impl<'tcx> NonSpecExprVisitor<'tcx> for ModelUsageVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::MethodCall(_, _, call_span) = expr.kind {
            let maybe_method_decl_hir_id: Option<hir::HirId> = self.get_called_method(expr);

            if let Some(method_decl_hir_id) = maybe_method_decl_hir_id {
                let attrs = self.tcx.hir().attrs(method_decl_hir_id);

                if has_model_attr(attrs) {
                    self.model_usages_in_non_spec_code.push(call_span);
                }
            }
        }
    }
}
