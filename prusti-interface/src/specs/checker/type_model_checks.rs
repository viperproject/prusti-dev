use super::common::*;
use crate::{
    environment::Environment,
    utils::{has_to_model_fn_attr, has_to_model_impl_attr},
    PrustiError,
};
use log::debug;
use rustc_hash::FxHashMap;
use prusti_rustc_interface::hir::{
    self as hir,
    def::{DefKind, Res},
    intravisit, HirId, QPath, TyKind,
};
use prusti_rustc_interface::middle::{hir::map::Map, ty::TyCtxt};
use prusti_rustc_interface::span::Span;
use prusti_rustc_interface::errors::MultiSpan;

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

                if has_to_model_fn_attr(attrs) {
                    self.model_usages_in_non_spec_code.push(call_span);
                }
            }
        }
    }
}

/// Checks whether modelled types have fields
pub struct ModelDefinedOnTypeWithoutFields;

impl<'tcx> SpecCheckerStrategy<'tcx> for ModelDefinedOnTypeWithoutFields {
    fn check(&self, env: &Environment<'tcx>) -> Vec<PrustiError> {
        let mut collect = CollectModelledTypes {
            tcx: env.tcx(),
            modelled_types: FxHashMap::default(),
        };
        env.tcx().hir().walk_toplevel_module(&mut collect);

        // Mark all modelled types as "dangerous", i.e. assume they have no fields
        let mut modelled_types_has_fields: FxHashMap<HirId, bool> = collect
            .modelled_types
            .iter()
            .map(|(ty_hir_id, _)| (*ty_hir_id, true))
            .collect();
        let mut type_names: FxHashMap<HirId, String> = FxHashMap::default();

        // Try to show that all modelled types have fields
        for (hir_id, self_ty) in collect.modelled_types {
            if let TyKind::Path(QPath::Resolved(_, path)) = &self_ty.kind {
                if let Res::Def(DefKind::Struct, def_id) = path.res {
                    let adt_def = env.tcx().adt_def(def_id);
                    let has_fields = adt_def.all_fields().next().is_some();
                    let def_path_str = env.tcx().def_path_str(def_id);
                    debug!("Type {} has fields: {}", def_path_str, has_fields);
                    modelled_types_has_fields.insert(hir_id, !has_fields);
                    type_names.insert(hir_id, def_path_str);
                }
            }
        }

        modelled_types_has_fields
            .into_iter()
            .filter(|(_, has_no_fields)| *has_no_fields)
            .map(|(ty_hir_id_without_fields, _)| {
                let span = env.tcx().def_span(ty_hir_id_without_fields.owner);
                let message_type_name = type_names.get(&ty_hir_id_without_fields).unwrap();
                let message = format!("Potentially dangerous type model definition for type '{}'", message_type_name);

                let mut warning = PrustiError::incorrect(
                        message,
                    MultiSpan::from_span(span),
                )
                .add_note(
                    "The modelled type could have no fields. This can lead to unsound verification code.",
                    env.tcx().def_ident_span(ty_hir_id_without_fields.owner),
                );
                warning.set_warning();
                warning
            })
            .collect()
    }
}

struct CollectModelledTypes<'tcx> {
    tcx: TyCtxt<'tcx>,
    modelled_types: FxHashMap<HirId, &'tcx hir::Ty<'tcx>>,
}

impl<'tcx> intravisit::Visitor<'tcx> for CollectModelledTypes<'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter =prusti_rustc_interface::middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        if let hir::ItemKind::Impl(_impl) = &item.kind {
            let attrs = self.tcx.hir().attrs(item.hir_id());
            if has_to_model_impl_attr(attrs) {
                self.modelled_types
                    .insert(_impl.self_ty.hir_id, _impl.self_ty);
            }
        }

        intravisit::walk_item(self, item);
    }
}
