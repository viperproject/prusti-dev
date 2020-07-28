use prusti_specs::specifications::common;
use prusti_specs::specifications::json;
use rustc_hir::BodyId;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir, ty::{self, TyCtxt}};
use rustc_span::Span;
use std::collections::HashMap;

pub use common::{ExpressionId, SpecType, SpecificationId};

/// A specification that has no types associated with it.
pub type Specification<'tcx> = common::Specification<ExpressionId, LocalDefId, (mir::Local, ty::Ty<'tcx>)>;
/// A set of untyped specifications associated with a single element.
pub type SpecificationSet<'tcx> = common::SpecificationSet<ExpressionId, LocalDefId, (mir::Local, ty::Ty<'tcx>)>;
/// A set of untyped specifications associated with a loop.
pub type LoopSpecification<'tcx> = common::LoopSpecification<ExpressionId, LocalDefId, (mir::Local, ty::Ty<'tcx>)>;
/// A set of untyped specifications associated with a procedure.
pub type ProcedureSpecification<'tcx> = common::ProcedureSpecification<ExpressionId, LocalDefId, (mir::Local, ty::Ty<'tcx>)>;
/// A map of untyped specifications for a specific crate.
pub type SpecificationMap<'tcx> = HashMap<common::SpecificationId, SpecificationSet<'tcx>>;
/// An assertion that has no types associated with it.
pub type Assertion<'tcx> = common::Assertion<ExpressionId, LocalDefId, (mir::Local, ty::Ty<'tcx>)>;
/// An assertion kind that has no types associated with it.
pub type AssertionKind<'tcx> = common::AssertionKind<ExpressionId, LocalDefId, (mir::Local, ty::Ty<'tcx>)>;
/// An expression that has no types associated with it.
pub type Expression = common::Expression<ExpressionId, LocalDefId>;
/// A trigger set that has no types associated with it.
pub type TriggerSet = common::TriggerSet<ExpressionId, LocalDefId>;
/// For all variables that have no types associated with it.
pub type ForAllVars<'tcx> = common::ForAllVars<ExpressionId, (mir::Local, ty::Ty<'tcx>)>;
/// A trigger that has no types associated with it.
pub type Trigger = common::Trigger<ExpressionId, LocalDefId>;

pub trait Spanned<'tcx> {
    fn get_spans(&self, tcx: TyCtxt<'tcx>) -> Vec<Span>;
}

impl<'tcx> Spanned<'tcx> for Expression {
    fn get_spans(&self, tcx: TyCtxt<'tcx>) -> Vec<Span> {
        vec![tcx.def_span(self.expr)]
    }
}

impl<'tcx> Spanned<'tcx> for Assertion<'tcx> {
    fn get_spans(&self, tcx: TyCtxt<'tcx>) -> Vec<Span> {
        match *self.kind {
            AssertionKind::Expr(ref assertion_expr) => assertion_expr.get_spans(tcx),
            AssertionKind::And(ref assertions) => {
                assertions
                    .iter()
                    .flat_map(|a| a.get_spans(tcx))
                    .collect()
            }
            AssertionKind::Implies(ref lhs, ref rhs) => {
                let mut spans = lhs.get_spans(tcx);
                spans.extend(rhs.get_spans(tcx));
                spans
            }
            AssertionKind::ForAll(ref _vars, ref _trigger_set, ref body) => {
                // FIXME: include the variables
                body.get_spans(tcx)
            }
            AssertionKind::TypeCond(ref _vars, ref body) => {
                // FIXME: include the conditions
                body.get_spans(tcx)
            }
        }
    }
}

pub trait StructuralToTyped<'tcx, Target> {
    fn to_typed(self, typed_expressions: &HashMap<String, LocalDefId>, tcx: TyCtxt<'tcx>) -> Target;
}

impl<'tcx> StructuralToTyped<'tcx, Expression> for json::Expression {
    fn to_typed(self, typed_expressions: &HashMap<String, LocalDefId>, tcx: TyCtxt<'tcx>) -> Expression {
        let local_id = typed_expressions[&format!("{}_{}", self.spec_id, self.expr_id)];
        Expression {
            spec_id: self.spec_id,
            id: self.expr_id,
            expr: local_id,
        }
    }
}

impl<'tcx> StructuralToTyped<'tcx, TriggerSet> for json::TriggerSet {
    fn to_typed(self, typed_expressions: &HashMap<String, LocalDefId>, tcx: TyCtxt<'tcx>) -> TriggerSet {
        common::TriggerSet(
            self.0
                .into_iter()
                .map(|x| x.to_typed(typed_expressions, tcx))
                .collect()
        )
    }
}

impl<'tcx> StructuralToTyped<'tcx, Trigger> for json::Trigger {
    fn to_typed(self, typed_expressions: &HashMap<String, LocalDefId>, tcx: TyCtxt<'tcx>) -> Trigger {
        common::Trigger(
            self.0
                .into_iter()
                .map(|x| x.to_typed(typed_expressions, tcx))
                .collect()
        )
    }
}

impl<'tcx> StructuralToTyped<'tcx, ForAllVars<'tcx>> for json::ForAllVars {
    fn to_typed(self, typed_expressions: &HashMap<String, LocalDefId>, tcx: TyCtxt<'tcx>) -> ForAllVars<'tcx> {
        let local_id = typed_expressions[&format!("{}_{}", self.spec_id, self.expr_id)];
        let (body, _) = tcx.mir_validated(ty::WithOptConstParam::unknown(local_id));
        let body = body.borrow();

        // the first argument to the node is the closure itself and the
        // following ones are the variables; therefore, we need to skip
        // the first one
        let vars: Vec<(mir::Local, ty::Ty)> = body
            .args_iter()
            .skip(1)
            .map(|arg| (arg, body.local_decls
                           .get(arg)
                           .unwrap()
                           .ty
                           .clone()))
            .collect();

        assert!(body.arg_count-1 == self.count);
        assert_eq!(vars.len(), self.count);
        return ForAllVars {
            spec_id: self.spec_id,
            id: self.expr_id,
            vars
        }
    }
}

impl<'tcx> StructuralToTyped<'tcx, AssertionKind<'tcx>> for json::AssertionKind {
    fn to_typed(self, typed_expressions: &HashMap<String, LocalDefId>, tcx: TyCtxt<'tcx>) -> AssertionKind<'tcx> {
        use json::AssertionKind::*;
        match self {
            Expr(expr) => AssertionKind::Expr(expr.to_typed(typed_expressions, tcx)),
            And(assertions) => AssertionKind::And(
                assertions.into_iter()
                          .map(|assertion| assertion.to_typed(typed_expressions, tcx))
                          .collect()
            ),
            Implies(lhs, rhs) => AssertionKind::Implies(
                lhs.to_typed(typed_expressions, tcx),
                rhs.to_typed(typed_expressions, tcx)
            ),
            ForAll(vars, body, triggers) => AssertionKind::ForAll(
                vars.to_typed(typed_expressions, tcx),
                triggers.to_typed(typed_expressions, tcx),
                body.to_typed(typed_expressions, tcx),
            )
        }
    }
}

impl<'tcx> StructuralToTyped<'tcx, Assertion<'tcx>> for json::Assertion {
    fn to_typed(self, typed_expressions: &HashMap<String, LocalDefId>, tcx: TyCtxt<'tcx>) -> Assertion<'tcx> {
        Assertion {
            kind: box self.kind.to_typed(typed_expressions, tcx),
        }
    }
}
