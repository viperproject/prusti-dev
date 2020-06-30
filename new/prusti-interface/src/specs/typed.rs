use prusti_specs::specifications::common;
use prusti_specs::specifications::json;
use rustc_hir::BodyId;
use rustc_middle::ty::{TyCtxt, TyKind, TyS};
use std::collections::HashMap;

pub use common::{ExpressionId, SpecType, SpecificationId};

// TODO: Replace with a proper one.
type Arg = ();

/// A specification that has no types associated with it.
pub type Specification = common::Specification<ExpressionId, BodyId, Arg>;
/// A set of untyped specifications associated with a single element.
pub type SpecificationSet = common::SpecificationSet<ExpressionId, BodyId, Arg>;
/// A set of untyped specifications associated with a loop.
pub type LoopSpecification = common::LoopSpecification<ExpressionId, BodyId, Arg>;
/// A set of untyped specifications associated with a procedure.
pub type ProcedureSpecification = common::ProcedureSpecification<ExpressionId, BodyId, Arg>;
/// A map of untyped specifications for a specific crate.
pub type SpecificationMap = HashMap<common::SpecificationId, SpecificationSet>;
/// An assertion that has no types associated with it.
pub type Assertion = common::Assertion<ExpressionId, BodyId, Arg>;
/// An assertion kind that has no types associated with it.
pub type AssertionKind = common::AssertionKind<ExpressionId, BodyId, Arg>;
/// An expression that has no types associated with it.
pub type Expression = common::Expression<ExpressionId, BodyId>;
/// A trigger set that has no types associated with it.
pub type TriggerSet = common::TriggerSet<ExpressionId, BodyId>;
/// For all variables that have no types associated with it.
pub type ForAllVars = common::ForAllVars<ExpressionId, Arg>;
/// A trigger that has no types associated with it.
pub type Trigger = common::Trigger<ExpressionId, BodyId>;

pub trait StructuralToTyped<Target> {
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt) -> Target;
}

impl StructuralToTyped<Expression> for json::Expression {
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt) -> Expression {
        let body_id = typed_expressions[&format!("{}_{}", self.spec_id, self.expr_id)];
        Expression {
            spec_id: self.spec_id,
            id: self.expr_id,
            expr: body_id,
        }
    }
}

impl StructuralToTyped<TriggerSet> for json::TriggerSet {
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt) -> TriggerSet {
        common::TriggerSet(
            self.0
                .into_iter()
                .map(|x| x.to_typed(typed_expressions, tcx))
                .collect()
        )
    }
}

impl StructuralToTyped<Trigger> for json::Trigger {
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt) -> Trigger {
        common::Trigger(
            self.0
                .into_iter()
                .map(|x| x.to_typed(typed_expressions, tcx))
                .collect()
        )
    }
}

impl StructuralToTyped<ForAllVars> for json::ForAllVars {
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt) -> ForAllVars {
        let (body, _) = tcx.mir_validated(
            typed_expressions[&format!("{}_{}", self.spec_id, self.expr_id)].hir_id.owner
        );
        let body = body.steal();

        let last_idx = body.local_decls.last().unwrap();
        let last = body.local_decls.get(last_idx).unwrap();
        if let TyKind::Closure(_, substs) = last.ty.kind {
            if let TyKind::FnPtr(fnptr) = substs.type_at(1).kind {
                let args = fnptr.no_bound_vars().unwrap().inputs()[0];
                if let TyKind::Tuple(items) = args.kind {
                    assert!(items.len() == self.count);
                    return ForAllVars {
                        spec_id: self.spec_id,
                        id: self.expr_id,
                        vars: items.iter().collect()
                    };
                }
                else {
                    unreachable!();
                }
            }
            else {
                unreachable!();
            }
        }
        else {
            unreachable!();
        }


    }
}

impl StructuralToTyped<AssertionKind> for json::AssertionKind {
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt) -> AssertionKind {
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

impl StructuralToTyped<Assertion> for json::Assertion {
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt) -> Assertion {
        Assertion {
            kind: box self.kind.to_typed(typed_expressions, tcx),
        }
    }
}
