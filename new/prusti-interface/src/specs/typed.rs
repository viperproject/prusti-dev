use prusti_specs::specifications::common;
use prusti_specs::specifications::json;
use rustc_hir::BodyId;
use rustc_middle::ty::{TyCtxt, TyKind};
use std::collections::HashMap;

pub use common::{ExpressionId, SpecType, SpecificationId};

/// A specification that has no types associated with it.
pub type Specification<'tcx> = common::Specification<ExpressionId, BodyId, TyKind<'tcx>>;
/// A set of untyped specifications associated with a single element.
pub type SpecificationSet<'tcx> = common::SpecificationSet<ExpressionId, BodyId, TyKind<'tcx>>;
/// A set of untyped specifications associated with a loop.
pub type LoopSpecification<'tcx> = common::LoopSpecification<ExpressionId, BodyId, TyKind<'tcx>>;
/// A set of untyped specifications associated with a procedure.
pub type ProcedureSpecification<'tcx> = common::ProcedureSpecification<ExpressionId, BodyId, TyKind<'tcx>>;
/// A map of untyped specifications for a specific crate.
pub type SpecificationMap<'tcx> = HashMap<common::SpecificationId, SpecificationSet<'tcx>>;
/// An assertion that has no types associated with it.
pub type Assertion<'tcx> = common::Assertion<ExpressionId, BodyId, TyKind<'tcx>>;
/// An assertion kind that has no types associated with it.
pub type AssertionKind<'tcx> = common::AssertionKind<ExpressionId, BodyId, TyKind<'tcx>>;
/// An expression that has no types associated with it.
pub type Expression = common::Expression<ExpressionId, BodyId>;
/// A trigger set that has no types associated with it.
pub type TriggerSet = common::TriggerSet<ExpressionId, BodyId>;
/// For all variables that have no types associated with it.
pub type ForAllVars<'tcx> = common::ForAllVars<ExpressionId, TyKind<'tcx>>;
/// A trigger that has no types associated with it.
pub type Trigger = common::Trigger<ExpressionId, BodyId>;

pub trait StructuralToTyped<'tcx, Target> {
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt<'tcx>) -> Target;
}

impl<'tcx> StructuralToTyped<'tcx, Expression> for json::Expression {
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt<'tcx>) -> Expression {
        let body_id = typed_expressions[&format!("{}_{}", self.spec_id, self.expr_id)];
        Expression {
            spec_id: self.spec_id,
            id: self.expr_id,
            expr: body_id,
        }
    }
}

impl<'tcx> StructuralToTyped<'tcx, TriggerSet> for json::TriggerSet {
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt<'tcx>) -> TriggerSet {
        common::TriggerSet(
            self.0
                .into_iter()
                .map(|x| x.to_typed(typed_expressions, tcx))
                .collect()
        )
    }
}

impl<'tcx> StructuralToTyped<'tcx, Trigger> for json::Trigger {
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt<'tcx>) -> Trigger {
        common::Trigger(
            self.0
                .into_iter()
                .map(|x| x.to_typed(typed_expressions, tcx))
                .collect()
        )
    }
}

impl<'tcx> StructuralToTyped<'tcx, ForAllVars<'tcx>> for json::ForAllVars {
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt<'tcx>) -> ForAllVars<'tcx> {
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
                    let mut vars = vec![];
                    for item in items {
                        vars.push(item.expect_ty().kind.clone());
                    }
                    return ForAllVars {
                        spec_id: self.spec_id,
                        id: self.expr_id,
                        vars
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

impl<'tcx> StructuralToTyped<'tcx, AssertionKind<'tcx>> for json::AssertionKind {
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt<'tcx>) -> AssertionKind<'tcx> {
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
    fn to_typed(self, typed_expressions: &HashMap<String, rustc_hir::BodyId>, tcx: TyCtxt<'tcx>) -> Assertion<'tcx> {
        Assertion {
            kind: box self.kind.to_typed(typed_expressions, tcx),
        }
    }
}
