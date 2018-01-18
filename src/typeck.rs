// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A module for extracting type information for specifications.
//!
//! Please see the `parser.rs` file for more information about
//! specifications.

use rustc;
use rustc::hir::{self, intravisit};
use rustc::ty::TyCtxt;
use rustc_driver::driver;
use syntax::{self, ast};
use std::collections::HashMap;
use specifications::{Assertion, AssertionKind, Expression, ExpressionId, ForAllVars,
                     Specification, SpecificationSet, Trigger, TypedAssertion, TypedSpecification,
                     TypedSpecificationMap, TypedTriggerSet, UntypedAssertion,
                     UntypedSpecification, UntypedSpecificationMap, UntypedTriggerSet};

/// Convert untyped specifications to typed specifications.
pub fn type_specifications(
    state: &mut driver::CompileState,
    untyped_specifications: UntypedSpecificationMap,
) -> TypedSpecificationMap {
    trace!("[type_specifications] enter");
    let tcx = state.tcx.unwrap();
    let mut collector = TypeCollector::new(tcx);
    intravisit::walk_crate(&mut collector, tcx.hir.krate());
    let typed_specifications = convert_to_typed(
        untyped_specifications,
        &collector.typed_expressions,
        &collector.typed_forallargs,
    );
    trace!("[type_specifications] exit");
    typed_specifications
}

fn type_trigger_set(
    trigger_set: UntypedTriggerSet,
    typed_expressions: &HashMap<ExpressionId, rustc::hir::Expr>,
) -> TypedTriggerSet {
    TypedTriggerSet::new(
        trigger_set
            .into_iter()
            .map(|trigger| {
                Trigger::new(
                    trigger
                        .into_iter()
                        .map(|term| Expression {
                            id: term.id,
                            expr: typed_expressions[&term.id].clone(),
                        })
                        .collect(),
                )
            })
            .collect(),
    )
}

fn type_assertion(
    assertion: UntypedAssertion,
    typed_expressions: &HashMap<ExpressionId, rustc::hir::Expr>,
    typed_forallargs: &HashMap<ExpressionId, Vec<rustc::hir::Arg>>,
) -> TypedAssertion {
    Assertion {
        kind: box {
            let assertion_kind = *assertion.kind;
            match assertion_kind {
                AssertionKind::Expr(expression) => AssertionKind::Expr(Expression {
                    id: expression.id,
                    expr: typed_expressions[&expression.id].clone(),
                }),
                AssertionKind::And(assertions) => AssertionKind::And(
                    assertions
                        .into_iter()
                        .map(|assertion| {
                            type_assertion(assertion, typed_expressions, typed_forallargs)
                        })
                        .collect(),
                ),
                AssertionKind::Implies(expression, assertion) => AssertionKind::Implies(
                    Expression {
                        id: expression.id,
                        expr: typed_expressions[&expression.id].clone(),
                    },
                    type_assertion(assertion, typed_expressions, typed_forallargs),
                ),
                AssertionKind::ForAll(vars, trigger_set, filter, body) => AssertionKind::ForAll(
                    ForAllVars {
                        id: vars.id,
                        vars: typed_forallargs[&vars.id].clone(),
                    },
                    type_trigger_set(trigger_set, typed_expressions),
                    Expression {
                        id: filter.id,
                        expr: typed_expressions[&filter.id].clone(),
                    },
                    Expression {
                        id: body.id,
                        expr: typed_expressions[&body.id].clone(),
                    },
                ),
            }
        },
    }
}

fn type_specification(
    specification: UntypedSpecification,
    typed_expressions: &HashMap<ExpressionId, rustc::hir::Expr>,
    typed_forallargs: &HashMap<ExpressionId, Vec<rustc::hir::Arg>>,
) -> TypedSpecification {
    Specification {
        typ: specification.typ,
        assertion: type_assertion(specification.assertion, typed_expressions, typed_forallargs),
    }
}

fn convert_to_typed(
    untyped_specifications: UntypedSpecificationMap,
    typed_expressions: &HashMap<ExpressionId, rustc::hir::Expr>,
    typed_forallargs: &HashMap<ExpressionId, Vec<rustc::hir::Arg>>,
) -> TypedSpecificationMap {
    let convert = |specs: Vec<UntypedSpecification>| {
        specs
            .into_iter()
            .map(|spec| type_specification(spec, typed_expressions, typed_forallargs))
            .collect()
    };
    untyped_specifications
        .into_iter()
        .map(|(id, untyped_specification)| match untyped_specification {
            SpecificationSet::Procedure(precondition, postcondition) => (
                id,
                SpecificationSet::Procedure(convert(precondition), convert(postcondition)),
            ),
            SpecificationSet::Loop(invariants) => (id, SpecificationSet::Loop(convert(invariants))),
        })
        .collect()
}

/// Visitor that collects typed expressions used in specifications.
struct TypeCollector<'a, 'tcx: 'a> {
    pub typed_expressions: HashMap<ExpressionId, rustc::hir::Expr>,
    pub typed_forallargs: HashMap<ExpressionId, Vec<rustc::hir::Arg>>,
    pub current_args: Option<Vec<rustc::hir::Arg>>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
}

impl<'a, 'tcx: 'a> TypeCollector<'a, 'tcx> {
    fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        Self {
            typed_expressions: HashMap::new(),
            typed_forallargs: HashMap::new(),
            current_args: None,
            tcx: tcx,
        }
    }

    fn register_typed_expression(&mut self, args: &syntax::ptr::P<[rustc::hir::Expr]>) {
        trace!("[register_typed_expression] enter");
        let mut args = args.clone().into_vec();
        assert!(args.len() == 2);
        let expression = args.pop().unwrap();
        let id = match args.pop().unwrap().node {
            hir::Expr_::ExprLit(lit) => match lit.into_inner().node {
                ast::LitKind::Int(id, _) => ExpressionId::from(id),
                _ => bug!(),
            },
            _ => bug!(),
        };
        debug!("id = {:?} expression = {:?}", id, expression);
        self.typed_expressions.insert(id, expression);
        trace!("[register_typed_expression] exit");
    }

    fn register_typed_args(&mut self, args: &syntax::ptr::P<[rustc::hir::Expr]>) {
        trace!("[register_typed_args] enter");
        let mut args = args.clone().into_vec();
        assert!(args.len() == 1);
        let id = match args.pop().unwrap().node {
            hir::Expr_::ExprLit(lit) => match lit.into_inner().node {
                ast::LitKind::Int(id, _) => ExpressionId::from(id),
                _ => bug!(),
            },
            _ => bug!(),
        };
        let vars = self.current_args.take().unwrap();
        self.typed_forallargs.insert(id, vars);
        trace!("[register_typed_args] exit");
    }
}

impl<'a, 'tcx: 'a, 'hir> intravisit::Visitor<'tcx> for TypeCollector<'a, 'tcx> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'tcx> {
        let map = &self.tcx.hir;
        intravisit::NestedVisitorMap::All(map)
    }

    fn visit_body(&mut self, body: &'tcx hir::Body) {
        self.current_args = Some(body.arguments.clone().into_vec());
        intravisit::walk_body(self, body)
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr) {
        if let hir::Expr_::ExprCall(ref target, ref args) = expr.node {
            if let hir::Expr_::ExprPath(hir::QPath::Resolved(_, ref path)) = target.node {
                if let hir::def::Def::Fn(def_id) = path.def {
                    let def_path = self.tcx.def_path(def_id).to_string_no_crate();
                    let crate_name = self.tcx.crate_name(def_id.krate);
                    if crate_name == "prusti_contracts"
                        && def_path == r#"::internal[0]::__assertion[0]"# {
                        self.register_typed_expression(args);
                    }
                    if crate_name == "prusti_contracts"
                        && def_path == r#"::internal[0]::__trigger[0]"# {
                        self.register_typed_expression(args);
                    }
                    if crate_name == "prusti_contracts" && def_path == r#"::internal[0]::__id[0]"# {
                        self.register_typed_args(args);
                    }
                };
            };
        };
        intravisit::walk_expr(self, expr);
    }
}
