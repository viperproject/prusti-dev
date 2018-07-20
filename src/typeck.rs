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
use syntax::ast;
use std::collections::HashMap;
use prusti_interface::specifications::{Assertion, AssertionKind, Expression, ExpressionId, ForAllVars,
                     Specification, SpecificationSet, Trigger, TypedAssertion, TypedSpecification,
                     TypedSpecificationMap, TypedTriggerSet, UntypedAssertion,
                     UntypedSpecification, UntypedSpecificationMap, UntypedTriggerSet};
use syntax_pos::Span;

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
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
}

impl<'a, 'tcx: 'a> TypeCollector<'a, 'tcx> {
    fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        Self {
            typed_expressions: HashMap::new(),
            typed_forallargs: HashMap::new(),
            tcx: tcx,
        }
    }

    fn register_typed_expression(&mut self, expr_id: u128, expr: rustc::hir::Expr) {
        trace!("[register_typed_expression] enter");
        let id = ExpressionId::from(expr_id);
        debug!("id = {:?} expression = {:?}", id, expr);
        self.typed_expressions.insert(id, expr);
        trace!("[register_typed_expression] exit");
    }

    fn register_typed_forallargs(&mut self, forall_id: u128, args: Vec<rustc::hir::Arg>) {
        trace!("[register_typed_forallargs] enter");
        let id = ExpressionId::from(forall_id);
        self.typed_forallargs.insert(id, args);
        trace!("[register_typed_forallargs] exit");
    }
}

fn get_attr_value(attr: &ast::Attribute) -> String {
    use syntax::tokenstream::TokenTree;
    use syntax::parse::token;

    let trees: Vec<_> = attr.tokens.trees().collect();
    assert_eq!(trees.len(), 2);

    match trees[0] {
        TokenTree::Token(_, ref token) => assert_eq!(*token, token::Token::Eq),
        _ => unreachable!()
    };

    match trees[1] {
        TokenTree::Token(_, ref token) => match *token {
            token::Token::Literal(ref lit, None) => match *lit {
                token::Lit::Str_(ref name) |
                token::Lit::StrRaw(ref name, _) => {
                    name.as_str().to_string()
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }
}

impl<'a, 'tcx: 'a, 'hir> intravisit::Visitor<'tcx> for TypeCollector<'a, 'tcx> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'tcx> {
        let map = &self.tcx.hir;
        intravisit::NestedVisitorMap::All(map)
    }

    fn visit_fn(&mut self, fk: intravisit::FnKind<'tcx>, fd: &'tcx hir::FnDecl, bi: hir::BodyId, s: Span, id: ast::NodeId) {
        let opt_body = self.nested_visit_map().intra().map(|map| map.body(bi));
        if let Some(body) = opt_body {
            let args = &body.arguments;
            let expr = &body.value;

            for attr in fk.attrs().iter() {
                if attr.path.to_string() == "__PRUSTI_SPEC_EXPR_ID" {
                    let expr_id: u128 = get_attr_value(attr).parse().unwrap();
                    self.register_typed_expression(expr_id, expr.clone());
                }
                if attr.path.to_string() == "__PRUSTI_SPEC_FORALL_VARS_ID" {
                    let forall_id: u128 = get_attr_value(attr).parse().unwrap();
                    self.register_typed_forallargs(forall_id, args.clone().into_vec());
                }
            }
        }

        intravisit::walk_fn(self, fk, fd, bi, s, id)
    }
}
