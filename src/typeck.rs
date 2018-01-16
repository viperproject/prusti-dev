//! A module for extracting type information for specifications.


use rustc;
use rustc::hir::{self, intravisit};
use rustc::ty::TyCtxt;
use rustc_driver::driver;
use syntax::{self, ast};
use std::collections::HashMap;
use specifications::{
    ExpressionId, UntypedSpecificationMap, UntypedSpecification,
    TypedSpecification, TypedSpecificationMap, SpecificationSet,
    UntypedAssertion, TypedAssertion, Specification, AssertionKind,
    Assertion, Expression,
};


/// Convert untyped specifications to typed specifications.
pub fn type_specifications(state: &mut driver::CompileState,
                           untyped_specifications: UntypedSpecificationMap
                           ) -> TypedSpecificationMap {
    trace!("[type_specifications] enter");
    let tcx = state.tcx.unwrap();
    let mut collector = TypeCollector::new(tcx);
    intravisit::walk_crate(&mut collector, tcx.hir.krate());
    let typed_specifications = convert_to_typed(
        untyped_specifications, &collector.typed_expressions);
    trace!("[type_specifications] exit");
    typed_specifications
}


fn type_assertion(assertion: UntypedAssertion,
                  typed_expressions: &HashMap<ExpressionId, rustc::hir::Expr>
                  ) -> TypedAssertion {
    Assertion {
        kind: box {
            match *assertion.kind {
                AssertionKind::Expr(expr) => {
                    AssertionKind::Expr(
                        Expression {
                            id: expr.id,
                            expr: typed_expressions[&expr.id].clone(),
                        }
                    )
                },
                AssertionKind::And(assertions) => {
                    AssertionKind::And(
                        assertions
                            .into_iter()
                            .map(|assertion|
                                 type_assertion(assertion, typed_expressions))
                            .collect()
                    )
                },
                _ => {
                    unimplemented!()
                },
            }
        }
    }
}


fn type_specification(specification: UntypedSpecification,
                      typed_expressions: &HashMap<ExpressionId, rustc::hir::Expr>
                      ) -> TypedSpecification {
    Specification {
        typ: specification.typ,
        assertion: type_assertion(specification.assertion, typed_expressions),
    }
}


fn convert_to_typed(untyped_specifications: UntypedSpecificationMap,
                    typed_expressions: &HashMap<ExpressionId, rustc::hir::Expr>
                    ) -> TypedSpecificationMap {
    let convert = |specs: Vec<UntypedSpecification>| {
        specs
            .into_iter()
            .map(|spec| type_specification(spec, typed_expressions))
            .collect()
    };
    untyped_specifications.into_iter().map(
        |(id, untyped_specification)| {
            match untyped_specification {
                SpecificationSet::Procedure(precondition, postcondition) => {
                    (id, SpecificationSet::Procedure(
                            convert(precondition),
                            convert(postcondition)))
                },
                SpecificationSet::Loop(invariants) => {
                    (id, SpecificationSet::Loop(convert(invariants)))
                },
            }
        }
    ).collect()
}


/// Visitor that collects typed expressions used in specifications.
struct TypeCollector<'a, 'tcx: 'a> {
    pub typed_expressions: HashMap<ExpressionId, rustc::hir::Expr>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
}


impl <'a, 'tcx: 'a> TypeCollector<'a, 'tcx> {

    fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        Self {
            typed_expressions: HashMap::new(),
            tcx: tcx,
        }
    }

    fn register_typed_expression(&mut self,
                                args: &syntax::ptr::P<[rustc::hir::Expr]>) {
        trace!("[register_typed_expression] enter");
        let mut args = args.clone().into_vec();
        assert!(args.len() == 2);
        let expression = args.pop().unwrap();
        let id = match args.pop().unwrap().node {
            hir::Expr_::ExprLit(lit) => {
                match lit.into_inner().node {
                    ast::LitKind::Int(id, _) => {
                        ExpressionId::from(id)
                    },
                    _ => {bug!()},
                }
            },
            _ => {bug!()},
        };
        debug!("id = {:?} expression = {:?}", id, expression);
        self.typed_expressions.insert(id, expression);
        trace!("[register_typed_expression] exit");
    }

}

impl <'a, 'tcx: 'a, 'hir> intravisit::Visitor<'tcx>
        for TypeCollector<'a, 'tcx> {

    fn nested_visit_map<'this>(&'this mut self) ->
            intravisit::NestedVisitorMap<'this, 'tcx> {
        let map = &self.tcx.hir;
        intravisit::NestedVisitorMap::All(map)
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr) {
        match expr.node {
            hir::Expr_::ExprCall(ref target, ref args) => {
                match target.node {
                    hir::Expr_::ExprPath(
                        hir::QPath::Resolved(_, ref path)) => {
                        match path.def {
                            hir::def::Def::Fn(def_id) => {
                                let def_path = self.tcx
                                    .def_path(def_id)
                                    .to_string_no_crate();
                                let crate_name = self.tcx.crate_name(
                                    def_id.krate);
                                if crate_name == "prusti_contracts" &&
                                    def_path == r#"::internal[0]::__assertion[0]"# {
                                    self.register_typed_expression(args);
                                }
                            },
                            _ => {},
                        };
                    },
                    _ => {},
                }
            },
            _ => {},
        }
        intravisit::walk_expr(self, expr);
    }

}
