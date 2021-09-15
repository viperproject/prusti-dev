use super::untyped;
use serde::{Deserialize, Serialize};
use super::common;

#[derive(Serialize, Deserialize)]
pub struct Assertion {
    pub kind: Box<AssertionKind>,
}

#[derive(Serialize, Deserialize)]
pub enum AssertionKind {
    Expr(Expression),
    And(Vec<Assertion>),
    Implies(Assertion, Assertion),
    ForAll(QuantifierVars, Assertion, TriggerSet),
    Exists(QuantifierVars, Assertion, TriggerSet),
    SpecEntailment {
        closure: Expression,
        arg_binders: SpecEntailmentVars,
        pres: Vec<Assertion>,
        posts: Vec<Assertion>,
    },
}

#[derive(Serialize, Deserialize)]
pub struct Expression {
    /// Identifier of the specification to which this expression belongs.
    pub spec_id: untyped::SpecificationId,
    /// Identifier of the expression within the specification.
    pub expr_id: untyped::ExpressionId,
}

#[derive(Serialize, Deserialize)]
pub struct QuantifierVars {
    pub spec_id: untyped::SpecificationId,
    pub expr_id: untyped::ExpressionId,
    pub count: usize,
}

#[derive(Serialize, Deserialize)]
pub struct SpecEntailmentVars {
    pub spec_id: untyped::SpecificationId,
    pub pre_expr_id: untyped::ExpressionId,
    pub post_expr_id: untyped::ExpressionId,
    pub arg_count: usize,
}

#[derive(Serialize, Deserialize)]
pub struct TriggerSet(pub Vec<Trigger>);

#[derive(Serialize, Deserialize)]
pub struct Trigger(pub Vec<Expression>);

impl untyped::Expression {
    fn to_structure(&self) -> Expression {
        Expression {
            spec_id: self.spec_id,
            expr_id: self.id,
        }
    }
}

impl common::QuantifierVars<untyped::ExpressionId, untyped::Arg> {
    fn to_structure(&self) -> QuantifierVars {
        QuantifierVars {
            spec_id: self.spec_id,
            count: self.vars.len(),
            expr_id: self.id,
        }
    }
}

impl common::SpecEntailmentVars<untyped::ExpressionId, untyped::Arg> {
    fn to_structure(&self) -> SpecEntailmentVars {
        SpecEntailmentVars {
            spec_id: self.spec_id,
            arg_count: self.args.len(),
            pre_expr_id: self.pre_id,
            post_expr_id: self.post_id,
        }
    }
}

impl untyped::TriggerSet {
    fn to_structure(&self) -> TriggerSet {
        TriggerSet(self.0.clone()
                         .into_iter()
                         .map(|x| x.to_structure())
                         .collect()
        )
    }
}

impl common::Trigger<common::ExpressionId, syn::Expr> {
    fn to_structure(&self) -> Trigger {
        Trigger(self.0
                    .clone()
                    .into_iter()
                    .map(|x| x.to_structure())
                    .collect()
        )
    }
}

impl untyped::AssertionKind {
    fn to_structure(&self) -> AssertionKind {
        use super::common::AssertionKind::*;
        match self {
            Expr(expr) => AssertionKind::Expr(expr.to_structure()),
            And(assertions) => {
                AssertionKind::And(
                    assertions.iter()
                              .map(|assertion| Assertion { kind: Box::new(assertion.kind.to_structure()) })
                              .collect()
                )
            }
            Implies(lhs, rhs) => AssertionKind::Implies(
                lhs.to_structure(),
                rhs.to_structure()
            ),
            ForAll(vars, triggers, body) => AssertionKind::ForAll(
                vars.to_structure(),
                body.to_structure(),
                triggers.to_structure(),
            ),
            Exists(vars, triggers, body) => AssertionKind::Exists(
                vars.to_structure(),
                body.to_structure(),
                triggers.to_structure(),
            ),
            SpecEntailment {closure, arg_binders, pres, posts} => AssertionKind::SpecEntailment {
                closure: closure.to_structure(),
                arg_binders: arg_binders.to_structure(),
                pres: pres.iter().map(|pre| pre.to_structure()).collect(),
                posts: posts.iter().map(|post| post.to_structure()).collect(),
            },
            x => {
                unimplemented!("{:?}", x);
            }
        }
    }
}

impl untyped::Assertion {
    fn to_structure(&self) -> Assertion {
        Assertion {
            kind: Box::new(self.kind.to_structure()),
        }
    }
}

pub fn to_json_string(assertion: &untyped::Assertion) -> String {
    serde_json::to_string(&assertion.to_structure()).unwrap()
}

impl Assertion {
    pub fn from_json_string(json: &str) -> Self {
        serde_json::from_str(json).unwrap()
    }
}
