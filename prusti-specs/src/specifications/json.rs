use super::untyped;
use serde::{Deserialize, Serialize};
use super::common;


#[derive(Serialize, Deserialize)]
pub struct Expression {
    /// Identifier of the specification to which this expression belongs.
    pub spec_id: untyped::SpecificationId,
    /// Identifier of the expression within the specification.
    pub expr_id: untyped::ExpressionId,
}

#[derive(Serialize, Deserialize)]
pub enum AssertionKind {
    Expr(Expression),
    And(Vec<Assertion>),
    Implies(Assertion, Assertion),
    ForAll(ForAllVars, Assertion, TriggerSet),
    SpecEnt(String, SpecEntVars, Assertion, Assertion),
}

#[derive(Serialize, Deserialize)]
pub struct Assertion {
    pub kind: Box<AssertionKind>,
}

#[derive(Serialize, Deserialize)]
pub struct ForAllVars {
    pub spec_id: untyped::SpecificationId,
    pub expr_id: untyped::ExpressionId,
    pub count: usize,
}

#[derive(Serialize, Deserialize)]
pub struct SpecEntVars {
    pub spec_id: untyped::SpecificationId,
    pub pre_expr_id: untyped::ExpressionId,
    pub post_expr_id: untyped::ExpressionId,
    pub arg_count: usize,
}

#[derive(Serialize, Deserialize)]
pub struct Trigger(pub Vec<Expression>);

#[derive(Serialize, Deserialize)]
pub struct TriggerSet(pub Vec<Trigger>);

trait ToStructure<T> {
    fn to_structure(&self) -> T;
}

impl ToStructure<Expression> for untyped::Expression {
    fn to_structure(&self) -> Expression {
        Expression {
            spec_id: self.spec_id.clone(),
            expr_id: self.id.clone(),
        }
    }
}

impl ToStructure<ForAllVars> for common::ForAllVars<untyped::ExpressionId, untyped::Arg> {
    fn to_structure(&self) -> ForAllVars {
        ForAllVars {
            spec_id: self.spec_id.clone(),
            count: self.vars.len(),
            expr_id: self.id.clone(),
        }
    }
}

impl ToStructure<SpecEntVars> for common::SpecEntVars<untyped::ExpressionId, untyped::Arg> {
    fn to_structure(&self) -> SpecEntVars {
        SpecEntVars {
            spec_id: self.spec_id.clone(),
            arg_count: self.args.len(),
            pre_expr_id: self.pre_id.clone(),
            post_expr_id: self.post_id.clone(),
        }
    }
}

impl ToStructure<TriggerSet> for untyped::TriggerSet {
    fn to_structure(&self) -> TriggerSet {
        TriggerSet(self.0.clone()
                         .into_iter()
                         .map(|x| x.to_structure())
                         .collect()
        )
    }
}

impl ToStructure<Trigger> for common::Trigger<common::ExpressionId, syn::Expr> {
    fn to_structure(&self) -> Trigger {
        Trigger(self.0
                    .clone()
                    .into_iter()
                    .map(|x| x.to_structure())
                    .collect()
        )
    }
}

impl ToStructure<AssertionKind> for untyped::AssertionKind {
    fn to_structure(&self) -> AssertionKind {
        use super::common::AssertionKind::*;
        match self {
            Expr(expr) => AssertionKind::Expr(expr.to_structure()),
            And(assertions) => {
                AssertionKind::And(
                    assertions.into_iter()
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
            SpecEnt(clname, args, pre, post) => AssertionKind::SpecEnt(
                clname.clone(),
                args.to_structure(),
                pre.to_structure(),
                post.to_structure(),
            ),
            x => {
                unimplemented!("{:?}", x);
            }
        }
    }
}

impl ToStructure<Assertion> for untyped::Assertion {
    fn to_structure(&self) -> Assertion {
        Assertion {
            kind: box self.kind.to_structure(),
        }
    }
}

pub fn to_json_string(assertion: &untyped::Assertion) -> String {
    serde_json::to_string(&assertion.to_structure()).unwrap()
}

impl Assertion {
    pub fn from_json_string(json: &str) -> Self {
        serde_json::from_str(&json).unwrap()
    }
}
