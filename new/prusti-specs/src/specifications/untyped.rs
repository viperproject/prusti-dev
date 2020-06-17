use super::common::{self, ExpressionIdGenerator};
use proc_macro2::TokenStream;
use quote::quote_spanned;
use std::collections::HashMap;
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;

pub use common::{ExpressionId, SpecType, SpecificationId, Arg};
pub use super::preparser::Parser;

/// A specification that has no types associated with it.
pub type Specification = common::Specification<ExpressionId, syn::Expr, Arg>;
/// A set of untyped specifications associated with a single element.
pub type SpecificationSet = common::SpecificationSet<ExpressionId, syn::Expr, Arg>;
/// A set of untyped specifications associated with a loop.
pub type LoopSpecification = common::LoopSpecification<ExpressionId, syn::Expr, Arg>;
/// A set of untyped specifications associated with a procedure.
pub type ProcedureSpecification = common::ProcedureSpecification<ExpressionId, syn::Expr, Arg>;
/// A map of untyped specifications for a specific crate.
pub type SpecificationMap = HashMap<common::SpecificationId, SpecificationSet>;
/// An assertion that has no types associated with it.
pub type Assertion = common::Assertion<ExpressionId, syn::Expr, Arg>;
/// An assertion kind that has no types associated with it.
pub type AssertionKind = common::AssertionKind<ExpressionId, syn::Expr, Arg>;
/// An expression that has no types associated with it.
pub type Expression = common::Expression<ExpressionId, syn::Expr>;
/// A trigger set that has not types associated with it.
pub type TriggerSet = common::TriggerSet<ExpressionId, syn::Expr>;

impl Assertion {
    pub(crate) fn parse(
        tokens: TokenStream,
        spec_id: SpecificationId,
        id_generator: &mut ExpressionIdGenerator,
    ) -> syn::Result<Self> {
        let mut parser = Parser::new(tokens);
        let assertion = parser.extract_assertion()?;
        println!("{:#?}", assertion);
        Ok(assertion.assign_id(spec_id, id_generator))
    }
}

impl Parse for common::Expression<(), syn::Expr> {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            spec_id: SpecificationId::dummy(),
            id: (),
            expr: input.parse()?,
        })
    }
}

impl Parse for common::Assertion<(), syn::Expr, Arg> {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // TODO: Implement parsing of the full spec. Some code can be taken from
        // here:
        // https://gitlab.inf.ethz.ch/OU-PMUELLER/prusti-dev/-/commits/new-parser/
        Ok(Self {
            kind: box common::AssertionKind::Expr(input.parse()?),
        })
    }
}

pub(crate) trait AssignExpressionId<Target> {
    fn assign_id(
        self,
        spec_id: SpecificationId,
        id_generator: &mut ExpressionIdGenerator,
    ) -> Target;
}

impl AssignExpressionId<Expression> for common::Expression<(), syn::Expr> {
    fn assign_id(
        self,
        spec_id: SpecificationId,
        id_generator: &mut ExpressionIdGenerator,
    ) -> Expression {
        Expression {
            spec_id: spec_id,
            id: id_generator.generate(),
            expr: self.expr,
        }
    }
}

impl AssignExpressionId<AssertionKind> for common::AssertionKind<(), syn::Expr, Arg> {
    fn assign_id(
        self,
        spec_id: SpecificationId,
        id_generator: &mut ExpressionIdGenerator,
    ) -> AssertionKind {
        use common::AssertionKind::*;
        match self {
            Expr(expr) => Expr(expr.assign_id(spec_id, id_generator)),
            And(assertions) => And(
                assertions.into_iter()
                          .map(|assertion|
                              Assertion { kind: assertion.kind.assign_id(spec_id, id_generator) })
                          .collect()),
            Implies(lhs, rhs) => Implies(
                lhs.assign_id(spec_id, id_generator),
                rhs.assign_id(spec_id, id_generator)
            ),

            x => unimplemented!("{:?}", x),
        }
    }
}

impl AssignExpressionId<Box<AssertionKind>> for Box<common::AssertionKind<(), syn::Expr, Arg>> {
    fn assign_id(
        self,
        spec_id: SpecificationId,
        id_generator: &mut ExpressionIdGenerator,
    ) -> Box<AssertionKind> {
        box (*self).assign_id(spec_id, id_generator)
    }
}

impl AssignExpressionId<Assertion> for common::Assertion<(), syn::Expr, Arg> {
    fn assign_id(
        self,
        spec_id: SpecificationId,
        id_generator: &mut ExpressionIdGenerator,
    ) -> Assertion {
        Assertion {
            kind: self.kind.assign_id(spec_id, id_generator),
        }
    }
}

/// A trait for encoding the statements for type-checking the spec.
pub trait EncodeTypeCheck {
    fn encode_type_check(&self, tokens: &mut TokenStream);
}

impl EncodeTypeCheck for Vec<Specification> {
    fn encode_type_check(&self, tokens: &mut TokenStream) {
        for spec in self {
            spec.encode_type_check(tokens);
        }
    }
}

impl EncodeTypeCheck for Specification {
    fn encode_type_check(&self, tokens: &mut TokenStream) {
        self.assertion.encode_type_check(tokens);
    }
}

impl EncodeTypeCheck for Assertion {
    fn encode_type_check(&self, tokens: &mut TokenStream) {
        match &*self.kind {
            AssertionKind::Expr(expression) => {
                expression.encode_type_check(tokens);
            }
            AssertionKind::And(assertions) => {
                for assertion in assertions {
                    assertion.encode_type_check(tokens);
                }
            }
            AssertionKind::Implies(lhs, rhs) => {
                lhs.encode_type_check(tokens);
                rhs.encode_type_check(tokens);
            }
            x => {
                unimplemented!("{:?}", x);
            }
        }
    }
}

impl EncodeTypeCheck for Expression {
    fn encode_type_check(&self, tokens: &mut TokenStream) {
        let span = self.expr.span();
        let expr = &self.expr;
        let identifier = format!("{}_{}", self.spec_id, self.id);
        let typeck_call = quote_spanned! { span =>
            #[doc = #identifier]
            || -> bool {
                #expr
            };
        };
        tokens.extend(typeck_call);
    }
}
