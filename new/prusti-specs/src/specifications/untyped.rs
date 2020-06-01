use super::common;
use std::collections::HashMap;

pub struct Arg {
    name: syn::Ident,
    typ: syn::Type,
}

/// A specification that has no types associated with it.
pub type Specification = common::Specification<syn::Expr, Arg>;
/// A set of untyped specifications associated with a single element.
pub type SpecificationSet = common::SpecificationSet<syn::Expr, Arg>;
/// A map of untyped specifications for a specific crate.
pub type SpecificationMap = HashMap<common::SpecID, SpecificationSet>;
/// An assertion that has no types associated with it.
pub type Assertion = common::Assertion<syn::Expr, Arg>;
/// An assertion kind that has no types associated with it.
pub type AssertionKind = common::AssertionKind<syn::Expr, Arg>;
/// An expression that has no types associated with it.
pub type Expression = common::Expression<syn::Expr>;
/// A trigger set that has not types associated with it.
pub type TriggerSet = common::TriggerSet<syn::Expr>;
