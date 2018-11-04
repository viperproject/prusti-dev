// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Data structures for storing information about specifications.
//!
//! Please see the `parser.rs` file for more information about
//! specifications.

use rustc;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::string::ToString;
use syntax::{ast, ptr};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// A specification type.
pub enum SpecType {
    /// Precondition of a procedure.
    Precondition,
    /// Postcondition of a procedure.
    Postcondition,
    /// Loop invariant.
    Invariant,
}

#[derive(Debug)]
/// A conversion from string into specification type error.
pub enum TryFromStringError {
    /// Reported when the string being converted is not one of the
    /// following: `requires`, `ensures`, `invariant`.
    UnknownSpecificationType,
}

impl<'a> TryFrom<&'a str> for SpecType {
    type Error = TryFromStringError;

    fn try_from(typ: &str) -> Result<SpecType, TryFromStringError> {
        match typ {
            "requires" => Ok(SpecType::Precondition),
            "ensures" => Ok(SpecType::Postcondition),
            "invariant" => Ok(SpecType::Invariant),
            _ => Err(TryFromStringError::UnknownSpecificationType),
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq, Hash, Clone, Copy)]
/// A unique ID of the specification element such as entire precondition
/// or postcondition.
pub struct SpecID(u64);

impl SpecID {
    /// Constructor.
    pub fn new() -> Self {
        Self { 0: 100 }
    }
    /// Increment ID and return a copy of the new value.
    pub fn inc(&mut self) -> Self {
        self.0 += 1;
        Self { 0: self.0 }
    }
}

impl ToString for SpecID {
    fn to_string(&self) -> String {
        self.0.to_string()
    }
}

impl From<u64> for SpecID {
    fn from(value: u64) -> Self {
        Self { 0: value }
    }
}

#[derive(Debug, Default, PartialEq, Eq, Hash, Clone, Copy)]
/// A unique ID of the Rust expression used in the specification.
pub struct ExpressionId(usize);

impl ExpressionId {
    /// Constructor.
    pub fn new() -> Self {
        Self { 0: 100 }
    }
    /// Increment ID and return a copy of the new value.
    pub fn inc(&mut self) -> Self {
        self.0 += 1;
        Self { 0: self.0 }
    }
}

impl ToString for ExpressionId {
    fn to_string(&self) -> String {
        self.0.to_string()
    }
}

impl Into<usize> for ExpressionId {
    fn into(self) -> usize {
        self.0
    }
}

impl Into<u128> for ExpressionId {
    fn into(self) -> u128 {
        self.0 as u128
    }
}

impl From<u128> for ExpressionId {
    fn from(value: u128) -> Self {
        Self { 0: value as usize }
    }
}

#[derive(Debug, Clone)]
/// A Rust expression used in the specification.
pub struct Expression<ET> {
    /// Unique identifier.
    pub id: ExpressionId,
    /// Actual expression.
    pub expr: ET,
}

#[derive(Debug, Clone)]
/// An assertion used in the specification.
pub struct Assertion<ET, AT> {
    /// Subassertions.
    pub kind: Box<AssertionKind<ET, AT>>,
}

#[derive(Debug, Clone)]
/// A single trigger for a quantifier.
pub struct Trigger<ET>(Vec<Expression<ET>>);

impl<ET> Trigger<ET> {
    /// Construct a new trigger, which is a “conjunction” of terms.
    pub fn new(terms: Vec<Expression<ET>>) -> Trigger<ET> {
        Trigger(terms)
    }
    /// Getter for terms.
    pub fn terms(&self) -> &Vec<Expression<ET>> {
        &self.0
    }
}

impl<ET> IntoIterator for Trigger<ET> {
    type Item = Expression<ET>;
    type IntoIter = ::std::vec::IntoIter<Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[derive(Debug, Clone)]
/// A set of triggers used in the quantifier.
pub struct TriggerSet<ET>(Vec<Trigger<ET>>);

impl<ET> TriggerSet<ET> {
    /// Construct a new trigger set.
    pub fn new(triggers: Vec<Trigger<ET>>) -> TriggerSet<ET> {
        TriggerSet(triggers)
    }
    /// Getter for triggers.
    pub fn triggers(&self) -> &Vec<Trigger<ET>> {
        &self.0
    }
}

impl<ET> IntoIterator for TriggerSet<ET> {
    type Item = Trigger<ET>;
    type IntoIter = ::std::vec::IntoIter<Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[derive(Debug, Clone)]
/// A sequence of variables used in the forall.
pub struct ForAllVars<AT> {
    /// Unique id for this sequence of variables.
    pub id: ExpressionId,
    /// Variables.
    pub vars: Vec<AT>,
}

#[derive(Debug, Clone)]
/// An assertion kind used in the specification.
pub enum AssertionKind<ET, AT> {
    /// A single Rust expression.
    Expr(Expression<ET>),
    /// Conjunction &&.
    And(Vec<Assertion<ET, AT>>),
    /// Implication ==>
    Implies(Expression<ET>, Assertion<ET, AT>),
    /// Quantifier (forall vars :: {triggers} filter ==> body)
    ForAll(
        ForAllVars<AT>,
        TriggerSet<ET>,
        Assertion<ET, AT>,
    ),
    /// Pledge after_expiry<reference>(body)
    Pledge(
        /// The blocking reference used in a loop. None for postconditions.
        Option<Expression<ET>>,
        /// The body.
        Assertion<ET, AT>,
    ),
}

#[derive(Debug, Clone)]
/// Specification such as precondition, postcondition, or invariant.
pub struct Specification<ET, AT> {
    /// Specification type.
    pub typ: SpecType,
    /// Actual specification.
    pub assertion: Assertion<ET, AT>,
}

#[derive(Debug, Clone)]
/// Specification of a single element such as procedure or loop.
pub enum SpecificationSet<ET, AT> {
    /// (Precondition, Postcondition)
    Procedure(Vec<Specification<ET, AT>>, Vec<Specification<ET, AT>>),
    /// Loop invariant.
    Loop(Vec<Specification<ET, AT>>),
}

impl<ET, AT> SpecificationSet<ET, AT> {
    pub fn is_empty(&self) -> bool {
        match self {
            SpecificationSet::Procedure(ref pres, ref posts) => pres.is_empty() && posts.is_empty(),
            SpecificationSet::Loop(ref invs) => invs.is_empty(),
        }
    }
}

/// A specification that has no types associated with it.
pub type UntypedSpecification = Specification<ptr::P<ast::Expr>, ast::Arg>;
/// A set of untyped specifications associated with a single element.
pub type UntypedSpecificationSet = SpecificationSet<ptr::P<ast::Expr>, ast::Arg>;
/// A map of untyped specifications for a specific crate.
pub type UntypedSpecificationMap = HashMap<SpecID, UntypedSpecificationSet>;
/// An assertion that has no types associated with it.
pub type UntypedAssertion = Assertion<ptr::P<ast::Expr>, ast::Arg>;
/// An assertion kind that has no types associated with it.
pub type UntypedAssertionKind = AssertionKind<ptr::P<ast::Expr>, ast::Arg>;
/// An expression that has no types associated with it.
pub type UntypedExpression = Expression<ptr::P<ast::Expr>>;
/// A trigger set that has not types associated with it.
pub type UntypedTriggerSet = TriggerSet<ptr::P<ast::Expr>>;

/// A specification that types associated with it.
pub type TypedSpecification = Specification<rustc::hir::Expr, rustc::hir::Arg>;
/// A set of typed specifications associated with a single element.
pub type TypedSpecificationSet = SpecificationSet<rustc::hir::Expr, rustc::hir::Arg>;
/// A map of typed specifications for a specific crate.
pub type TypedSpecificationMap = HashMap<SpecID, TypedSpecificationSet>;
/// An assertion that has types associated with it.
pub type TypedAssertion = Assertion<rustc::hir::Expr, rustc::hir::Arg>;
/// An assertion kind that has types associated with it.
pub type TypedAssertionKind = AssertionKind<rustc::hir::Expr, rustc::hir::Arg>;
/// An expression that has types associated with it.
pub type TypedExpression = Expression<rustc::hir::Expr>;
/// A trigger set that has types associated with it.
pub type TypedTriggerSet = TriggerSet<rustc::hir::Expr>;

pub type TypedTrigger = Trigger<rustc::hir::Expr>;
