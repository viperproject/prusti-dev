//! Data structures for storing information about specifications.
//!
//! Currently, we support preconditions, postconditions, and loop
//! invariants that can be specified by using the attribute syntax as
//! follows:
//!
//! ```rust
//! #[requires="0 < n && n < 10"]
//! #[ensures="result > 0"]
//! fn fib(mut n: i32) -> i32 {
//!     let mut i = 1;
//!     let mut j = 1;
//!     #[invariant="i > 0 && j > 0"]
//!     while n > 2 {
//!         let tmp = i + j;
//!         j = i;
//!         i = tmp;
//!         n -= 1;
//!     }
//!     i
//! }
//! ```

use std::convert::TryFrom;
use std::string::ToString;
use syntax::{ast, ptr};
use syntax::codemap::Span;


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// A specification type.
pub enum SpecType {
    Precondition,
    Postcondition,
    Invariant,
}

#[derive(Debug)]
pub enum TryFromStringError {
    UnknownSpecificationType,
}

impl<'a> TryFrom<&'a str> for SpecType {

    type Error = TryFromStringError;

    fn try_from(typ: &str) -> Result<SpecType, TryFromStringError> {
        match typ {
            "requires" => {Ok(SpecType::Precondition)},
            "ensures" => {Ok(SpecType::Postcondition)},
            "invariant" => {Ok(SpecType::Invariant)},
            _ => {Err(TryFromStringError::UnknownSpecificationType)},
        }
    }
}


#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
/// A unique specification ID.
pub struct SpecID(u64);

impl SpecID {
    pub fn new() -> SpecID {
        SpecID(100)
    }
    pub fn inc(&mut self) -> SpecID {
        self.0 += 1;
        SpecID(self.0)
    }
    pub fn to_number(&self) -> u64 {
        self.0
    }
}

impl ToString for SpecID {
    fn to_string(&self) -> String {
        self.0.to_string()
    }
}


#[derive(Debug, Clone)]
/// A specification AST extracted from the attribute.
pub struct RawSpec {
    pub spec_type: SpecType,
    pub expr: ptr::P<ast::Expr>,
    pub span: Span,
}
