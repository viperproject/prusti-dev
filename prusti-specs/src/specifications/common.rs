//! Data structures for storing information about specifications.
//!
//! Please see the `parser.rs` file for more information about
//! specifications.

use serde::{Deserialize, Serialize};
use std::convert::TryFrom;
use std::fmt::{Display, Debug};
use uuid::Uuid;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// A specification type.
pub enum SpecType {
    /// Precondition of a procedure.
    Precondition,
    /// Postcondition of a procedure.
    Postcondition,
    /// Loop invariant or struct invariant
    Invariant,
    /// Predicate
    Predicate,
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
            "predicate" => Ok(SpecType::Predicate),
            _ => Err(TryFromStringError::UnknownSpecificationType),
        }
    }
}

#[derive(
    Debug, Default, PartialEq, Eq, Hash, Clone, Copy, Serialize, Deserialize, PartialOrd, Ord,
)]
/// A unique ID of the specification element such as entire precondition
/// or postcondition.
pub struct SpecificationId(Uuid);

/// A reference to a procedure specification.
#[derive(Debug, Clone, Copy)]
pub enum SpecIdRef {
    Precondition(SpecificationId),
    Postcondition(SpecificationId),
    Pledge {
        lhs: Option<SpecificationId>,
        rhs: SpecificationId,
    },
    Predicate(SpecificationId),
}

impl Display for SpecificationId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0.to_simple().encode_lower(&mut Uuid::encode_buffer()),
        )
    }
}

impl std::convert::TryFrom<String> for SpecificationId {
    type Error = uuid::Error;
    fn try_from(value: String) -> Result<Self, Self::Error> {
        Uuid::parse_str(&value).map(Self)
    }
}

impl SpecificationId {
    pub fn dummy() -> Self {
        Self(Uuid::nil())
    }
}

pub(crate) struct SpecificationIdGenerator {}

impl SpecificationIdGenerator {
    pub(crate) fn new() -> Self {
        Self {}
    }
    pub(crate) fn generate(&mut self) -> SpecificationId {
        SpecificationId(Uuid::new_v4())
    }
}

pub(crate) struct NameGenerator {}

impl NameGenerator {
    pub(crate) fn new() -> Self { Self { } }
    pub(crate) fn generate_struct_name(&self, item: &syn::ItemImpl) -> Result<String, String> {
        let mut path_str: String = String::new();

        match &*item.self_ty {
            syn::Type::Path (ty_path) => {
                for seg in ty_path.path.segments.iter() {
                    path_str.push_str(&seg.ident.to_string());
                }
            }
            _ => {
                return Err("expected a path".to_string());
            }
        };
        let uuid = Uuid::new_v4().to_simple();

        Ok(format!("PrustiStruct{}_{}", path_str, uuid))
    }

    pub(crate) fn generate_mod_name(&self, ident: &syn::Ident) -> String {
        let uuid = Uuid::new_v4().to_simple();
        format!("{}_{}", ident, uuid)
    }
}
