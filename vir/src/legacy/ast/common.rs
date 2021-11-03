// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    cmp::Ordering,
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
    mem::discriminant,
    ops,
};

pub trait WithIdentifier {
    fn get_identifier(&self) -> String;
}

/// The identifier of a statement. Used in error reporting.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Position {
    pub(crate) line: i32,
    pub(crate) column: i32,
    pub(crate) id: u64,
}

impl Position {
    pub fn new(line: i32, column: i32, id: u64) -> Self {
        Position { line, column, id }
    }
}

impl Default for Position {
    fn default() -> Self {
        Position::new(0, 0, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_position() {
        assert!(!Position::new(123, 234, 345).is_default());
        assert!(Position::default().is_default());
    }
}

pub enum PermAmountError {
    InvalidAdd(PermAmount, PermAmount),
    InvalidSub(PermAmount, PermAmount),
}

/// The permission amount.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PermAmount {
    Read,
    Write,
    /// The permission remaining after ``Read`` was subtracted from ``Write``.
    Remaining,
}

impl PermAmount {
    /// Can this permission amount be used in specifications?
    pub fn is_valid_for_specs(&self) -> bool {
        match self {
            PermAmount::Read | PermAmount::Write => true,
            PermAmount::Remaining => false,
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn add(self, other: PermAmount) -> Result<PermAmount, PermAmountError> {
        match (self, other) {
            (PermAmount::Read, PermAmount::Remaining)
            | (PermAmount::Remaining, PermAmount::Read) => Ok(PermAmount::Write),
            _ => Err(PermAmountError::InvalidAdd(self, other)),
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn sub(self, other: PermAmount) -> Result<PermAmount, PermAmountError> {
        match (self, other) {
            (PermAmount::Write, PermAmount::Read) => Ok(PermAmount::Remaining),
            (PermAmount::Write, PermAmount::Remaining) => Ok(PermAmount::Read),
            _ => Err(PermAmountError::InvalidSub(self, other)),
        }
    }
}

impl fmt::Display for PermAmount {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PermAmount::Read => write!(f, "read"),
            PermAmount::Write => write!(f, "write"),
            PermAmount::Remaining => write!(f, "write-read"),
        }
    }
}

impl PartialOrd for PermAmount {
    fn partial_cmp(&self, other: &PermAmount) -> Option<Ordering> {
        match (self, other) {
            (PermAmount::Read, PermAmount::Write) => Some(Ordering::Less),
            (PermAmount::Read, PermAmount::Read) | (PermAmount::Write, PermAmount::Write) => {
                Some(Ordering::Equal)
            }
            (PermAmount::Write, PermAmount::Read) => Some(Ordering::Greater),
            _ => None,
        }
    }
}

impl Ord for PermAmount {
    fn cmp(&self, other: &PermAmount) -> Ordering {
        self.partial_cmp(other)
            .unwrap_or_else(|| panic!("Undefined comparison between {:?} and {:?}", self, other))
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum Float {
    F32,
    F64,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum BitVector {
    BV8,
    BV16,
    BV32,
    BV64,
    BV128,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Type {
    Int,
    Bool,
    Float(Float),
    BitVector(BitVector),
    Seq(Box<Type>),
    //Ref, // At the moment we don't need this
    /// TypedRef: the first parameter is the name of the predicate that encodes the type
    TypedRef(String),
    Domain(String),
    Snapshot(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeId {
    Int,
    Bool,
    Float,
    BitVector,
    Ref,
    Seq,
    Domain,
    Snapshot,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::Float(Float::F32) => write!(f, "F32"),
            Type::Float(Float::F64) => write!(f, "F64"),
            Type::BitVector(BitVector::BV8) => write!(f, "BV8"),
            Type::BitVector(BitVector::BV16) => write!(f, "BV16"),
            Type::BitVector(BitVector::BV32) => write!(f, "BV32"),
            Type::BitVector(BitVector::BV64) => write!(f, "BV64"),
            Type::BitVector(BitVector::BV128) => write!(f, "BV128"),
            //Type::Ref => write!(f, "Ref"),
            Type::TypedRef(ref name) => write!(f, "Ref({})", name),
            Type::Domain(ref name) => write!(f, "Domain({})", name),
            Type::Snapshot(ref name) => write!(f, "Snapshot({})", name),
            Type::Seq(ref elem_ty) => write!(f, "Seq[{}]", elem_ty),
        }
    }
}

impl Type {
    pub fn is_ref(&self) -> bool {
        matches!(self, &Type::TypedRef(_))
    }

    pub fn is_domain(&self) -> bool {
        matches!(self, &Type::Domain(_))
    }

    pub fn is_snapshot(&self) -> bool {
        matches!(self, &Type::Snapshot(_))
    }

    pub fn name(&self) -> String {
        match self {
            Type::Bool => "bool".to_string(),
            Type::Int => "int".to_string(),
            Type::Float(Float::F32) => "f32".to_string(),
            Type::Float(Float::F64) => "f64".to_string(),
            Type::BitVector(BitVector::BV8) => "bv8".to_string(),
            Type::BitVector(BitVector::BV16) => "bv16".to_string(),
            Type::BitVector(BitVector::BV32) => "bv32".to_string(),
            Type::BitVector(BitVector::BV64) => "bv64".to_string(),
            Type::BitVector(BitVector::BV128) => "bv128".to_string(),
            Type::TypedRef(ref pred_name) => pred_name.to_string(),
            Type::Domain(ref pred_name) => pred_name.to_string(),
            Type::Snapshot(ref pred_name) => pred_name.to_string(),
            Type::Seq(_) => "Seq".to_string(),
        }
    }

    /// Construct a new VIR type that corresponds to an enum variant.
    pub fn variant(self, variant: &str) -> Self {
        match self {
            Type::TypedRef(mut name) => {
                name.push_str(variant);
                Type::TypedRef(name)
            }
            _ => unreachable!(),
        }
    }

    /// Replace all generic types with their instantiations by using string substitution.
    /// FIXME: this is a hack to support generics. See issue #187.
    pub fn patch(self, substs: &HashMap<String, String>) -> Self {
        match self {
            Type::TypedRef(mut predicate_name) => {
                for (typ, subst) in substs {
                    predicate_name = predicate_name.replace(typ, subst);
                }
                Type::TypedRef(predicate_name)
            }
            typ => typ,
        }
    }

    pub fn get_id(&self) -> TypeId {
        match self {
            Type::Bool => TypeId::Bool,
            Type::Int => TypeId::Int,
            Type::Float(_) => TypeId::Float,
            Type::BitVector(_) => TypeId::BitVector,
            Type::TypedRef(_) => TypeId::Ref,
            Type::Domain(_) => TypeId::Domain,
            Type::Snapshot(_) => TypeId::Snapshot,
            Type::Seq(_) => TypeId::Seq,
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        discriminant(self) == discriminant(other)
    }
}

impl Eq for Type {}

impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LocalVar {
    pub name: String,
    pub typ: Type,
}

impl fmt::Display for LocalVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Debug for LocalVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.typ)
    }
}

impl LocalVar {
    pub fn new<S: Into<String>>(name: S, typ: Type) -> Self {
        LocalVar {
            name: name.into(),
            typ,
        }
    }

    pub fn new_typed_ref<S: Into<String>>(name: S, ty_ref_name: String) -> Self {
        LocalVar::new(name, Type::TypedRef(ty_ref_name))
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Field {
    pub name: String,
    pub typ: Type,
}

impl fmt::Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Debug for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.typ)
    }
}

impl Field {
    pub fn new<S: Into<String>>(name: S, typ: Type) -> Self {
        Field {
            name: name.into(),
            typ,
        }
    }

    pub fn typed_ref_name(&self) -> Option<String> {
        match self.typ {
            Type::TypedRef(ref name) => Some(name.clone()),
            _ => None,
        }
    }
}

impl WithIdentifier for Field {
    fn get_identifier(&self) -> String {
        self.name.clone()
    }
}
