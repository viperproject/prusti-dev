// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::discriminant;
use std::ops;

pub trait WithIdentifier {
    fn get_identifier(&self) -> String;
}

/// The identifier of a statement. Used in error reporting.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Position {
    line: i32,
    column: i32,
    id: String,
}

impl Position {
    pub fn new(line: i32, column: i32, id: String) -> Self {
        Position { line, column, id }
    }

    pub fn line(&self) -> i32 {
        self.line
    }

    pub fn column(&self) -> i32 {
        self.column
    }

    pub fn id(&self) -> String {
        self.id.to_string()
    }

    pub fn is_default(&self) -> bool {
        self.line == 0 && self.column == 0 && self.id == "no-position"
    }
}

impl Default for Position {
    fn default() -> Self {
        Position::new(0, 0, "no-position".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_position() {
        assert!(!Position::new(123, 234, "123123123".to_string()).is_default());
        assert!(Position::default().is_default());
    }
}

/// The permission amount.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

impl ops::Add for PermAmount {
    type Output = PermAmount;

    fn add(self, other: PermAmount) -> PermAmount {
        match (self, other) {
            (PermAmount::Read, PermAmount::Remaining)
            | (PermAmount::Remaining, PermAmount::Read) => PermAmount::Write,
            _ => unreachable!("Invalid addition: {} + {}", self, other),
        }
    }
}

impl ops::Sub for PermAmount {
    type Output = PermAmount;

    fn sub(self, other: PermAmount) -> PermAmount {
        match (self, other) {
            (PermAmount::Write, PermAmount::Read) => PermAmount::Remaining,
            (PermAmount::Write, PermAmount::Remaining) => PermAmount::Read,
            _ => unreachable!("Invalid subtraction: {} - {}", self, other),
        }
    }
}

impl Ord for PermAmount {
    fn cmp(&self, other: &PermAmount) -> Ordering {
        match (self, other) {
            (PermAmount::Read, PermAmount::Write) => Ordering::Less,
            (PermAmount::Read, PermAmount::Read) | (PermAmount::Write, PermAmount::Write) => {
                Ordering::Equal
            }
            (PermAmount::Write, PermAmount::Read) => Ordering::Greater,
            _ => unreachable!("self={} other={}", self, other),
        }
    }
}

impl PartialOrd for PermAmount {
    fn partial_cmp(&self, other: &PermAmount) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Clone)]
pub enum Type {
    Int,
    Bool,
    //Ref, // At the moment we don't need this
    /// TypedRef: the first parameter is the name of the predicate that encodes the type
    TypedRef(String),
    Domain(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeId {
    Int,
    Bool,
    Ref,
    Domain,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Type::Int => write!(f, "Int"),
            &Type::Bool => write!(f, "Bool"),
            //&Type::Ref => write!(f, "Ref"),
            &Type::TypedRef(ref name) => write!(f, "Ref({})", name),
            &Type::Domain(ref name) => write!(f, "Domain({})", name),
        }
    }
}

impl Type {
    pub fn is_ref(&self) -> bool {
        match self {
            //&Type::Ref |
            &Type::TypedRef(_) => true,
            _ => false,
        }
    }

    pub fn name(&self) -> String {
        match self {
            &Type::Bool => "bool".to_string(),
            &Type::Int => "int".to_string(),
            &Type::TypedRef(ref pred_name) => format!("{}", pred_name),
            &Type::Domain(ref pred_name) => format!("{}", pred_name),
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

    /// FIXME: A hack. Replaces all generic types with their instantiations by using string
    /// substitution.
    pub fn patch(self, substs: &HashMap<String, String>) -> Self {
        match self {
            Type::TypedRef(mut predicate_name) => {
                for (typ, subst) in substs {
                    predicate_name = predicate_name.replace(typ, subst);
                }
                Type::TypedRef(predicate_name)
            },
            typ => typ,
        }
    }

    pub fn get_id(&self) -> TypeId {
        match self {
            Type::Bool => TypeId::Bool,
            Type::Int => TypeId::Int,
            Type::TypedRef(_) => TypeId::Ref,
            Type::Domain(_) => TypeId::Domain,
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

#[derive(Clone, PartialEq, Eq, Hash)]
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
}

#[derive(Clone)]
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

impl PartialEq for Field {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.typ == other.typ
    }
}

impl Eq for Field {}

impl Hash for Field {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.typ.hash(state);
    }
}

impl WithIdentifier for Field {
    fn get_identifier(&self) -> String {
        self.name.clone()
    }
}
