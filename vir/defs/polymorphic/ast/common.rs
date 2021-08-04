// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::polymorphic::ast::*;
use std::{
    cmp::Ordering,
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
    mem::discriminant,
};

/// The identifier of a statement. Used in error reporting.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Position {
    line: i32,
    column: i32,
    id: u64,
}

impl Position {
    pub fn new(line: i32, column: i32, id: u64) -> Self {
        Position { line, column, id }
    }

    pub fn line(&self) -> i32 {
        self.line
    }

    pub fn column(&self) -> i32 {
        self.column
    }

    pub fn id(&self) -> u64 {
        self.id
    }
}

pub enum PermAmountError {
    InvalidAdd(PermAmount, PermAmount),
    InvalidSub(PermAmount, PermAmount)
}

/// The permission amount.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PermAmount {
    Read,
    Write,
    /// The permission remaining after ``Read`` was subtracted from ``Write``.
    Remaining,
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
        self.partial_cmp(other).expect(&format!(
            "Undefined comparison between {:?} and {:?}",
            self, other
        ))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Type {
    Int,
    Bool,
    Seq(SeqType),
    //Ref, // At the moment we don't need this
    /// TypedRef: the first parameter is the name of the predicate that encodes the type
    TypedRef(TypedRef),
    Domain(DomainType),
    Snapshot(SnapshotType),
    // For type substitution
    TypeVar(TypeVar),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            _ => write!(f, "{}", self),
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        discriminant(self) == discriminant(other) &&
        match (self, other) {
            (Type::Seq(seq), Type::Seq(other_seq)) => seq == other_seq,
            (Type::TypedRef(typed_ref), Type::TypedRef(other_typed_ref)) => typed_ref == other_typed_ref,
            (Type::Domain(domain_type), Type::Domain(other_domain_type)) => domain_type == other_domain_type,
            (Type::Snapshot(snapshot_type), Type::Snapshot(other_snapshot_type)) => snapshot_type == other_snapshot_type,
            (Type::TypeVar(type_var), Type::TypeVar(other_type_var)) => type_var == other_type_var,
            _ => true,
        }
    }
}

impl Eq for Type {}

impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SeqType {
    pub typ: Box<Type>,
}

impl PartialEq for SeqType {
    fn eq(&self, other: &Self) -> bool {
        *self.typ == *other.typ
    }
}

impl Eq for SeqType {}

impl Hash for SeqType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self.typ).hash(state);
    }
}

impl fmt::Display for SeqType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Seq[{}]", &self.typ)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypedRef {
    pub label: String,
    pub arguments: Vec<Type>,
}

impl PartialEq for TypedRef {
    fn eq(&self, other: &Self) -> bool {
        (&self.label, &self.arguments) == (&other.label, &other.arguments)
    }
}

impl Eq for TypedRef {}

impl Hash for TypedRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.label, &self.arguments).hash(state);
    }
}

impl fmt::Display for TypedRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Ref({})", &self.label)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DomainType {
    pub label: String,
    pub arguments: Vec<Type>,
}

impl PartialEq for DomainType {
    fn eq(&self, other: &Self) -> bool {
        (&self.label, &self.arguments) == (&other.label, &other.arguments)
    }
}

impl Eq for DomainType {}

impl Hash for DomainType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.label, &self.arguments).hash(state);
    }
}

impl fmt::Display for DomainType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Domain({})", &self.label)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SnapshotType {
    pub label: String,
    pub arguments: Vec<Type>,
}

impl PartialEq for SnapshotType {
    fn eq(&self, other: &Self) -> bool {
        (&self.label, &self.arguments) == (&other.label, &other.arguments)
    }
}

impl Eq for SnapshotType {}

impl Hash for SnapshotType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.label, &self.arguments).hash(state);
    }
}

impl fmt::Display for SnapshotType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Snapshot({})", &self.label)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeVar {
    pub label: String,
}

impl PartialEq for TypeVar {
    fn eq(&self, other: &Self) -> bool {
        &self.label == &other.label
    }
}

impl Eq for TypeVar {}

impl Hash for TypeVar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.label).hash(state);
    }
}

impl fmt::Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TypeVar({})", &self.label)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeId {
    Int,
    Bool,
    Ref,
    Seq,
    Domain,
    Snapshot,
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
