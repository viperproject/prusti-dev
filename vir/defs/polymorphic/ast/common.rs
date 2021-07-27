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
    ops,
};

use super::super::super::{legacy, converter};

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
}

impl From<Position> for legacy::Position {
    fn from(position: Position) -> legacy::Position {
        legacy::Position::new(
            position.line,
            position.column,
            position.id
        )
    }
}

pub enum PermAmountError {
    InvalidAdd(PermAmount, PermAmount),
    InvalidSub(PermAmount, PermAmount)
}

impl From<PermAmountError> for legacy::PermAmountError {
    fn from(perm_amount_error: PermAmountError) -> legacy::PermAmountError {
        match perm_amount_error {
            PermAmountError::InvalidAdd(perm_amount_1, perm_amount_2) => legacy::PermAmountError::InvalidAdd(legacy::PermAmount::from(perm_amount_1), legacy::PermAmount::from(perm_amount_2)),
            PermAmountError::InvalidSub(perm_amount_1, perm_amount_2) => legacy::PermAmountError::InvalidSub(legacy::PermAmount::from(perm_amount_1), legacy::PermAmount::from(perm_amount_2)),
        }
    }
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

impl From<PermAmount> for legacy::PermAmount {
    fn from(perm_amount: PermAmount) -> legacy::PermAmount {
        match perm_amount {
            PermAmount::Read => legacy::PermAmount::Read,
            PermAmount::Write => legacy::PermAmount::Write,
            PermAmount::Remaining => legacy::PermAmount::Remaining,
        }
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

impl From<Type> for legacy::Type {
    fn from(typ: Type) -> legacy::Type {
        match typ {
            Type::Int => legacy::Type::Int,
            Type::Bool => legacy::Type::Bool,
            Type::Seq(seq) => legacy::Type::Seq(Box::new(legacy::Type::from((*seq.typ).clone()))),
            Type::TypedRef(typed_ref) => legacy::Type::TypedRef(typed_ref.label.clone()),
            Type::Domain(domain_type) => legacy::Type::Domain(domain_type.label.clone()),
            Type::Snapshot(snapshot_type) => legacy::Type::Snapshot(snapshot_type.label.clone()),
            // Does not happen, unless type substitution is incorrect
            Type::TypeVar(_) => unreachable!(),
        }
    }
}

impl converter::Generic for Type {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        match self {
            Type::Bool | Type::Int => self,
            Type::Seq(mut seq) => {
                let typ = *seq.typ;
                *seq.typ = typ.substitute(map);
                Type::Seq(seq)
            },
            Type::TypedRef(mut typed_ref) => {
                typed_ref.arguments = typed_ref.arguments.into_iter().map(|arg| arg.substitute(map)).collect();
                Type::TypedRef(typed_ref)
            },
            Type::Domain(mut domain_type) => {
                domain_type.arguments = domain_type.arguments.into_iter().map(|arg| arg.substitute(map)).collect();
                Type::Domain(domain_type)
            },
            Type::Snapshot(mut snapshot_type) => {
                snapshot_type.arguments = snapshot_type.arguments.into_iter().map(|arg| arg.substitute(map)).collect();
                Type::Snapshot(snapshot_type)
            },
            Type::TypeVar(type_var) => {
                match map.get(&type_var) {
                    Some(substituted_typ) => substituted_typ.clone(),
                    _ => Type::TypeVar(type_var),
                }
            }
        }
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

impl From<TypeId> for legacy::TypeId {
    fn from(type_id: TypeId) -> legacy::TypeId {
        match type_id {
            TypeId::Int => legacy::TypeId::Int,
            TypeId::Bool => legacy::TypeId::Bool,
            TypeId::Ref => legacy::TypeId::Ref,
            TypeId::Seq => legacy::TypeId::Seq,
            TypeId::Domain => legacy::TypeId::Domain,
            TypeId::Snapshot => legacy::TypeId::Snapshot,
        }
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

impl From<LocalVar> for legacy::LocalVar {
    fn from(type_id: LocalVar) -> legacy::LocalVar {
        legacy::LocalVar {
            name: type_id.name.clone(),
            typ: legacy::Type::from(type_id.typ.clone()),
        }
    }
}

impl converter::Generic for LocalVar {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut local_var = self;
        local_var.typ = local_var.typ.substitute(map);
        local_var
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

impl From<Field> for legacy::Field {
    fn from(field: Field) -> legacy::Field {
        legacy::Field {
            name: field.name.clone(),
            typ: legacy::Type::from(field.typ.clone()),
        }
    }
}

impl converter::Generic for Field {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut field = self;
        field.typ = field.typ.substitute(map);
        field
    }
}