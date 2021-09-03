// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{converter::type_substitution::Generic, polymorphic::ast::*};
use std::{
    cmp::Ordering,
    collections::{hash_map::DefaultHasher, HashMap},
    fmt,
    hash::{Hash, Hasher},
    mem::discriminant,
};

pub trait WithIdentifier {
    fn get_identifier(&self) -> String;
}

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

    pub fn is_default(&self) -> bool {
        self.line == 0 && self.column == 0 && self.id == 0
    }
}

impl Default for Position {
    fn default() -> Self {
        Position::new(0, 0, 0)
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
}

impl std::ops::Add for PermAmount {
    type Output = Result<PermAmount, PermAmountError>;
    fn add(self, other: PermAmount) -> Self::Output {
        match (self, other) {
            (PermAmount::Read, PermAmount::Remaining)
            | (PermAmount::Remaining, PermAmount::Read) => Ok(PermAmount::Write),
            _ => Err(PermAmountError::InvalidAdd(self, other)),
        }
    }
}

impl std::ops::Sub for PermAmount {
    type Output = Result<PermAmount, PermAmountError>;
    fn sub(self, other: PermAmount) -> Result<PermAmount, PermAmountError> {
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

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
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
            Type::Seq(seq) => seq.fmt(f),
            Type::TypedRef(_) => write!(f, "Ref({})", self.encode_as_string()),
            Type::Domain(_) => write!(f, "Domain({})", self.encode_as_string()),
            Type::Snapshot(_) => write!(f, "Snapshot({})", self.encode_as_string()),
            Type::TypeVar(type_var) => type_var.fmt(f),
        }
    }
}

impl Type {
    pub fn is_typed_ref_or_type_var(&self) -> bool {
        self.is_typed_ref() || self.is_type_var()
    }

    pub fn is_typed_ref(&self) -> bool {
        matches!(self, &Type::TypedRef(_))
    }

    pub fn is_domain(&self) -> bool {
        matches!(self, &Type::Domain(_))
    }

    pub fn is_snapshot(&self) -> bool {
        matches!(self, &Type::Snapshot(_))
    }

    pub fn is_type_var(&self) -> bool {
        matches!(self, &Type::TypeVar(_))
    }

    pub fn is_mir_reference(&self) -> bool {
        if let Type::TypedRef(TypedRef { label, .. }) = self {
            // FIXME: We should not rely on string names for type conversions.
            label == "ref"
        } else {
            false
        }
    }

    pub fn name(&self) -> String {
        match self {
            Type::Bool => "bool".to_string(),
            Type::Int => "int".to_string(),
            Type::Domain(_) | Type::Snapshot(_) | Type::TypedRef(_) | Type::TypeVar(_) => {
                self.encode_as_string()
            }
            Type::Seq(SeqType { box ref typ }) => typ.name(),
        }
    }

    /// Construct a new VIR type that corresponds to an enum variant.
    pub fn variant(self, variant: &str) -> Self {
        match self {
            Type::TypedRef(mut typed_ref) => {
                typed_ref.variant = variant.into();
                Type::TypedRef(typed_ref)
            }
            _ => unreachable!(),
        }
    }

    /// Replace all generic types with their instantiations by using string substitution.
    pub fn patch(self, substs: &HashMap<TypeVar, Type>) -> Self {
        self.substitute(substs)
    }

    pub fn typed_ref<S: Into<String>>(name: S) -> Self {
        Type::TypedRef(TypedRef {
            label: name.into(),
            arguments: vec![],
            variant: String::from(""),
        })
    }

    pub fn typed_ref_with_args<S: Into<String>>(name: S, arguments: Vec<Type>) -> Self {
        Type::TypedRef(TypedRef {
            label: name.into(),
            arguments,
            variant: String::from(""),
        })
    }

    pub fn domain<S: Into<String>>(name: S) -> Self {
        Type::Domain(DomainType {
            label: name.into(),
            arguments: vec![],
            variant: String::from(""),
        })
    }

    pub fn domain_with_args<S: Into<String>>(name: S, arguments: Vec<Type>) -> Self {
        Type::Domain(DomainType {
            label: name.into(),
            arguments,
            variant: String::from(""),
        })
    }

    pub fn snapshot<S: Into<String>>(name: S) -> Self {
        Type::Snapshot(SnapshotType {
            label: name.into(),
            arguments: vec![],
            variant: String::from(""),
        })
    }

    pub fn snapshot_with_args<S: Into<String>>(name: S, arguments: Vec<Type>) -> Self {
        Type::Snapshot(SnapshotType {
            label: name.into(),
            arguments,
            variant: String::from(""),
        })
    }

    // TODO: this is a temporary solution for converting the encoded type in type encoder as a snapshot variant, which ould be cleaner
    pub fn convert_to_snapshot(&self) -> Self {
        match self {
            Type::TypedRef(typed_ref) => Type::Snapshot(typed_ref.clone().into()),
            Type::TypeVar(_) => Type::Snapshot(SnapshotType {
                label: self.encode_as_string(),
                arguments: Vec::new(),
                variant: String::from(""),
            }),
            _ => unreachable!(),
        }
    }

    pub fn type_var<S: Into<String>>(name: S) -> Self {
        Type::TypeVar(TypeVar { label: name.into() })
    }

    pub fn get_type_var(&self) -> Option<TypeVar> {
        if let Type::TypeVar(type_var) = self {
            Some(type_var.clone())
        } else {
            None
        }
    }

    pub fn get_id(&self) -> TypeId {
        match self {
            Type::Bool => TypeId::Bool,
            Type::Int => TypeId::Int,
            Type::TypedRef(_) => TypeId::Ref,
            Type::Domain(_) => TypeId::Domain,
            Type::Snapshot(_) => TypeId::Snapshot,
            Type::Seq(_) => TypeId::Seq,
            Type::TypeVar(t) => unreachable!(t),
        }
    }

    pub fn encode_as_string(&self) -> String {
        match self {
            Type::TypedRef(TypedRef {
                label,
                arguments,
                variant,
            })
            | Type::Domain(DomainType {
                label,
                arguments,
                variant,
            })
            | Type::Snapshot(SnapshotType {
                label,
                arguments,
                variant,
            }) => {
                let label_str = label.as_str();
                match label_str {
                    "ref" | "raw_ref" | "Slice" => {
                        format!("{}${}", label_str, Self::encode_arguments(arguments))
                    }
                    // TODO: remove len constraint once encoders are all updated with polymorphic
                    array if array.starts_with("Array") && !arguments.is_empty() => {
                        format!("{}${}", label_str, Self::encode_arguments(arguments))
                    }
                    "tuple" => format!(
                        "tuple{}${}",
                        arguments.len(),
                        Self::encode_arguments(arguments)
                    ),
                    // TODO: remove len constraint once encoders are all updated with polymorphic
                    closure if closure.starts_with("closure") && !arguments.is_empty() => format!(
                        "{}${}${}",
                        closure,
                        arguments.len(),
                        Self::hash_arguments(arguments)
                    ),
                    adt if adt.starts_with("adt") => format!(
                        "{}${}{}",
                        &adt[4..],
                        Self::encode_substs(arguments),
                        variant
                    ),
                    _label => {
                        if !arguments.is_empty() {
                            // Projection
                            format!("{}${}", label_str, Self::encode_arguments(arguments))
                        } else {
                            // General cases (e.g. bool, isize, never, ...)
                            String::from(label_str)
                        }
                    }
                }
            }
            Type::TypeVar(TypeVar { label }) => format!("__TYPARAM__$_{}$__", label),
            x => unreachable!(x),
        }
    }

    /// The string to be appended to the encoding of certain types to make generics "less fragile".
    fn encode_substs(types: &[Type]) -> String {
        let mut composed_name = vec![
            "_beg_".to_string(), // makes generics "less fragile"
        ];
        let mut first = true;
        for typ in types.iter() {
            if first {
                first = false
            } else {
                // makes generics "less fragile"
                composed_name.push("_sep_".to_string());
            }
            composed_name.push(typ.encode_as_string());
        }
        composed_name.push("_end_".to_string()); // makes generics "less fragile"
        composed_name.join("$")
    }

    /// Converts vector of arguments to string connected with "$".
    fn encode_arguments(args: &[Type]) -> String {
        let mut composed_name = vec![];

        for arg in args.iter() {
            composed_name.push(arg.encode_as_string());
        }

        composed_name.join("$")
    }

    fn hash_arguments(args: &[Type]) -> u64 {
        let mut s = DefaultHasher::new();
        args.hash(&mut s);
        s.finish()
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
    pub variant: String,
}

impl PartialEq for TypedRef {
    fn eq(&self, other: &Self) -> bool {
        (&self.label, &self.arguments, &self.variant)
            == (&other.label, &other.arguments, &other.variant)
    }
}

impl Eq for TypedRef {}

impl Hash for TypedRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.label, &self.arguments, &self.variant).hash(state);
    }
}

impl From<SnapshotType> for TypedRef {
    fn from(snapshot: SnapshotType) -> Self {
        Self {
            label: snapshot.label,
            arguments: snapshot.arguments,
            variant: snapshot.variant,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DomainType {
    pub label: String,
    pub arguments: Vec<Type>,
    pub variant: String,
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

impl From<TypedRef> for DomainType {
    fn from(typed_ref: TypedRef) -> DomainType {
        DomainType {
            label: typed_ref.label,
            arguments: typed_ref.arguments,
            variant: typed_ref.variant,
        }
    }
}

impl From<TypeVar> for DomainType {
    fn from(type_var: TypeVar) -> DomainType {
        DomainType {
            label: type_var.label,
            arguments: vec![],
            variant: String::from(""),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SnapshotType {
    pub label: String,
    pub arguments: Vec<Type>,
    pub variant: String,
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

impl From<TypedRef> for SnapshotType {
    fn from(typed_ref: TypedRef) -> SnapshotType {
        SnapshotType {
            label: typed_ref.label,
            arguments: typed_ref.arguments,
            variant: typed_ref.variant,
        }
    }
}

impl From<TypeVar> for SnapshotType {
    fn from(type_var: TypeVar) -> SnapshotType {
        SnapshotType {
            label: type_var.label,
            arguments: vec![],
            variant: String::from(""),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct TypeVar {
    pub label: String,
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

impl LocalVar {
    pub fn new<S: Into<String>>(name: S, typ: Type) -> Self {
        LocalVar {
            name: name.into(),
            typ,
        }
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
            Type::TypedRef(_) | Type::TypeVar(_) => Some(self.typ.encode_as_string()),
            _ => None,
        }
    }
}

impl WithIdentifier for Field {
    fn get_identifier(&self) -> String {
        self.name.clone()
    }
}
