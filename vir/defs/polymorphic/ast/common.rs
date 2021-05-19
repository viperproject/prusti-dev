// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

/// The identifier of a statement. Used in error reporting.

use std::collections::HashMap;

#[derive(Debug, Copy, Clone)]
pub struct Position {
    line: i32,
    column: i32,
    id: u64,
}

pub enum PermAmountError {
    InvalidAdd(PermAmount, PermAmount),
    InvalidSub(PermAmount, PermAmount)
}

/// The permission amount.
#[derive(Debug, Clone, Copy)]
pub enum PermAmount {
    Read,
    Write,
    /// The permission remaining after ``Read`` was subtracted from ``Write``.
    Remaining,
}

#[derive(Debug, Clone)]
pub enum Type {
    Int,
    Bool,
    //Ref, // At the moment we don't need this
    /// TypedRef: the first parameter is the name of the predicate that encodes the type
    TypedRef(TypedRef),
    Domain(Domain),
    TypeVar(TypeVar),
}

#[derive(Debug, Clone, Copy)]
pub enum TypeId {
    Int,
    Bool,
    Ref,
    Domain,
    TypeVar,
}

#[derive(Debug, Clone)]
pub struct LocalVar {
    pub name: String,
    pub typ: Type,
}

#[derive(Debug, Clone)]
pub struct Field {
    pub name: String,
    pub typ: Type,
}

#[derive(Debug, Clone)]
pub struct TypedRef {
    name: String,
    type_map: HashMap<TypeVar, Type>,
}

#[derive(Debug, Clone)]
pub struct Domain {
    name: String,
    type_map: HashMap<TypeVar, Type>,
}

#[derive(Debug, Clone)]
pub struct TypeVar {
    name: String,
}
