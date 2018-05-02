// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id();

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Perm {
    pub num: u32,
    pub den: u32,
}

impl Perm {
    pub fn full() -> Self {
        Perm {
            num: 1,
            den: 1
        }
    }

    pub fn none() -> Self {
        Perm {
            num: 0,
            den: 1
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Bool,
    Ref,
    /// TypedRef: the first parameter is the name of the predicate that encodes the type
    TypedRef(String)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LocalVar {
    pub name: String,
    pub typ: Type
}

impl LocalVar {
    pub fn new<S: Into<String>>(name: S, typ: Type) -> Self {
        LocalVar {
            name: name.into(),
            typ
        }
    }
}

impl fmt::Display for LocalVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Field {
    pub name: String,
    pub typ: Type
}

impl Field {
    pub fn new<S: Into<String>>(name: S, typ: Type) -> Self {
        Field {
            name: name.into(),
            typ
        }
    }
}

impl fmt::Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Place {
    Base(LocalVar),
    Field(Box<Place>, Field)
}

impl Place {
    pub fn access(self, field: Field) -> Self {
        Place::Field(box self, field)
    }

    pub fn parent(&self) -> Option<&Place> {
        match self {
            &Place::Base(_) => None,
            &Place::Field(ref place, _) => Some(place)
        }
    }

    pub fn base(&self) -> &LocalVar {
        match self {
            &Place::Base(ref var) => var,
            &Place::Field(ref place, _) => place.base(),
        }
    }

    pub fn has_prefix(&self, other: &Place) -> bool {
        if self == other {
            true
        } else {
            match self.parent() {
                Some(parent) => parent.has_prefix(other),
                None => false
            }
        }
    }

    pub fn all_prefixes(&self) -> Vec<&Place> {
        let mut res = match self.parent() {
            Some(parent) => parent.all_prefixes(),
            None => vec![]
        };
        res.push(self);
        res
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Place::Base(ref var) => write!(f, "{}", var),
            &Place::Field(ref place, ref field) => write!(f, "{}.{}", place, field)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Stmt {
    Comment(String),
    Label(String),
    Inhale(Expr),
    Exhale(Expr, Id),
    Assert(Expr, Id),
    /// MethodCall: method_name, args, targets
    MethodCall(String, Vec<Expr>, Vec<LocalVar>),
    Assign(Place, Expr),
    New(LocalVar, Vec<Field>),
}

impl Stmt {
    pub fn comment<S: ToString>(comment: S) -> Self {
        Stmt::Comment(comment.to_string())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Const(Const),
    Place(Place),
    Old(Box<Expr>),
    LabelledOld(Box<Expr>, String),
    MagicWand(Box<Expr>, Box<Expr>),
    /// PredicateAccess: predicate_name, args
    PredicateAccess(String, Vec<Expr>),
    PredicateAccessPredicate(Box<Expr>, Perm),
    FieldAccessPredicate(Box<Expr>, Perm),
    UnaryOp(UnaryOpKind, Box<Expr>),
    BinOp(BinOpKind, Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOpKind {
    EqCmp, GtCmp, LeCmp, Add, Sub, And
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOpKind {
    Not, Minus
}

impl Expr {
    pub fn not(expr: Expr) -> Self {
        Expr::UnaryOp(UnaryOpKind::Not, box expr)
    }

    pub fn minus(expr: Expr) -> Self {
        Expr::UnaryOp(UnaryOpKind::Minus, box expr)
    }

    pub fn and(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::And, box left, box right)
    }

    pub fn gt_cmp(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::GtCmp, box left, box right)
    }

    pub fn le_cmp(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::LeCmp, box left, box right)
    }

    pub fn eq_cmp(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::EqCmp, box left, box right)
    }

    pub fn add(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::Add, box left, box right)
    }

    pub fn sub(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::Sub, box left, box right)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Const {
    Bool(bool),
    Null,
    Int(i64),
    BigInt(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Predicate {
    pub name: String,
    pub args: Vec<LocalVar>,
    pub body: Option<Expr>,
}

impl Predicate {
    pub fn new<S: Into<String>>(name: S, args: Vec<LocalVar>, body: Option<Expr>) -> Self {
        Predicate {
            name: name.into(),
            args,
            body
        }
    }
}
