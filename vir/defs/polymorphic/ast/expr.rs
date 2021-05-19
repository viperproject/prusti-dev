// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::*;

#[derive(Debug, Clone)]
pub enum Expr {
    /// A local var
    Local(Local),
    /// An enum variant: base, variant index.
    Variant(Variant),
    /// A field access
    Field(FieldExpr),
    /// The inverse of a `val_ref` field access
    AddrOf(AddrOf),
    LabelledOld(LabelledOld),
    Const(ConstExpr),
    /// lhs, rhs, borrow, position
    MagicWand(MagicWand),
    /// PredicateAccessPredicate: predicate_name, arg, permission amount
    PredicateAccessPredicate(PredicateAccessPredicate),
    FieldAccessPredicate(FieldAccessPredicate),
    UnaryOp(UnaryOp),
    BinOp(BinOp),
    /// Unfolding: predicate name, predicate_args, in_expr, permission amount, enum variant
    Unfolding(Unfolding),
    /// Cond: guard, then_expr, else_expr
    Cond(Cond),
    /// ForAll: variables, triggers, body
    ForAll(ForAll),
    /// let variable == (expr) in body
    LetExpr(LetExpr),
    /// FuncApp: function_name, args, formal_args, return_type, Viper position
    FuncApp(FuncApp),
    /// Domain function application: function_name, args, formal_args, return_type, domain_name, Viper position (unused)
    DomainFuncApp(DomainFuncApp),
    // TODO use version below once providing a return type is supported in silver
    // DomainFuncApp(String, Vec<Expr>, Vec<LocalVar>, Type, String, Position),
    /// Inhale Exhale: inhale expression, exhale expression, Viper position (unused)
    InhaleExhale(InhaleExhale),
    /// Inform the fold-unfold algorithm that at this program point a enum type can be downcasted
    /// to one of its variants. This statement is a no-op for Viper.
    /// Arguments:
    /// * expression in which the downcast is visible
    /// * place to the enumeration that is downcasted
    /// * field that encodes the variant
    Downcast(Downcast),
}

/// A component that can be used to represent a place as a vector.
#[derive(Debug, Clone)]
pub enum PlaceComponent {
    Field(Field, Position),
    Variant(Field, Position),
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOpKind {
    Not,
    Minus,
}

#[derive(Debug, Clone, Copy)]
pub enum BinOpKind {
    EqCmp,
    NeCmp,
    GtCmp,
    GeCmp,
    LtCmp,
    LeCmp,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Implies,
}

#[derive(Debug, Clone)]
pub enum Const {
    Bool(bool),
    Int(i64),
    BigInt(String),
    /// All function pointers share the same constant, because their function
    /// is determined by the type system.
    FnPtr,
}

/// Individual structs for different cases of Expr
#[derive(Debug, Clone)]
pub struct Local {
    pub variable: LocalVar,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct Variant {
    pub base: Box<Expr>,
    pub variant_index: Field,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct FieldExpr {
    pub base: Box<Expr>,
    pub field: Field,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct AddrOf {
    pub base: Box<Expr>,
    pub addr_type: Type,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct LabelledOld {
    pub label: String,
    pub expr: Box<Expr>,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct ConstExpr {
    pub value: Const,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct MagicWand {
    pub left: Box<Expr>,
    pub right: Box<Expr>,
    pub borrow: Option<Borrow>,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct PredicateAccessPredicate {
    pub predicate_name: String,
    pub argument: Box<Expr>,
    pub permission: PermAmount,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct FieldAccessPredicate {
    pub expr: Box<Expr>,
    pub permission: PermAmount,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct UnaryOp {
    pub op_kind: UnaryOpKind,
    pub expr: Box<Expr>,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct BinOp {
    pub op_kind: BinOpKind,
    pub left: Box<Expr>,
    pub right: Box<Expr>,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct Unfolding {
    pub predicate_name: String,
    pub arguments: Vec<Expr>,
    pub expr: Box<Expr>,
    pub permission: PermAmount,
    pub variant: MaybeEnumVariantIndex,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct Cond {
    pub guard: Box<Expr>,
    pub then_expr : Box<Expr>,
    pub else_expr: Box<Expr>,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct ForAll {
    pub variables: Vec<LocalVar>,
    pub triggers: Vec<Trigger>,
    pub body: Box<Expr>,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct LetExpr {
    pub variable: LocalVar,
    pub expr: Box<Expr>,
    pub body: Box<Expr>,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct FuncApp {
    pub function_name: String,
    pub arguments: Vec<Expr>,
    pub formal_arguments: Vec<LocalVar>,
    pub return_type: Type,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct DomainFuncApp {
    pub function_name: String,
    pub arguments: Vec<Expr>,
    pub formal_arguments: Vec<LocalVar>,
    pub return_type: Type,
    pub domain_name: String,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct InhaleExhale {
    pub inhale_expr: Box<Expr>,
    pub exhale_expr: Box<Expr>,
    pub position: Position,
}

#[derive(Debug, Clone)]
pub struct Downcast {
    pub base: Box<Expr>,
    pub enum_place: Box<Expr>,
    pub field: Field,
}