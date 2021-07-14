// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::super::borrows::Borrow;
use crate::polymorphic::ast::*;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::mem::discriminant;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
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

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

/// A component that can be used to represent a place as a vector.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PlaceComponent {
    Field(Field, Position),
    Variant(Field, Position),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum UnaryOpKind {
    Not,
    Minus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Const {
    Bool(bool),
    Int(i64),
    BigInt(String),
    /// All function pointers share the same constant, because their function
    /// is determined by the type system.
    FnPtr,
}

/// Individual structs for different cases of Expr
#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct Local {
    pub variable: LocalVar,
    pub position: Position,
}

impl fmt::Display for Local {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.variable)
    }
}

impl PartialEq for Local {
    fn eq(&self, other: &Self) -> bool {
        &self.variable == &other.variable
    }
}

impl Hash for Local {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&self.variable).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct Variant {
    pub base: Box<Expr>,
    pub variant_index: Field,
    pub position: Position,
}

impl fmt::Display for Variant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}[{}]", &self.base, &self.variant_index)
    }
}

impl PartialEq for Variant {
    fn eq(&self, other: &Self) -> bool {
        (&*self.base, &self.variant_index) == (&*other.base, &other.variant_index)
    }
}

impl Hash for Variant {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&*self.base, &self.variant_index).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct FieldExpr {
    pub base: Box<Expr>,
    pub field: Field,
    pub position: Position,
}

impl fmt::Display for FieldExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", &self.base, &self.field)
    }
}

impl PartialEq for FieldExpr {
    fn eq(&self, other: &Self) -> bool {
        (&*self.base, &self.field) == (&*other.base, &other.field)
    }
}

impl Hash for FieldExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&*self.base, &self.field).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct AddrOf {
    pub base: Box<Expr>,
    pub addr_type: Type,
    pub position: Position,
}

impl fmt::Display for AddrOf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "&({})", &self.base)
    }
}

impl PartialEq for AddrOf {
    fn eq(&self, other: &Self) -> bool {
        (&*self.base, &self.addr_type) == (&*other.base, &other.addr_type)
    }
}

impl Hash for AddrOf {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&*self.base, &self.addr_type).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct LabelledOld {
    pub label: String,
    pub base: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for LabelledOld {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "old[{}]({})", &self.label, &self.base)
    }
}

impl PartialEq for LabelledOld {
    fn eq(&self, other: &Self) -> bool {
        (&self.label, &*self.base) == (&other.label, &*other.base)
    }
}

impl Hash for LabelledOld {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&self.label, &*self.base).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct ConstExpr {
    pub value: Const,
    pub position: Position,
}

impl fmt::Display for ConstExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.value)
    }
}

impl PartialEq for ConstExpr {
    fn eq(&self, other: &Self) -> bool {
        &self.value == &other.value
    }
}

impl Hash for ConstExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&self.value).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct MagicWand {
    pub left: Box<Expr>,
    pub right: Box<Expr>,
    pub borrow: Option<Borrow>,
    pub position: Position,
}

impl fmt::Display for MagicWand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}) {:?} --* ({})", &self.left, &self.borrow, &self.right)
    }
}

impl PartialEq for MagicWand {
    fn eq(&self, other: &Self) -> bool {
        (&*self.left, &*self.right, self.borrow) == (&*other.left, &*other.right, other.borrow)
    }
}

impl Hash for MagicWand {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&*self.left, &*self.right, self.borrow).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct PredicateAccessPredicate {
    pub predicate_name: String,
    pub argument: Box<Expr>,
    pub permission: PermAmount,
    pub position: Position,
}

impl fmt::Display for PredicateAccessPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "acc({}({}), {})", &self.predicate_name, &self.argument, self.permission)
    }
}

impl PartialEq for PredicateAccessPredicate {
    fn eq(&self, other: &Self) -> bool {
        (&self.predicate_name, &self.argument, self.permission) == (&other.predicate_name, &other.argument, other.permission)
    }
}

impl Hash for PredicateAccessPredicate {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&self.predicate_name, &self.argument, self.permission).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct FieldAccessPredicate {
    pub base: Box<Expr>,
    pub permission: PermAmount,
    pub position: Position,
}

impl fmt::Display for FieldAccessPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "acc({}, {})", &self.base, self.permission)
    }
}

impl PartialEq for FieldAccessPredicate {
    fn eq(&self, other: &Self) -> bool {
        (&*self.base, self.permission) == (&*other.base, other.permission)
    }
}

impl Hash for FieldAccessPredicate {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&*self.base, self.permission).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct UnaryOp {
    pub op_kind: UnaryOpKind,
    pub argument: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}({})", &self.op_kind, &self.argument)
    }
}

impl PartialEq for UnaryOp {
    fn eq(&self, other: &Self) -> bool {
        (&self.op_kind, &*self.argument) == (&other.op_kind, &*other.argument)
    }
}

impl Hash for UnaryOp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&self.op_kind, &*self.argument).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct BinOp {
    pub op_kind: BinOpKind,
    pub left: Box<Expr>,
    pub right: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}) {} ({})", &self.left, &self.op_kind, &self.right)
    }
}

impl PartialEq for BinOp {
    fn eq(&self, other: &Self) -> bool {
        (&self.op_kind, &*self.left, &*self.right) == (&other.op_kind, &*other.left, &*other.right)
    }
}

impl Hash for BinOp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&self.op_kind, &*self.left, &*self.right).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct Unfolding {
    pub predicate_name: String,
    pub arguments: Vec<Expr>,
    pub base: Box<Expr>,
    pub permission: PermAmount,
    pub variant: MaybeEnumVariantIndex,
    pub position: Position,
}

impl fmt::Display for Unfolding {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "(unfolding acc({}({}), {}) in {})",
            if let Some(variant_index) = &self.variant {
                format!("{}<variant {}>", &self.predicate_name, variant_index)
            } else {
                format!("{}", &self.predicate_name)
            },
            &(self.arguments).iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.permission,
            &self.base
        )
    }
}

impl PartialEq for Unfolding {
    fn eq(&self, other: &Self) -> bool {
        (&self.predicate_name, &self.arguments, &*self.base, self.permission, &self.variant) == (&other.predicate_name, &other.arguments, &*other.base, other.permission, &other.variant)
    }
}

impl Hash for Unfolding {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&self.predicate_name, &self.arguments, &*self.base, self.permission, &self.variant).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct Cond {
    pub guard: Box<Expr>,
    pub then_expr : Box<Expr>,
    pub else_expr: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for Cond {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({})?({}):({})", &self.guard, &self.then_expr, &self.else_expr)
    }
}

impl PartialEq for Cond {
    fn eq(&self, other: &Self) -> bool {
        (&*self.guard, &*self.then_expr, &*self.else_expr) == (&*other.guard, &*other.then_expr, &*other.else_expr)
    }
}

impl Hash for Cond {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&*self.guard, &*self.then_expr, &*self.else_expr).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct ForAll {
    pub variables: Vec<LocalVar>,
    pub triggers: Vec<Trigger>,
    pub body: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for ForAll {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "forall {} {} :: {}",
            (&self.variables).iter()
                .map(|x| format!("{:?}", x))
                .collect::<Vec<String>>()
                .join(", "),
            (&self.triggers)
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            (&self.body).to_string()
        )
    }
}

impl PartialEq for ForAll {
    fn eq(&self, other: &Self) -> bool {
        (&self.variables, &self.triggers, &*self.body) == (&other.variables, &other.triggers, &*other.body)
    }
}

impl Hash for ForAll {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&self.variables, &self.triggers, &*self.body).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct LetExpr {
    pub variable: LocalVar,
    pub def: Box<Expr>,
    pub body: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for LetExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "(let {:?} == ({}) in {})",
            &self.variable,
            (&self.def).to_string(),
            (&self.body).to_string()
        )
    }
}

impl PartialEq for LetExpr {
    fn eq(&self, other: &Self) -> bool {
        (&self.variable, &*self.def, &*self.body) == (&other.variable, &*other.def, &*other.body)
    }
}

impl Hash for LetExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&self.variable, &*self.def, &*self.body).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct FuncApp {
    pub function_name: String,
    pub arguments: Vec<Expr>,
    pub formal_arguments: Vec<LocalVar>,
    pub return_type: Type,
    pub position: Position,
}

impl fmt::Display for FuncApp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}<{},{}>({})",
            &self.function_name,
            (&self.formal_arguments)
                .iter()
                .map(|p| p.typ.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            &(self.return_type).to_string(),
            &(self.arguments).iter()
                .map(|f| f.to_string())
                .collect::<Vec<String>>()
                .join(", "),
        )
    }
}

impl PartialEq for FuncApp {
    fn eq(&self, other: &Self) -> bool {
        (&self.function_name, &self.arguments) == (&other.function_name, &other.arguments)
    }
}

impl Hash for FuncApp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&self.function_name, &self.arguments).hash(state);
    }
}


#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct DomainFuncApp {
    pub domain_function: DomainFunc,
    pub arguments: Vec<Expr>,
    pub position: Position,
}

impl fmt::Display for DomainFuncApp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}({})",
            (&self.domain_function).name,
            (&self.arguments).iter()
                .map(|f| f.to_string())
                .collect::<Vec<String>>()
                .join(", "),
        )
    }
}

impl PartialEq for DomainFuncApp {
    fn eq(&self, other: &Self) -> bool {
        (&self.domain_function, &self.arguments) == (&other.domain_function, &other.arguments)
    }
}

impl Hash for DomainFuncApp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&self.domain_function, &self.arguments).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct InhaleExhale {
    pub inhale_expr: Box<Expr>,
    pub exhale_expr: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for InhaleExhale {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[({}), ({})]", &self.inhale_expr, &self.exhale_expr)
    }
}

impl PartialEq for InhaleExhale {
    fn eq(&self, other: &Self) -> bool {
        (&*self.inhale_expr, &*self.exhale_expr) == (&*other.inhale_expr, &*other.exhale_expr)
    }
}

impl Hash for InhaleExhale {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&*self.inhale_expr, &*self.exhale_expr).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct Downcast {
    pub base: Box<Expr>,
    pub enum_place: Box<Expr>,
    pub field: Field,
}

impl fmt::Display for Downcast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "(downcast {} to {} in {})",
            (&self.enum_place).to_string(),
            &self.field,
            (&self.base).to_string(),
        )
    }
}

impl PartialEq for Downcast {
    fn eq(&self, other: &Self) -> bool {
        (&*self.base, &*self.enum_place, &self.field) == (&*other.base, &*other.enum_place, &other.field)
    }
}

impl Hash for Downcast {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        (&*self.base, &*self.enum_place, &self.field).hash(state);
    }
}

impl fmt::Display for UnaryOpKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UnaryOpKind::Not => write!(f, "!"),
            UnaryOpKind::Minus => write!(f, "-"),
        }
    }
}

impl fmt::Display for BinOpKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BinOpKind::EqCmp => write!(f, "=="),
            BinOpKind::NeCmp => write!(f, "!="),
            BinOpKind::GtCmp => write!(f, ">"),
            BinOpKind::GeCmp => write!(f, ">="),
            BinOpKind::LtCmp => write!(f, "<"),
            BinOpKind::LeCmp => write!(f, "<="),
            BinOpKind::Add => write!(f, "+"),
            BinOpKind::Sub => write!(f, "-"),
            BinOpKind::Mul => write!(f, "*"),
            BinOpKind::Div => write!(f, "\\"),
            BinOpKind::Mod => write!(f, "%"),
            BinOpKind::And => write!(f, "&&"),
            BinOpKind::Or => write!(f, "||"),
            BinOpKind::Implies => write!(f, "==>"),
        }
    }
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Const::Bool(val) => write!(f, "{}", val),
            Const::Int(val) => write!(f, "{}", val),
            Const::BigInt(ref val) => write!(f, "{}", val),
            Const::FnPtr => write!(f, "FnPtr"),
        }
    }
}
