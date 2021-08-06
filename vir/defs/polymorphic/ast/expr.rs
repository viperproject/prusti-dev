// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::super::borrows::Borrow;
use crate::polymorphic::ast::*;
use std::collections::{HashMap};
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
    /// Container Operation on a Viper container (e.g. Seq index)
    ContainerOp(ContainerOp),
    /// Viper Seq
    Seq(Seq),
    /// Unfolding: predicate name, predicate_args, in_expr, permission amount, enum variant
    Unfolding(Unfolding),
    /// Cond: guard, then_expr, else_expr
    Cond(Cond),
    /// ForAll: variables, triggers, body
    ForAll(ForAll),
    /// Exists: variables, triggers, body
    Exists(Exists),
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
    Downcast(DowncastExpr),
    /// Snapshot call to convert from a Ref to a snapshot value
    SnapApp(SnapApp),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Local(local) => local.fmt(f),
            Expr::Variant(variant) => variant.fmt(f),
            Expr::Field(field) => field.fmt(f),
            Expr::AddrOf(addr_of) => addr_of.fmt(f),
            Expr::Const(const_expr) => const_expr.fmt(f),
            Expr::LabelledOld(labelled_old) => labelled_old.fmt(f),
            Expr::MagicWand(magic_wand) => magic_wand.fmt(f),
            Expr::PredicateAccessPredicate(predicate_access_predicate) => predicate_access_predicate.fmt(f),
            Expr::FieldAccessPredicate(field_access_predicate) => field_access_predicate.fmt(f),
            Expr::UnaryOp(unary_op) => unary_op.fmt(f),
            Expr::BinOp(bin_op) => bin_op.fmt(f),
            Expr::Unfolding(unfolding) => unfolding.fmt(f),
            Expr::Cond(cond) => cond.fmt(f),
            Expr::ForAll(for_all) => for_all.fmt(f),
            Expr::Exists(exists) => exists.fmt(f),
            Expr::LetExpr(let_expr) => let_expr.fmt(f),
            Expr::FuncApp(func_app) => func_app.fmt(f),
            Expr::DomainFuncApp(domain_func_app) => domain_func_app.fmt(f),
            Expr::InhaleExhale(inhale_exhale) => inhale_exhale.fmt(f),
            Expr::SnapApp(snap_app) => snap_app.fmt(f),
            Expr::ContainerOp(container_op) => container_op.fmt(f),
            Expr::Seq(seq) => seq.fmt(f),
            Expr::Downcast(downcast_expr) => downcast_expr.fmt(f),
        }
    }
}

impl Expr {
    pub fn pos(&self) -> Position {
        match self {
            Expr::Local(local) => local.position,
            Expr::Variant(variant) => variant.position,
            Expr::Field(field) => field.position,
            Expr::AddrOf(addr_of) => addr_of.position,
            Expr::Const(const_expr) => const_expr.position,
            Expr::LabelledOld(labelled_old) => labelled_old.position,
            Expr::MagicWand(magic_wand) => magic_wand.position,
            Expr::PredicateAccessPredicate(predicate_access_predicate) => predicate_access_predicate.position,
            Expr::FieldAccessPredicate(field_access_predicate) => field_access_predicate.position,
            Expr::UnaryOp(unary_op) => unary_op.position,
            Expr::BinOp(bin_op) => bin_op.position,
            Expr::Unfolding(unfolding) => unfolding.position,
            Expr::Cond(cond) => cond.position,
            Expr::ForAll(for_all) => for_all.position,
            Expr::Exists(exists) => exists.position,
            Expr::LetExpr(let_expr) => let_expr.position,
            Expr::FuncApp(func_app) => func_app.position,
            Expr::DomainFuncApp(domain_func_app) => domain_func_app.position,
            Expr::InhaleExhale(inhale_exhale) => inhale_exhale.position,
            Expr::SnapApp(snap_app) => snap_app.position,
            Expr::ContainerOp(container_op) => container_op.position,
            Expr::Seq(seq) => seq.position,
            Expr::Downcast(downcast_expr) => (*downcast_expr.base).pos(),
        }
    }

    pub fn acc_permission(place: Expr, perm: PermAmount) -> Self {
        Expr::FieldAccessPredicate(FieldAccessPredicate {
            base: Box::new(place),
            permission: perm,
            position: Position::default(),
        })
    }

    pub fn eq_cmp(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOp {
            op_kind: BinOpKind::EqCmp,
            left: Box::new(left),
            right: Box::new(right),
            position: Position::default(),
        })
    }

    pub fn le_cmp(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOp {
            op_kind: BinOpKind::LeCmp,
            left: Box::new(left),
            right: Box::new(right),
            position: Position::default(),
        })
    }

    pub fn and(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOp {
            op_kind: BinOpKind::And,
            left: Box::new(left),
            right: Box::new(right),
            position: Position::default(),
        })
    }

    pub fn or(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOp {
            op_kind: BinOpKind::Or,
            left: Box::new(left),
            right: Box::new(right),
            position: Position::default(),
        })
    }

    pub fn implies(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOp {
            op_kind: BinOpKind::Implies,
            left: Box::new(left),
            right: Box::new(right),
            position: Position::default(),
        })
    }

    pub fn predicate_access_predicate<S: ToString>(name: S, place: Expr, perm: PermAmount) -> Self {
        let pos = place.pos();
        Expr::PredicateAccessPredicate(PredicateAccessPredicate {
            predicate_name: name.to_string(),
            argument: Box::new(place),
            permission: perm,
            position: pos,
        })
    }

    pub fn field(self, field: Field) -> Self {
        Expr::Field(FieldExpr {
            base: Box::new(self),
            field: field,
            position: Position::default(),
        })
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ContainerOpKind {
    SeqIndex,
    SeqConcat,
    SeqLen,
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
        (&self.op_kind, &*self.left, &*self.right).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct ContainerOp {
    pub op_kind: ContainerOpKind,
    pub left: Box<Expr>,
    pub right: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for ContainerOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.op_kind {
            ContainerOpKind::SeqIndex => write!(f, "{}[{}]", &self.left, &self.right),
            ContainerOpKind::SeqConcat => write!(f, "{} ++ {}", &self.left, &self.right),
            ContainerOpKind::SeqLen => write!(f, "|{}|", &self.left),
        }
    }
}

impl PartialEq for ContainerOp {
    fn eq(&self, other: &Self) -> bool {
        (&self.op_kind, &*self.left, &*self.right) == (&other.op_kind, &*other.left, &*other.right)
    }
}

impl Hash for ContainerOp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.op_kind, &*self.left, &*self.right).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct Seq {
    pub typ: Type,
    pub elements: Vec<Expr>,
    pub position: Position,
}

impl fmt::Display for Seq {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let typ = &self.typ;
        let elems_printed = self.elements.iter().map(|e| format!("{}", e)).collect::<Vec<_>>().join(", ");
        let elem_ty = if let Type::Seq(seq_type) = typ { 
            &*seq_type.typ
         } else { unreachable!() };
        write!(f, "Seq[{}]({})", elem_ty, elems_printed)
    }
}

impl PartialEq for Seq {
    fn eq(&self, other: &Self) -> bool {
        (&self.typ, &*self.elements) == (&other.typ, &*other.elements)
    }
}

impl Hash for Seq {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.typ, &*self.elements).hash(state);
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
        (&self.variables, &self.triggers, &*self.body).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct Exists {
    pub variables: Vec<LocalVar>,
    pub triggers: Vec<Trigger>,
    pub body: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for Exists {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "exists {} {} :: {}",
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

impl PartialEq for Exists {
    fn eq(&self, other: &Self) -> bool {
        (&self.variables, &self.triggers, &*self.body) == (&other.variables, &other.triggers, &*other.body)
    }
}

impl Hash for Exists {
    fn hash<H: Hasher>(&self, state: &mut H) {
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
        (&*self.inhale_expr, &*self.exhale_expr).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct DowncastExpr {
    pub base: Box<Expr>,
    pub enum_place: Box<Expr>,
    pub field: Field,
}

impl fmt::Display for DowncastExpr {
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

impl PartialEq for DowncastExpr {
    fn eq(&self, other: &Self) -> bool {
        (&*self.base, &*self.enum_place, &self.field) == (&*other.base, &*other.enum_place, &other.field)
    }
}

impl Hash for DowncastExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self.base, &*self.enum_place, &self.field).hash(state);
    }
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct SnapApp {
    pub base: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for SnapApp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "snap({})", (&*self.base).to_string())
    }
}

impl PartialEq for SnapApp {
    fn eq(&self, other: &Self) -> bool {
        &*self.base == &*other.base
    }
}

impl Hash for SnapApp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self.base).hash(state);
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

pub trait ExprIterator {
    /// Conjoin a sequence of expressions into a single expression.
    /// Returns true if the sequence has no elements.
    fn conjoin(&mut self) -> Expr;

    /// Disjoin a sequence of expressions into a single expression.
    /// Returns true if the sequence has no elements.
    fn disjoin(&mut self) -> Expr;
}

impl<T> ExprIterator for T
where
    T: Iterator<Item = Expr>,
{
    fn conjoin(&mut self) -> Expr {
        fn rfold<T>(s: &mut T) -> Expr
        where
            T: Iterator<Item = Expr>,
        {
            if let Some(conjunct) = s.next() {
                Expr::and(conjunct, rfold(s))
            } else {
                true.into()
            }
        }
        rfold(self)
    }

    fn disjoin(&mut self) -> Expr {
        fn rfold<T>(s: &mut T) -> Expr
        where
            T: Iterator<Item = Expr>,
        {
            if let Some(conjunct) = s.next() {
                Expr::or(conjunct, rfold(s))
            } else {
                false.into()
            }
        }
        rfold(self)
    }
}
