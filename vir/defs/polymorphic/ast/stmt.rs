// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::super::borrows::{Borrow, DAG as ReborrowingDAG};
use super::super::cfg::CfgBlockIndex;
use crate::polymorphic::ast::*;
use std::fmt;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Stmt {
    Comment(Comment),
    Label(Label),
    Inhale(Inhale),
    Exhale(Exhale),
    Assert(Assert),
    /// MethodCall: method_name, args, targets
    MethodCall(MethodCall),
    /// Target, source, kind
    Assign(Assign),
    /// Fold statement: predicate name, predicate args, perm_amount, variant of enum, position.
    Fold(Fold),
    /// Unfold statement: predicate name, predicate args, perm_amount, variant of enum.
    Unfold(Unfold),
    /// Obtain: conjunction of Expr::PredicateAccessPredicate or Expr::FieldAccessPredicate
    /// They will be used by the fold/unfold algorithm
    Obtain(Obtain),
    /// Mark a CFG point in which all current permissions are framed out
    /// They will be used by the fold/unfold algorithm
    BeginFrame(BeginFrame),
    /// Mark a CFG point in which all the permissions of a corresponding `BeginFrame` are framed in
    /// They will be used by the fold/unfold algorithm
    EndFrame(EndFrame),
    /// Move permissions from a place to another.
    /// This is used to restore permissions in the fold/unfold state when a loan expires.
    ///
    /// The last argument indicates if the transfer is unchecked. Unchecked transfer is used for
    /// encoding shared borrows which can be dangling and, therefore, we cannot use the safety
    /// checks.
    TransferPerm(TransferPerm),
    /// Package a Magic Wand
    /// Arguments: the magic wand, the package statement's body, the
    /// label just before the statement, and ghost variables used inside
    /// the package statement.
    PackageMagicWand(PackageMagicWand),
    /// Apply a Magic Wand.
    /// Arguments: the magic wand.
    ApplyMagicWand(ApplyMagicWand),
    /// Expire borrows given in the reborrowing DAG.
    ExpireBorrows(ExpireBorrows),
    /// An `if` statement: the guard and the 'then' branch.
    If(If),
    /// Inform the fold-unfold algorithm that at this program point a enum type can be downcasted
    /// to one of its variants. This statement is a no-op for Viper.
    /// Arguments:
    /// * place to the enumeration instance
    /// * field that encodes the variant
    Downcast(Downcast),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Stmt::Comment(comment) => comment.fmt(f),
            Stmt::Label(label) => label.fmt(f),
            Stmt::Inhale(inhale) => inhale.fmt(f),
            Stmt::Exhale(exhale) => exhale.fmt(f),
            Stmt::Assert(assert) => assert.fmt(f),
            Stmt::MethodCall(method_call) => method_call.fmt(f),
            Stmt::Assign(assign) => assign.fmt(f),
            Stmt::Fold(fold) => fold.fmt(f),
            Stmt::Unfold(unfold) => unfold.fmt(f),
            Stmt::Obtain(obtain) => obtain.fmt(f),
            Stmt::BeginFrame(begin_frame) => begin_frame.fmt(f),
            Stmt::EndFrame(end_frame) => end_frame.fmt(f),
            Stmt::TransferPerm(transfer_perm) => transfer_perm.fmt(f),
            Stmt::PackageMagicWand(package_magic_wand) => package_magic_wand.fmt(f),
            Stmt::ApplyMagicWand(apply_magic_wand) => apply_magic_wand.fmt(f),
            Stmt::ExpireBorrows(expire_borrows) => expire_borrows.fmt(f),
            Stmt::If(if_stmt) => if_stmt.fmt(f),
            Stmt::Downcast(downcast) => downcast.fmt(f),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AssignKind {
    /// Encodes a Rust copy.
    /// This assignment can be used iff the Viper type of the `lhs` and `rhs` is *not* Ref.
    Copy,
    /// Encodes a Rust move. The permissions in the rhs move to the `lhs`.
    /// This assignment can be used iff the Viper type of the `lhs` and `rhs` is Ref.
    Move,
    /// Encodes the initialization of a mutable borrow.
    /// The permissions in the `rhs` move to the `lhs`, but they can be restored when the borrow dies.
    MutableBorrow(Borrow),
    /// Encodes the initialization of a shared borrow.
    /// The permissions in the `rhs` are duplicated to the `lhs`.
    SharedBorrow(Borrow),
    /// Used to mark that the assignment is to a ghost variable and should be ignored by
    /// the fold-unfold algorithm.
    Ghost,
}

/// Individual structs for different cases of Expr
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Comment {
    pub comment: String,
}

impl fmt::Display for Comment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "// {}", self.comment)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Label {
    pub label: String,
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "label {}", self.label)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Inhale {
    pub expr: Expr,
}

impl fmt::Display for Inhale {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "inhale {}", self.expr)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Exhale {
    pub expr: Expr,
    pub position: Position,
}

impl fmt::Display for Exhale {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "exhale {}", self.expr)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Assert {
    pub expr: Expr,
    pub position: Position,
}

impl fmt::Display for Assert {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "assert {}", self.expr)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MethodCall {
    pub method_name: String,
    pub arguments: Vec<Expr>,
    pub targets: Vec<LocalVar>,
}

impl fmt::Display for MethodCall {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} := {}({})",
            self.targets.iter()
                .map(|f| f.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.method_name,
            self.arguments.iter()
                .map(|f| f.to_string())
                .collect::<Vec<String>>()
                .join(", "),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Assign {
    pub target: Expr,
    pub source: Expr,
    pub kind: AssignKind,
}

impl fmt::Display for Assign {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            AssignKind::Move => write!(f, "{} := move {}", self.target, self.source),
            AssignKind::Copy => write!(f, "{} := copy {}", self.target, self.source),
            AssignKind::MutableBorrow(borrow) => {
                write!(f, "{} := mut borrow {} // {:?}", self.target, self.source, borrow)
            }
            AssignKind::SharedBorrow(borrow) => {
                write!(f, "{} := borrow {} // {:?}", self.target, self.source, borrow)
            }
            AssignKind::Ghost => write!(f, "{} := ghost {}", self.target, self.source),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Fold {
    pub predicate_name: String,
    pub arguments: Vec<Expr>,
    pub permission: PermAmount,
    pub enum_variant: MaybeEnumVariantIndex,
    pub position: Position,
}

impl fmt::Display for Fold {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "fold acc({}({}), {})",
            if let Some(variant_index) = &self.enum_variant {
                format!("{}<variant {}>", self.predicate_name, variant_index)
            } else {
                format!("{}", self.predicate_name)
            },
            self.arguments.iter()
                .map(|f| f.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.permission,
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Unfold {
    pub predicate_name: String,
    pub arguments: Vec<Expr>,
    pub permission: PermAmount,
    pub enum_variant: MaybeEnumVariantIndex,
}

impl fmt::Display for Unfold {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "unfold acc({}({}), {})",
            if let Some(variant_index) = &self.enum_variant {
                format!("{}<variant {}>", self.predicate_name, variant_index)
            } else {
                format!("{}", self.predicate_name)
            },
            self.arguments.iter()
                .map(|f| f.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.permission,
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Obtain {
    pub predicate_name: Expr,
    pub position: Position,
}

impl fmt::Display for Obtain {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "obtain {}", self.predicate_name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BeginFrame {}

impl fmt::Display for BeginFrame {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "begin frame")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EndFrame {}

impl fmt::Display for EndFrame {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "end frame")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransferPerm {
    pub left: Expr,
    pub right: Expr,
    pub unchecked: bool,
}

impl fmt::Display for TransferPerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "transfer perm {} --> {} // unchecked: {}",
            self.left, self.right, self.unchecked
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PackageMagicWand {
    pub magic_wand: Expr,
    pub package_stmts: Vec<Stmt>,
    pub label: String,
    pub variables: Vec<LocalVar>,
    pub position: Position,
}

impl fmt::Display for PackageMagicWand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Expr::MagicWand(magic_wand_expr) = &self.magic_wand {
            if !magic_wand_expr.borrow.is_some() {
                writeln!(f, "package[{}] {}", self.label, magic_wand_expr.left)?;
                writeln!(f, "    --* {}", magic_wand_expr.right)?;
            } else {
                writeln!(f, "package[{}] {}", self.label, self.magic_wand)?;    
            }
        } else {
            writeln!(f, "package[{}] {}", self.label, self.magic_wand)?;
        }
        write!(f, "{{")?;
        if !self.package_stmts.is_empty() {
            write!(f, "\n")?;
        }
        for stmt in self.package_stmts.iter() {
            writeln!(f, "    {}", stmt.to_string().replace("\n", "\n    "))?;
        }
        write!(f, "}}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ApplyMagicWand {
    pub magic_wand: Expr,
    pub position: Position,
}

impl fmt::Display for ApplyMagicWand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Expr::MagicWand(magic_wand_expr) = &self.magic_wand {
            if magic_wand_expr.borrow.is_some() {
                return writeln!(f, "apply[{:?}] {} --* {}", magic_wand_expr.borrow.unwrap(), magic_wand_expr.left, magic_wand_expr.right);
            }
        }
        writeln!(f, "apply {}", self.magic_wand)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpireBorrows {
    pub dag: ReborrowingDAG,
}

impl fmt::Display for ExpireBorrows {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "expire_borrows {:?}", self.dag)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct If {
    pub guard: Expr,
    pub then_stmts: Vec<Stmt>,
    pub else_stmts: Vec<Stmt>,
}

impl fmt::Display for If {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn write_stmt(f: &mut fmt::Formatter, stmt: &Stmt) -> fmt::Result {
            writeln!(f, "    {}", stmt.to_string().replace("\n", "\n    "))
        }
        fn write_block(f: &mut fmt::Formatter, stmts: &[Stmt]) -> fmt::Result {
            write!(f, "{{")?;
            if !stmts.is_empty() {
                write!(f, "\n")?;
            }
            for stmt in stmts.iter() {
                write_stmt(f, stmt)?;
            }
            write!(f, "}}")
        }
        write!(f, "if {} ", self.guard)?;
        write_block(f, &self.then_stmts)?;
        write!(f, " else ")?;
        write_block(f, &self.else_stmts)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Downcast {
    pub base: Expr,
    pub field: Field,
}

impl fmt::Display for Downcast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "downcast {} to {}", self.base, self.field)
    }
}
