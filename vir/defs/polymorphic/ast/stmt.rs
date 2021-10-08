// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::super::{
    borrows::{Borrow, DAG as ReborrowingDAG},
    cfg::CfgBlockIndex,
};
use crate::polymorphic::ast::*;
use std::{collections::HashMap, fmt};

// TODO: Fix by boxing all `Expr`s.
#[allow(clippy::large_enum_variant)]
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
            self.targets
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.method_name,
            self.arguments
                .iter()
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
                write!(
                    f,
                    "{} := mut borrow {} // {:?}",
                    self.target, self.source, borrow
                )
            }
            AssignKind::SharedBorrow(borrow) => {
                write!(
                    f,
                    "{} := borrow {} // {:?}",
                    self.target, self.source, borrow
                )
            }
            AssignKind::Ghost => write!(f, "{} := ghost {}", self.target, self.source),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub struct Fold {
    pub predicate: Type,
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
                format!("{}<variant {}>", self.predicate, variant_index)
            } else {
                self.predicate.to_string()
            },
            self.arguments
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.permission,
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub struct Unfold {
    pub predicate: Type,
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
                format!("{}<variant {}>", self.predicate, variant_index)
            } else {
                self.predicate.to_string()
            },
            self.arguments
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.permission,
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Obtain {
    pub expr: Expr,
    pub position: Position,
}

impl fmt::Display for Obtain {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "obtain {}", self.expr)
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
            if magic_wand_expr.borrow.is_none() {
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
            writeln!(f)?;
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
                return writeln!(
                    f,
                    "apply[{:?}] {} --* {}",
                    magic_wand_expr.borrow.unwrap(),
                    magic_wand_expr.left,
                    magic_wand_expr.right
                );
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
                writeln!(f)?;
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

impl Stmt {
    pub fn is_comment(&self) -> bool {
        matches!(self, Stmt::Comment(_))
    }

    pub fn comment<S: ToString>(comment: S) -> Self {
        Stmt::Comment(Comment {
            comment: comment.to_string(),
        })
    }

    pub fn label<S: ToString>(label: S) -> Self {
        Stmt::Label(Label {
            label: label.to_string(),
        })
    }

    pub fn inhale(expr: Expr) -> Self {
        Stmt::Inhale(Inhale { expr })
    }

    pub fn package_magic_wand(
        lhs: Expr,
        rhs: Expr,
        stmts: Vec<Stmt>,
        label: String,
        vars: Vec<LocalVar>,
        pos: Position,
    ) -> Self {
        Stmt::PackageMagicWand(PackageMagicWand {
            magic_wand: Expr::MagicWand(MagicWand {
                left: Box::new(lhs),
                right: Box::new(rhs),
                borrow: None,
                position: pos,
            }),
            package_stmts: stmts,
            label,
            variables: vars,
            position: pos,
        })
    }

    pub fn apply_magic_wand(lhs: Expr, rhs: Expr, borrow: Borrow, pos: Position) -> Self {
        Stmt::ApplyMagicWand(ApplyMagicWand {
            magic_wand: Expr::magic_wand(lhs, rhs, Some(borrow)),
            position: pos,
        })
    }

    // TODO: Potentially add more variants based on how they are used in encoders
    pub fn pos(&self) -> Option<&Position> {
        match self {
            Stmt::PackageMagicWand(PackageMagicWand { position, .. }) => Some(position),
            Stmt::Exhale(Exhale { position, .. }) => Some(position),
            _ => None,
        }
    }

    // TODO: Potentially add more variants based on how they are used in encoders
    pub fn set_pos(self, position: Position) -> Self {
        match self {
            Stmt::PackageMagicWand(PackageMagicWand {
                magic_wand,
                package_stmts,
                label,
                variables,
                ..
            }) => Stmt::PackageMagicWand(PackageMagicWand {
                magic_wand,
                package_stmts,
                label,
                variables,
                position,
            }),
            Stmt::Exhale(Exhale { expr, .. }) => Stmt::Exhale(Exhale { expr, position }),
            x => x,
        }
    }

    // Replace a Position::default() position with `pos`
    pub fn set_default_pos(self, pos: Position) -> Self {
        if self.pos().iter().any(|x| x.is_default()) {
            self.set_pos(pos)
        } else {
            self
        }
    }

    // Replace all Position::default() positions in expressions with `pos`
    pub fn set_default_expr_pos(self, pos: Position) -> Self {
        self.map_expr(|e| e.set_default_pos(pos))
    }
}

pub trait StmtFolder {
    fn fold(&mut self, e: Stmt) -> Stmt {
        match e {
            Stmt::Comment(comment) => self.fold_comment(comment),
            Stmt::Label(label) => self.fold_label(label),
            Stmt::Inhale(inhale) => self.fold_inhale(inhale),
            Stmt::Exhale(exhale) => self.fold_exhale(exhale),
            Stmt::Assert(assert) => self.fold_assert(assert),
            Stmt::MethodCall(method_call) => self.fold_method_call(method_call),
            Stmt::Assign(assign) => self.fold_assign(assign),
            Stmt::Fold(fold) => self.fold_fold(fold),
            Stmt::Unfold(unfold) => self.fold_unfold(unfold),
            Stmt::Obtain(obtain) => self.fold_obtain(obtain),
            Stmt::BeginFrame(_) => self.fold_begin_frame(),
            Stmt::EndFrame(_) => self.fold_end_frame(),
            Stmt::TransferPerm(transfer_perm) => self.fold_transfer_perm(transfer_perm),
            Stmt::PackageMagicWand(package_magic_wand) => {
                self.fold_package_magic_wand(package_magic_wand)
            }
            Stmt::ApplyMagicWand(apply_magic_wand) => self.fold_apply_magic_wand(apply_magic_wand),
            Stmt::ExpireBorrows(expire_borrows) => self.fold_expire_borrows(expire_borrows),
            Stmt::If(if_stmt) => self.fold_if(if_stmt),
            Stmt::Downcast(downcast) => self.fold_downcast(downcast),
        }
    }

    fn fold_expr(&mut self, expr: Expr) -> Expr {
        expr
    }

    fn fold_comment(&mut self, comment: Comment) -> Stmt {
        Stmt::Comment(comment)
    }

    fn fold_label(&mut self, label: Label) -> Stmt {
        Stmt::Label(label)
    }

    fn fold_inhale(&mut self, statement: Inhale) -> Stmt {
        let Inhale { expr } = statement;
        Stmt::Inhale(Inhale {
            expr: self.fold_expr(expr),
        })
    }

    fn fold_exhale(&mut self, statement: Exhale) -> Stmt {
        let Exhale { expr, position } = statement;
        Stmt::Exhale(Exhale {
            expr: self.fold_expr(expr),
            position,
        })
    }

    fn fold_assert(&mut self, statement: Assert) -> Stmt {
        let Assert { expr, position } = statement;
        Stmt::Assert(Assert {
            expr: self.fold_expr(expr),
            position,
        })
    }

    fn fold_method_call(&mut self, statement: MethodCall) -> Stmt {
        let MethodCall {
            method_name,
            arguments,
            targets,
        } = statement;
        Stmt::MethodCall(MethodCall {
            method_name,
            arguments: arguments.into_iter().map(|e| self.fold_expr(e)).collect(),
            targets,
        })
    }

    fn fold_assign(&mut self, statement: Assign) -> Stmt {
        let Assign {
            target,
            source,
            kind,
        } = statement;
        Stmt::Assign(Assign {
            target: self.fold_expr(target),
            source: self.fold_expr(source),
            kind,
        })
    }
    fn fold_fold(&mut self, statement: Fold) -> Stmt {
        let Fold {
            predicate,
            arguments,
            permission,
            enum_variant,
            position,
        } = statement;
        Stmt::Fold(Fold {
            predicate,
            arguments: arguments.into_iter().map(|e| self.fold_expr(e)).collect(),
            permission,
            enum_variant,
            position,
        })
    }

    fn fold_unfold(&mut self, statement: Unfold) -> Stmt {
        let Unfold {
            predicate,
            arguments,
            permission,
            enum_variant,
        } = statement;
        Stmt::Unfold(Unfold {
            predicate,
            arguments: arguments.into_iter().map(|e| self.fold_expr(e)).collect(),
            permission,
            enum_variant,
        })
    }

    fn fold_obtain(&mut self, statement: Obtain) -> Stmt {
        let Obtain { expr, position } = statement;
        Stmt::Obtain(Obtain {
            expr: self.fold_expr(expr),
            position,
        })
    }

    fn fold_begin_frame(&mut self) -> Stmt {
        Stmt::BeginFrame(BeginFrame {})
    }

    fn fold_end_frame(&mut self) -> Stmt {
        Stmt::EndFrame(EndFrame {})
    }

    fn fold_transfer_perm(&mut self, statement: TransferPerm) -> Stmt {
        let TransferPerm {
            left,
            right,
            unchecked,
        } = statement;
        Stmt::TransferPerm(TransferPerm {
            left: self.fold_expr(left),
            right: self.fold_expr(right),
            unchecked,
        })
    }

    fn fold_package_magic_wand(&mut self, statement: PackageMagicWand) -> Stmt {
        let PackageMagicWand {
            magic_wand,
            package_stmts,
            label,
            variables,
            position,
        } = statement;
        Stmt::PackageMagicWand(PackageMagicWand {
            magic_wand: self.fold_expr(magic_wand),
            package_stmts: package_stmts.into_iter().map(|x| self.fold(x)).collect(),
            label,
            variables,
            position,
        })
    }

    fn fold_apply_magic_wand(&mut self, statement: ApplyMagicWand) -> Stmt {
        let ApplyMagicWand {
            magic_wand,
            position,
        } = statement;
        Stmt::ApplyMagicWand(ApplyMagicWand {
            magic_wand: self.fold_expr(magic_wand),
            position,
        })
    }

    fn fold_expire_borrows(&mut self, statement: ExpireBorrows) -> Stmt {
        let ExpireBorrows { dag } = statement;
        Stmt::ExpireBorrows(ExpireBorrows { dag })
    }

    fn fold_if(&mut self, statement: If) -> Stmt {
        let If {
            guard,
            then_stmts,
            else_stmts,
        } = statement;
        Stmt::If(If {
            guard: self.fold_expr(guard),
            then_stmts: then_stmts.into_iter().map(|x| self.fold(x)).collect(),
            else_stmts: else_stmts.into_iter().map(|x| self.fold(x)).collect(),
        })
    }

    fn fold_downcast(&mut self, statement: Downcast) -> Stmt {
        let Downcast { base, field } = statement;
        Stmt::Downcast(Downcast {
            base: self.fold_expr(base),
            field,
        })
    }
}

pub trait FallibleStmtFolder {
    type Error;

    fn fallible_fold(&mut self, e: Stmt) -> Result<Stmt, Self::Error> {
        match e {
            Stmt::Comment(comment) => self.fallible_fold_comment(comment),
            Stmt::Label(label) => self.fallible_fold_label(label),
            Stmt::Inhale(inhale) => self.fallible_fold_inhale(inhale),
            Stmt::Exhale(exhale) => self.fallible_fold_exhale(exhale),
            Stmt::Assert(assert) => self.fallible_fold_assert(assert),
            Stmt::MethodCall(method_call) => self.fallible_fold_method_call(method_call),
            Stmt::Assign(assign) => self.fallible_fold_assign(assign),
            Stmt::Fold(fold) => self.fallible_fold_fold(fold),
            Stmt::Unfold(unfold) => self.fallible_fold_unfold(unfold),
            Stmt::Obtain(obtain) => self.fallible_fold_obtain(obtain),
            Stmt::BeginFrame(_) => self.fallible_fold_begin_frame(),
            Stmt::EndFrame(_) => self.fallible_fold_end_frame(),
            Stmt::TransferPerm(transfer_perm) => self.fallible_fold_transfer_perm(transfer_perm),
            Stmt::PackageMagicWand(package_magic_wand) => {
                self.fallible_fold_package_magic_wand(package_magic_wand)
            }
            Stmt::ApplyMagicWand(apply_magic_wand) => {
                self.fallible_fold_apply_magic_wand(apply_magic_wand)
            }
            Stmt::ExpireBorrows(expire_borrows) => {
                self.fallible_fold_expire_borrows(expire_borrows)
            }
            Stmt::If(if_stmt) => self.fallible_fold_if(if_stmt),
            Stmt::Downcast(downcast) => self.fallible_fold_downcast(downcast),
        }
    }

    fn fallible_fold_expr(&mut self, expr: Expr) -> Result<Expr, Self::Error> {
        Ok(expr)
    }

    fn fallible_fold_comment(&mut self, comment: Comment) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Comment(comment))
    }

    fn fallible_fold_label(&mut self, label: Label) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Label(label))
    }

    fn fallible_fold_inhale(&mut self, statement: Inhale) -> Result<Stmt, Self::Error> {
        let Inhale { expr } = statement;
        Ok(Stmt::Inhale(Inhale {
            expr: self.fallible_fold_expr(expr)?,
        }))
    }

    fn fallible_fold_exhale(&mut self, statement: Exhale) -> Result<Stmt, Self::Error> {
        let Exhale { expr, position } = statement;
        Ok(Stmt::Exhale(Exhale {
            expr: self.fallible_fold_expr(expr)?,
            position,
        }))
    }

    fn fallible_fold_assert(&mut self, statement: Assert) -> Result<Stmt, Self::Error> {
        let Assert { expr, position } = statement;
        Ok(Stmt::Assert(Assert {
            expr: self.fallible_fold_expr(expr)?,
            position,
        }))
    }

    fn fallible_fold_method_call(&mut self, statement: MethodCall) -> Result<Stmt, Self::Error> {
        let MethodCall {
            method_name,
            arguments,
            targets,
        } = statement;
        Ok(Stmt::MethodCall(MethodCall {
            method_name,
            arguments: arguments
                .into_iter()
                .map(|e| self.fallible_fold_expr(e))
                .collect::<Result<_, _>>()?,
            targets,
        }))
    }

    fn fallible_fold_assign(&mut self, statement: Assign) -> Result<Stmt, Self::Error> {
        let Assign {
            target,
            source,
            kind,
        } = statement;
        Ok(Stmt::Assign(Assign {
            target: self.fallible_fold_expr(target)?,
            source: self.fallible_fold_expr(source)?,
            kind,
        }))
    }

    fn fallible_fold_fold(&mut self, statement: Fold) -> Result<Stmt, Self::Error> {
        let Fold {
            predicate,
            arguments,
            permission,
            enum_variant,
            position,
        } = statement;
        Ok(Stmt::Fold(Fold {
            predicate,
            arguments: arguments
                .into_iter()
                .map(|e| self.fallible_fold_expr(e))
                .collect::<Result<_, _>>()?,
            permission,
            enum_variant,
            position,
        }))
    }

    fn fallible_fold_unfold(&mut self, statement: Unfold) -> Result<Stmt, Self::Error> {
        let Unfold {
            predicate,
            arguments,
            permission,
            enum_variant,
        } = statement;
        Ok(Stmt::Unfold(Unfold {
            predicate,
            arguments: arguments
                .into_iter()
                .map(|e| self.fallible_fold_expr(e))
                .collect::<Result<_, _>>()?,
            permission,
            enum_variant,
        }))
    }

    fn fallible_fold_obtain(&mut self, statement: Obtain) -> Result<Stmt, Self::Error> {
        let Obtain { expr, position } = statement;
        Ok(Stmt::Obtain(Obtain {
            expr: self.fallible_fold_expr(expr)?,
            position,
        }))
    }

    fn fallible_fold_begin_frame(&mut self) -> Result<Stmt, Self::Error> {
        Ok(Stmt::BeginFrame(BeginFrame {}))
    }

    fn fallible_fold_end_frame(&mut self) -> Result<Stmt, Self::Error> {
        Ok(Stmt::EndFrame(EndFrame {}))
    }

    fn fallible_fold_transfer_perm(
        &mut self,
        statement: TransferPerm,
    ) -> Result<Stmt, Self::Error> {
        let TransferPerm {
            left,
            right,
            unchecked,
        } = statement;
        Ok(Stmt::TransferPerm(TransferPerm {
            left: self.fallible_fold_expr(left)?,
            right: self.fallible_fold_expr(right)?,
            unchecked,
        }))
    }

    fn fallible_fold_package_magic_wand(
        &mut self,
        statement: PackageMagicWand,
    ) -> Result<Stmt, Self::Error> {
        let PackageMagicWand {
            magic_wand,
            package_stmts,
            label,
            variables,
            position,
        } = statement;
        Ok(Stmt::PackageMagicWand(PackageMagicWand {
            magic_wand: self.fallible_fold_expr(magic_wand)?,
            package_stmts: package_stmts
                .into_iter()
                .map(|x| self.fallible_fold(x))
                .collect::<Result<_, _>>()?,
            label,
            variables,
            position,
        }))
    }

    fn fallible_fold_apply_magic_wand(
        &mut self,
        statement: ApplyMagicWand,
    ) -> Result<Stmt, Self::Error> {
        let ApplyMagicWand {
            magic_wand,
            position,
        } = statement;
        Ok(Stmt::ApplyMagicWand(ApplyMagicWand {
            magic_wand: self.fallible_fold_expr(magic_wand)?,
            position,
        }))
    }

    fn fallible_fold_expire_borrows(
        &mut self,
        statement: ExpireBorrows,
    ) -> Result<Stmt, Self::Error> {
        let ExpireBorrows { dag } = statement;
        Ok(Stmt::ExpireBorrows(ExpireBorrows { dag }))
    }

    fn fallible_fold_if(&mut self, statement: If) -> Result<Stmt, Self::Error> {
        let If {
            guard,
            then_stmts,
            else_stmts,
        } = statement;
        Ok(Stmt::If(If {
            guard: self.fallible_fold_expr(guard)?,
            then_stmts: then_stmts
                .into_iter()
                .map(|x| self.fallible_fold(x))
                .collect::<Result<_, _>>()?,
            else_stmts: else_stmts
                .into_iter()
                .map(|x| self.fallible_fold(x))
                .collect::<Result<_, _>>()?,
        }))
    }

    fn fallible_fold_downcast(&mut self, statement: Downcast) -> Result<Stmt, Self::Error> {
        let Downcast { base, field } = statement;
        Ok(Stmt::Downcast(Downcast {
            base: self.fallible_fold_expr(base)?,
            field,
        }))
    }
}

pub trait StmtWalker {
    fn walk(&mut self, e: &Stmt) {
        match e {
            Stmt::Comment(comment) => self.walk_comment(comment),
            Stmt::Label(label) => self.walk_label(label),
            Stmt::Inhale(inhale) => self.walk_inhale(inhale),
            Stmt::Exhale(exhale) => self.walk_exhale(exhale),
            Stmt::Assert(assert) => self.walk_assert(assert),
            Stmt::MethodCall(method_call) => self.walk_method_call(method_call),
            Stmt::Assign(assign) => self.walk_assign(assign),
            Stmt::Fold(fold) => self.walk_fold(fold),
            Stmt::Unfold(unfold) => self.walk_unfold(unfold),
            Stmt::Obtain(obtain) => self.walk_obtain(obtain),
            Stmt::BeginFrame(_) => self.walk_begin_frame(),
            Stmt::EndFrame(_) => self.walk_end_frame(),
            Stmt::TransferPerm(transfer_perm) => self.walk_transfer_perm(transfer_perm),
            Stmt::PackageMagicWand(package_magic_wand) => {
                self.walk_package_magic_wand(package_magic_wand)
            }
            Stmt::ApplyMagicWand(apply_magic_wand) => self.walk_apply_magic_wand(apply_magic_wand),
            Stmt::ExpireBorrows(expire_borrows) => self.walk_expire_borrows(expire_borrows),
            Stmt::If(if_stmt) => self.walk_if(if_stmt),
            Stmt::Downcast(downcast) => self.walk_downcast(downcast),
        }
    }

    fn walk_expr(&mut self, _expr: &Expr) {}

    fn walk_local_var(&mut self, _local_var: &LocalVar) {}

    fn walk_comment(&mut self, _comment: &Comment) {}

    fn walk_label(&mut self, _label: &Label) {}

    fn walk_inhale(&mut self, statement: &Inhale) {
        let Inhale { expr } = statement;
        self.walk_expr(expr);
    }

    fn walk_exhale(&mut self, statement: &Exhale) {
        let Exhale { expr, .. } = statement;
        self.walk_expr(expr);
    }

    fn walk_assert(&mut self, statement: &Assert) {
        let Assert { expr, .. } = statement;
        self.walk_expr(expr);
    }

    fn walk_method_call(&mut self, statement: &MethodCall) {
        let MethodCall {
            arguments, targets, ..
        } = statement;
        for arg in arguments {
            self.walk_expr(arg);
        }
        for target in targets {
            self.walk_local_var(target);
        }
    }

    fn walk_assign(&mut self, statement: &Assign) {
        let Assign { target, source, .. } = statement;
        self.walk_expr(target);
        self.walk_expr(source);
    }

    fn walk_fold(&mut self, statement: &Fold) {
        let Fold { arguments, .. } = statement;
        for arg in arguments {
            self.walk_expr(arg);
        }
    }

    fn walk_unfold(&mut self, statement: &Unfold) {
        let Unfold { arguments, .. } = statement;
        for arg in arguments {
            self.walk_expr(arg);
        }
    }

    fn walk_obtain(&mut self, statement: &Obtain) {
        let Obtain { expr, .. } = statement;
        self.walk_expr(expr);
    }

    fn walk_weak_obtain(&mut self, expr: &Expr) {
        self.walk_expr(expr);
    }

    fn walk_havoc(&mut self) {}

    fn walk_begin_frame(&mut self) {}

    fn walk_end_frame(&mut self) {}

    fn walk_transfer_perm(&mut self, statement: &TransferPerm) {
        let TransferPerm { left, right, .. } = statement;
        self.walk_expr(left);
        self.walk_expr(right);
    }

    fn walk_package_magic_wand(&mut self, statement: &PackageMagicWand) {
        let PackageMagicWand {
            magic_wand,
            package_stmts,
            variables,
            ..
        } = statement;
        self.walk_expr(magic_wand);
        for var in variables {
            self.walk_local_var(var);
        }
        for statement in package_stmts {
            self.walk(statement);
        }
    }

    fn walk_apply_magic_wand(&mut self, statement: &ApplyMagicWand) {
        let ApplyMagicWand { magic_wand, .. } = statement;
        self.walk_expr(magic_wand);
    }

    fn walk_expire_borrows(&mut self, _expire_borrows: &ExpireBorrows) {}

    fn walk_nested_cfg(&mut self, _entry: &CfgBlockIndex, _exit: &CfgBlockIndex) {}

    fn walk_if(&mut self, statement: &If) {
        let If {
            guard,
            then_stmts,
            else_stmts,
        } = statement;
        self.walk_expr(guard);
        for s in then_stmts {
            self.walk(s);
        }
        for s in else_stmts {
            self.walk(s);
        }
    }

    fn walk_downcast(&mut self, statement: &Downcast) {
        let Downcast { base, .. } = statement;
        self.walk_expr(base);
    }
}

pub trait FallibleStmtWalker {
    type Error;

    fn fallible_walk(&mut self, e: &Stmt) -> Result<(), Self::Error> {
        match e {
            Stmt::Comment(comment) => self.fallible_walk_comment(comment),
            Stmt::Label(label) => self.fallible_walk_label(label),
            Stmt::Inhale(inhale) => self.fallible_walk_inhale(inhale),
            Stmt::Exhale(exhale) => self.fallible_walk_exhale(exhale),
            Stmt::Assert(assert) => self.fallible_walk_assert(assert),
            Stmt::MethodCall(method_call) => self.fallible_walk_method_call(method_call),
            Stmt::Assign(assign) => self.fallible_walk_assign(assign),
            Stmt::Fold(fold) => self.fallible_walk_fold(fold),
            Stmt::Unfold(unfold) => self.fallible_walk_unfold(unfold),
            Stmt::Obtain(obtain) => self.fallible_walk_obtain(obtain),
            Stmt::BeginFrame(_) => self.fallible_walk_begin_frame(),
            Stmt::EndFrame(_) => self.fallible_walk_end_frame(),
            Stmt::TransferPerm(transfer_perm) => self.fallible_walk_transfer_perm(transfer_perm),
            Stmt::PackageMagicWand(package_magic_wand) => {
                self.fallible_walk_package_magic_wand(package_magic_wand)
            }
            Stmt::ApplyMagicWand(apply_magic_wand) => {
                self.fallible_walk_apply_magic_wand(apply_magic_wand)
            }
            Stmt::ExpireBorrows(expire_borrows) => {
                self.fallible_walk_expire_borrows(expire_borrows)
            }
            Stmt::If(if_stmt) => self.fallible_walk_if(if_stmt),
            Stmt::Downcast(downcast) => self.fallible_walk_downcast(downcast),
        }
    }

    fn fallible_walk_expr(&mut self, _expr: &Expr) -> Result<(), Self::Error> {
        Ok(())
    }

    fn fallible_walk_local_var(&mut self, _local_var: &LocalVar) -> Result<(), Self::Error> {
        Ok(())
    }

    fn fallible_walk_comment(&mut self, _comment: &Comment) -> Result<(), Self::Error> {
        Ok(())
    }

    fn fallible_walk_label(&mut self, _label: &Label) -> Result<(), Self::Error> {
        Ok(())
    }

    fn fallible_walk_inhale(&mut self, statement: &Inhale) -> Result<(), Self::Error> {
        let Inhale { expr } = statement;
        self.fallible_walk_expr(expr)?;
        Ok(())
    }

    fn fallible_walk_exhale(&mut self, statement: &Exhale) -> Result<(), Self::Error> {
        let Exhale { expr, .. } = statement;
        self.fallible_walk_expr(expr)?;
        Ok(())
    }

    fn fallible_walk_assert(&mut self, statement: &Assert) -> Result<(), Self::Error> {
        let Assert { expr, .. } = statement;
        self.fallible_walk_expr(expr)?;
        Ok(())
    }

    fn fallible_walk_method_call(&mut self, statement: &MethodCall) -> Result<(), Self::Error> {
        let MethodCall {
            arguments, targets, ..
        } = statement;
        for arg in arguments {
            self.fallible_walk_expr(arg)?;
        }
        for target in targets {
            self.fallible_walk_local_var(target)?;
        }
        Ok(())
    }

    fn fallible_walk_assign(&mut self, statement: &Assign) -> Result<(), Self::Error> {
        let Assign { target, source, .. } = statement;
        self.fallible_walk_expr(target)?;
        self.fallible_walk_expr(source)?;
        Ok(())
    }

    fn fallible_walk_fold(&mut self, statement: &Fold) -> Result<(), Self::Error> {
        let Fold { arguments, .. } = statement;
        for arg in arguments {
            self.fallible_walk_expr(arg)?;
        }
        Ok(())
    }

    fn fallible_walk_unfold(&mut self, statement: &Unfold) -> Result<(), Self::Error> {
        let Unfold { arguments, .. } = statement;
        for arg in arguments {
            self.fallible_walk_expr(arg)?;
        }
        Ok(())
    }

    fn fallible_walk_obtain(&mut self, statement: &Obtain) -> Result<(), Self::Error> {
        let Obtain { expr, .. } = statement;
        self.fallible_walk_expr(expr)?;
        Ok(())
    }

    fn fallible_walk_weak_obtain(&mut self, expr: &Expr) -> Result<(), Self::Error> {
        self.fallible_walk_expr(expr)?;
        Ok(())
    }

    fn fallible_walk_havoc(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn fallible_walk_begin_frame(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn fallible_walk_end_frame(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn fallible_walk_transfer_perm(&mut self, statement: &TransferPerm) -> Result<(), Self::Error> {
        let TransferPerm { left, right, .. } = statement;
        self.fallible_walk_expr(left)?;
        self.fallible_walk_expr(right)?;
        Ok(())
    }

    fn fallible_walk_package_magic_wand(
        &mut self,
        statement: &PackageMagicWand,
    ) -> Result<(), Self::Error> {
        let PackageMagicWand {
            magic_wand,
            package_stmts,
            variables,
            ..
        } = statement;
        self.fallible_walk_expr(magic_wand)?;
        for var in variables {
            self.fallible_walk_local_var(var)?;
        }
        for statement in package_stmts {
            self.fallible_walk(statement)?;
        }
        Ok(())
    }

    fn fallible_walk_apply_magic_wand(
        &mut self,
        statement: &ApplyMagicWand,
    ) -> Result<(), Self::Error> {
        let ApplyMagicWand { magic_wand, .. } = statement;
        self.fallible_walk_expr(magic_wand)?;
        Ok(())
    }

    fn fallible_walk_expire_borrows(
        &mut self,
        _expire_borrows: &ExpireBorrows,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn fallible_walk_nested_cfg(
        &mut self,
        _entry: &CfgBlockIndex,
        _exit: &CfgBlockIndex,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn fallible_walk_if(&mut self, statement: &If) -> Result<(), Self::Error> {
        let If {
            guard,
            then_stmts,
            else_stmts,
        } = statement;
        self.fallible_walk_expr(guard)?;
        for s in then_stmts {
            self.fallible_walk(s)?;
        }
        for s in else_stmts {
            self.fallible_walk(s)?;
        }
        Ok(())
    }

    fn fallible_walk_downcast(&mut self, statement: &Downcast) -> Result<(), Self::Error> {
        let Downcast { base, .. } = statement;
        self.fallible_walk_expr(base)?;
        Ok(())
    }
}

pub fn stmts_to_str(stmts: &[Stmt]) -> String {
    stmts
        .iter()
        .map(|stmt| format!("{}\n", stmt))
        .collect::<String>()
}
