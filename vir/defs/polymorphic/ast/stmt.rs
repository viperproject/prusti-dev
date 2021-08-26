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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
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

impl Stmt {
    pub fn is_comment(&self) -> bool {
        match self {
            Stmt::Comment(_) => true,
            _ => false,
        }
    }

    pub fn comment<S: ToString>(comment: S) -> Self {
        Stmt::Comment( Comment {
            comment: comment.to_string(),
        })
    }

    pub fn label<S: ToString>(label: S) -> Self {
        Stmt::Label( Label {
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
        Stmt::PackageMagicWand( PackageMagicWand {
            magic_wand: Expr::MagicWand( MagicWand {
                left: Box::new(lhs),
                right: Box::new(rhs),
                borrow: None,
                position: pos,
            }),
            package_stmts: stmts,
            label: label,
            variables: vars,
            position: pos,
        })
    }

    pub fn apply_magic_wand(lhs: Expr, rhs: Expr, borrow: Borrow, pos: Position) -> Self {
        Stmt::ApplyMagicWand( ApplyMagicWand {
            magic_wand: Expr::magic_wand(lhs, rhs, Some(borrow)),
            position: pos,
        })
    }

    // TODO: Potentially add more variants based on how they are used in encoders
    pub fn pos(&self) -> Option<&Position> {
        match self {
            Stmt::PackageMagicWand( PackageMagicWand {position, ..} ) => Some(position),
            Stmt::Exhale( Exhale {position, ..} ) => Some(position),
            _ => None,
        }
    }

        // TODO: Potentially add more variants based on how they are used in encoders
    pub fn set_pos(self, position: Position) -> Self {
        match self {
            Stmt::PackageMagicWand( PackageMagicWand {magic_wand, package_stmts, label, variables, ..} ) => {
                Stmt::PackageMagicWand( PackageMagicWand {magic_wand, package_stmts, label, variables, position} )
            }
            Stmt::Exhale( Exhale {expr, ..} ) => Stmt::Exhale( Exhale {expr, position} ),
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
            Stmt::Comment( Comment {comment} ) => self.fold_comment(comment),
            Stmt::Label( Label {label} ) => self.fold_label(label),
            Stmt::Inhale( Inhale {expr} ) => self.fold_inhale(expr),
            Stmt::Exhale( Exhale {expr, position} ) => self.fold_exhale(expr, position),
            Stmt::Assert( Assert {expr, position} ) => self.fold_assert(expr, position),
            Stmt::MethodCall( MethodCall {method_name, arguments, targets} ) => self.fold_method_call(method_name, arguments, targets),
            Stmt::Assign( Assign {target, source, kind} ) => self.fold_assign(target, source, kind),
            Stmt::Fold( Fold {predicate_name, arguments, permission, enum_variant, position} ) => self.fold_fold(predicate_name, arguments, permission, enum_variant, position),
            Stmt::Unfold( Unfold {predicate_name, arguments, permission, enum_variant} ) => self.fold_unfold(predicate_name, arguments, permission, enum_variant),
            Stmt::Obtain( Obtain {expr, position} ) => self.fold_obtain(expr, position),
            Stmt::BeginFrame(_) => self.fold_begin_frame(),
            Stmt::EndFrame(_) => self.fold_end_frame(),
            Stmt::TransferPerm( TransferPerm {left, right, unchecked} ) => self.fold_transfer_perm(left, right, unchecked),
            Stmt::PackageMagicWand( PackageMagicWand {magic_wand, package_stmts, label, variables, position} ) => self.fold_package_magic_wand(magic_wand, package_stmts, label, variables, position),
            Stmt::ApplyMagicWand( ApplyMagicWand {magic_wand, position} ) => self.fold_apply_magic_wand(magic_wand, position),
            Stmt::ExpireBorrows( ExpireBorrows {dag} ) => self.fold_expire_borrows(dag),
            Stmt::If( If {guard, then_stmts, else_stmts} ) => self.fold_if(guard, then_stmts, else_stmts),
            Stmt::Downcast( Downcast {base, field} ) => self.fold_downcast(base, field),
        }
    }

    fn fold_expr(&mut self, expr: Expr) -> Expr {
        expr
    }

    fn fold_comment(&mut self, comment: String) -> Stmt {
        Stmt::Comment( Comment {comment} )
    }

    fn fold_label(&mut self, label: String) -> Stmt {
        Stmt::Label( Label {label} )
    }

    fn fold_inhale(&mut self, expr: Expr) -> Stmt {
        Stmt::Inhale( Inhale {expr: self.fold_expr(expr)} )
    }

    fn fold_exhale(&mut self, e: Expr, position: Position) -> Stmt {
        Stmt::Exhale( Exhale {expr: self.fold_expr(e), position} )
    }

    fn fold_assert(&mut self, expr: Expr, position: Position) -> Stmt {
        Stmt::Assert( Assert {expr: self.fold_expr(expr), position} )
    }

    fn fold_method_call(&mut self, method_name: String, args: Vec<Expr>, targets: Vec<LocalVar>) -> Stmt {
        Stmt::MethodCall( MethodCall {
            method_name,
            arguments: args.into_iter().map(|e| self.fold_expr(e)).collect(),
            targets,
        })
    }

    fn fold_assign(&mut self, p: Expr, e: Expr, kind: AssignKind) -> Stmt {
        Stmt::Assign( Assign {
            target: self.fold_expr(p),
            source: self.fold_expr(e),
            kind,
        })
    }

    fn fold_fold(
        &mut self,
        predicate_name: String,
        args: Vec<Expr>,
        perm_amount: PermAmount,
        variant: MaybeEnumVariantIndex,
        position: Position,
    ) -> Stmt {
        Stmt::Fold( Fold {
            predicate_name,
            arguments: args.into_iter().map(|e| self.fold_expr(e)).collect(),
            permission: perm_amount,
            enum_variant: variant,
            position,
        })
    }

    fn fold_unfold(
        &mut self,
        predicate_name: String,
        args: Vec<Expr>,
        perm_amount: PermAmount,
        variant: MaybeEnumVariantIndex,
    ) -> Stmt {
        Stmt::Unfold( Unfold {
            predicate_name,
            arguments: args.into_iter().map(|e| self.fold_expr(e)).collect(),
            permission: perm_amount,
            enum_variant: variant,
        })
    }

    fn fold_obtain(&mut self, e: Expr, position: Position) -> Stmt {
        Stmt::Obtain( Obtain {expr: self.fold_expr(e), position} )
    }

    fn fold_begin_frame(&mut self) -> Stmt {
        Stmt::BeginFrame( BeginFrame {} )
    }

    fn fold_end_frame(&mut self) -> Stmt {
        Stmt::EndFrame( EndFrame {} )
    }

    fn fold_transfer_perm(&mut self, a: Expr, b: Expr, unchecked: bool) -> Stmt {
        Stmt::TransferPerm( TransferPerm {
            left: self.fold_expr(a),
            right: self.fold_expr(b),
            unchecked,
        })
    }

    fn fold_package_magic_wand(
        &mut self,
        wand: Expr,
        body: Vec<Stmt>,
        label: String,
        vars: Vec<LocalVar>,
        position: Position,
    ) -> Stmt {
        Stmt::PackageMagicWand( PackageMagicWand {
            magic_wand: self.fold_expr(wand),
            package_stmts: body.into_iter().map(|x| self.fold(x)).collect(),
            label,
            variables: vars,
            position,
        })
    }

    fn fold_apply_magic_wand(&mut self, w: Expr, position: Position) -> Stmt {
        Stmt::ApplyMagicWand( ApplyMagicWand {
            magic_wand: self.fold_expr(w),
            position,
        })
    }

    fn fold_expire_borrows(&mut self, dag: ReborrowingDAG) -> Stmt {
        Stmt::ExpireBorrows( ExpireBorrows {dag} )
    }

    fn fold_if(&mut self, g: Expr, t: Vec<Stmt>, e: Vec<Stmt>) -> Stmt {
        Stmt::If( If {
            guard: self.fold_expr(g),
            then_stmts: t.into_iter().map(|x| self.fold(x)).collect(),
            else_stmts: e.into_iter().map(|x| self.fold(x)).collect(),
        })
    }

    fn fold_downcast(&mut self, e: Expr, f: Field) -> Stmt {
        Stmt::Downcast( Downcast {
            base: self.fold_expr(e),
            field: f,
        })
    }
}

pub trait FallibleStmtFolder {
    type Error;

    fn fallible_fold(&mut self, e: Stmt) -> Result<Stmt, Self::Error> {
        match e {
            Stmt::Comment( Comment {comment} ) => self.fallible_fold_comment(comment),
            Stmt::Label( Label {label} ) => self.fallible_fold_label(label),
            Stmt::Inhale( Inhale {expr} ) => self.fallible_fold_inhale(expr),
            Stmt::Exhale( Exhale {expr, position} ) => self.fallible_fold_exhale(expr, position),
            Stmt::Assert( Assert {expr, position} ) => self.fallible_fold_assert(expr, position),
            Stmt::MethodCall( MethodCall {method_name, arguments, targets} ) => self.fallible_fold_method_call(method_name, arguments, targets),
            Stmt::Assign( Assign {target, source, kind} ) => self.fallible_fold_assign(target, source, kind),
            Stmt::Fold( Fold {predicate_name, arguments, permission, enum_variant, position} ) => self.fallible_fold_fold(predicate_name, arguments, permission, enum_variant, position),
            Stmt::Unfold( Unfold {predicate_name, arguments, permission, enum_variant} ) => self.fallible_fold_unfold(predicate_name, arguments, permission, enum_variant),
            Stmt::Obtain( Obtain {expr, position} ) => self.fallible_fold_obtain(expr, position),
            Stmt::BeginFrame(_) => self.fallible_fold_begin_frame(),
            Stmt::EndFrame(_) => self.fallible_fold_end_frame(),
            Stmt::TransferPerm( TransferPerm {left, right, unchecked} ) => self.fallible_fold_transfer_perm(left, right, unchecked),
            Stmt::PackageMagicWand( PackageMagicWand {magic_wand, package_stmts, label, variables, position} ) => {
                self.fallible_fold_package_magic_wand(magic_wand, package_stmts, label, variables, position)
            },
            Stmt::ApplyMagicWand( ApplyMagicWand {magic_wand, position} ) => self.fallible_fold_apply_magic_wand(magic_wand, position),
            Stmt::ExpireBorrows( ExpireBorrows {dag} ) => self.fallible_fold_expire_borrows(dag),
            Stmt::If( If {guard, then_stmts, else_stmts} ) => self.fallible_fold_if(guard, then_stmts, else_stmts),
            Stmt::Downcast( Downcast {base, field} ) => self.fallible_fold_downcast(base, field),
        }
    }

    fn fallible_fold_expr(&mut self, expr: Expr) -> Result<Expr, Self::Error> {
        Ok(expr)
    }

    fn fallible_fold_comment(&mut self, s: String) -> Result<Stmt, Self::Error> {
        Ok(Stmt::comment(s))
    }

    fn fallible_fold_label(&mut self, s: String) -> Result<Stmt, Self::Error> {
        Ok(Stmt::label(s))
    }

    fn fallible_fold_inhale(&mut self, expr: Expr) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Inhale( Inhale {
            expr: self.fallible_fold_expr(expr)?,
        }))
    }

    fn fallible_fold_exhale(&mut self, e: Expr, position: Position) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Exhale( Exhale {
            expr: self.fallible_fold_expr(e)?,
            position,
        }))
    }

    fn fallible_fold_assert(&mut self, expr: Expr, position: Position) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Assert( Assert {
            expr: self.fallible_fold_expr(expr)?,
            position,
        }))
    }

    fn fallible_fold_method_call(
        &mut self,
        name: String,
        args: Vec<Expr>,
        targets: Vec<LocalVar>,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::MethodCall( MethodCall {
            method_name: name,
            arguments: args.into_iter()
                .map(|e| self.fallible_fold_expr(e))
                .collect::<Result<_, _>>()?,
            targets,
        }))
    }

    fn fallible_fold_assign(
        &mut self,
        p: Expr,
        e: Expr,
        kind: AssignKind,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Assign( Assign {
            target: self.fallible_fold_expr(p)?,
            source: self.fallible_fold_expr(e)?,
            kind,
        }))
    }

    fn fallible_fold_fold(
        &mut self,
        predicate_name: String,
        args: Vec<Expr>,
        perm_amount: PermAmount,
        variant: MaybeEnumVariantIndex,
        position: Position,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Fold( Fold {
            predicate_name,
            arguments: args.into_iter()
                .map(|e| self.fallible_fold_expr(e))
                .collect::<Result<_, _>>()?,
            permission: perm_amount,
            enum_variant: variant,
            position,
        }))
    }

    fn fallible_fold_unfold(
        &mut self,
        predicate_name: String,
        args: Vec<Expr>,
        perm_amount: PermAmount,
        variant: MaybeEnumVariantIndex,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Unfold( Unfold {
            predicate_name,
            arguments: args.into_iter()
                .map(|e| self.fallible_fold_expr(e))
                .collect::<Result<_, _>>()?,
            permission: perm_amount,
            enum_variant: variant,
        }))
    }

    fn fallible_fold_obtain(&mut self, e: Expr, position: Position) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Obtain( Obtain {
            expr: self.fallible_fold_expr(e)?,
            position,
        }))
    }

    fn fallible_fold_begin_frame(&mut self) -> Result<Stmt, Self::Error> {
        Ok(Stmt::BeginFrame (BeginFrame {} ))
    }

    fn fallible_fold_end_frame(&mut self) -> Result<Stmt, Self::Error> {
        Ok(Stmt::EndFrame (EndFrame {} ))
    }

    fn fallible_fold_transfer_perm(
        &mut self,
        a: Expr,
        b: Expr,
        unchecked: bool,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::TransferPerm( TransferPerm {
            left: self.fallible_fold_expr(a)?,
            right: self.fallible_fold_expr(b)?,
            unchecked,
        }))
    }

    fn fallible_fold_package_magic_wand(
        &mut self,
        wand: Expr,
        body: Vec<Stmt>,
        label: String,
        vars: Vec<LocalVar>,
        position: Position,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::PackageMagicWand( PackageMagicWand {
            magic_wand: self.fallible_fold_expr(wand)?,
            package_stmts: body.into_iter()
                .map(|x| self.fallible_fold(x))
                .collect::<Result<_, _>>()?,
            label,
            variables: vars,
            position,
        }))
    }

    fn fallible_fold_apply_magic_wand(
        &mut self,
        w: Expr,
        position: Position,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::ApplyMagicWand( ApplyMagicWand {
            magic_wand: self.fallible_fold_expr(w)?,
            position,
        }))
    }

    fn fallible_fold_expire_borrows(&mut self, dag: ReborrowingDAG) -> Result<Stmt, Self::Error> {
        Ok(Stmt::ExpireBorrows( ExpireBorrows {dag} ))
    }

    fn fallible_fold_if(
        &mut self,
        g: Expr,
        t: Vec<Stmt>,
        e: Vec<Stmt>,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::If( If {
            guard: self.fallible_fold_expr(g)?,
            then_stmts: t.into_iter()
                .map(|x| self.fallible_fold(x))
                .collect::<Result<_, _>>()?,
            else_stmts: e.into_iter()
                .map(|x| self.fallible_fold(x))
                .collect::<Result<_, _>>()?,
        }))
    }

    fn fallible_fold_downcast(&mut self, e: Expr, f: Field) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Downcast( Downcast {
            base: self.fallible_fold_expr(e)?,
            field: f
        }))
    }
}

pub trait StmtWalker {
    fn walk(&mut self, e: &Stmt) {
        match e {
            Stmt::Comment( Comment {comment} ) => self.walk_comment(comment),
            Stmt::Label( Label {label} ) => self.walk_label(label),
            Stmt::Inhale( Inhale {expr} ) => self.walk_inhale(expr),
            Stmt::Exhale( Exhale {expr, position} ) => self.walk_exhale(expr, position),
            Stmt::Assert( Assert {expr, position} ) => self.walk_assert(expr, position),
            Stmt::MethodCall( MethodCall {method_name, arguments, targets} ) => self.walk_method_call(method_name, arguments, targets),
            Stmt::Assign( Assign {target, source, kind} ) => self.walk_assign(target, source, kind),
            Stmt::Fold( Fold {predicate_name, arguments, permission, enum_variant, position} ) => self.walk_fold(predicate_name, arguments, permission, enum_variant, position),
            Stmt::Unfold( Unfold {predicate_name, arguments, permission, enum_variant} ) => self.walk_unfold(predicate_name, arguments, permission, enum_variant),
            Stmt::Obtain( Obtain {expr, position} ) => self.walk_obtain(expr, position),
            Stmt::BeginFrame(_) => self.walk_begin_frame(),
            Stmt::EndFrame(_) => self.walk_end_frame(),
            Stmt::TransferPerm( TransferPerm {left, right, unchecked} ) => self.walk_transfer_perm(left, right, unchecked),
            Stmt::PackageMagicWand( PackageMagicWand {magic_wand, package_stmts, label, variables, position} ) => {
                self.walk_package_magic_wand(magic_wand, package_stmts, label, variables, position)
            },
            Stmt::ApplyMagicWand( ApplyMagicWand {magic_wand, position} ) => self.walk_apply_magic_wand(magic_wand, position),
            Stmt::ExpireBorrows( ExpireBorrows {dag} ) => self.walk_expire_borrows(dag),
            Stmt::If( If {guard, then_stmts, else_stmts} ) => self.walk_if(guard, then_stmts, else_stmts),
            Stmt::Downcast( Downcast {base, field} ) => self.walk_downcast(base, field),
        }
    }

    fn walk_expr(&mut self, _expr: &Expr) {}

    fn walk_local_var(&mut self, _local_var: &LocalVar) {}

    fn walk_comment(&mut self, _text: &str) {}

    fn walk_label(&mut self, _label: &str) {}

    fn walk_inhale(&mut self, expr: &Expr) {
        self.walk_expr(expr);
    }

    fn walk_exhale(&mut self, expr: &Expr, _pos: &Position) {
        self.walk_expr(expr);
    }

    fn walk_assert(&mut self, expr: &Expr, _pos: &Position) {
        self.walk_expr(expr);
    }

    fn walk_method_call(&mut self, _method_name: &str, args: &Vec<Expr>, targets: &Vec<LocalVar>) {
        for arg in args {
            self.walk_expr(arg);
        }
        for target in targets {
            self.walk_local_var(target);
        }
    }

    fn walk_assign(&mut self, target: &Expr, expr: &Expr, _kind: &AssignKind) {
        self.walk_expr(target);
        self.walk_expr(expr);
    }

    fn walk_fold(
        &mut self,
        _predicate_name: &str,
        args: &Vec<Expr>,
        _perm: &PermAmount,
        _variant: &MaybeEnumVariantIndex,
        _pos: &Position,
    ) {
        for arg in args {
            self.walk_expr(arg);
        }
    }

    fn walk_unfold(
        &mut self,
        _predicate_name: &str,
        args: &Vec<Expr>,
        _perm: &PermAmount,
        _variant: &MaybeEnumVariantIndex,
    ) {
        for arg in args {
            self.walk_expr(arg);
        }
    }

    fn walk_obtain(&mut self, expr: &Expr, _pos: &Position) {
        self.walk_expr(expr);
    }

    fn walk_weak_obtain(&mut self, expr: &Expr) {
        self.walk_expr(expr);
    }

    fn walk_havoc(&mut self) {}

    fn walk_begin_frame(&mut self) {}

    fn walk_end_frame(&mut self) {}

    fn walk_transfer_perm(&mut self, from: &Expr, to: &Expr, _unchecked: &bool) {
        self.walk_expr(from);
        self.walk_expr(to);
    }

    fn walk_package_magic_wand(
        &mut self,
        wand: &Expr,
        body: &Vec<Stmt>,
        _label: &str,
        vars: &[LocalVar],
        _pos: &Position,
    ) {
        self.walk_expr(wand);
        for var in vars {
            self.walk_local_var(var);
        }
        for statement in body {
            self.walk(statement);
        }
    }

    fn walk_apply_magic_wand(&mut self, wand: &Expr, _p: &Position) {
        self.walk_expr(wand);
    }

    fn walk_expire_borrows(&mut self, _dag: &ReborrowingDAG) {}

    fn walk_nested_cfg(&mut self, _entry: &CfgBlockIndex, _exit: &CfgBlockIndex) {}

    fn walk_if(&mut self, g: &Expr, t: &Vec<Stmt>, e: &Vec<Stmt>) {
        self.walk_expr(g);
        for s in t {
            self.walk(s);
        }
        for s in e {
            self.walk(s);
        }
    }

    fn walk_downcast(&mut self, e: &Expr, _f: &Field) {
        self.walk_expr(e);
    }
}

pub fn stmts_to_str(stmts: &[Stmt]) -> String {
    stmts
        .iter()
        .map(|stmt| format!("{}\n", stmt))
        .collect::<String>()
}
