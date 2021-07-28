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

use super::super::super::{legacy, converter};

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

impl From<Stmt> for legacy::Stmt {
    fn from(stmt: Stmt) -> legacy::Stmt {
        match stmt {
            Stmt::Comment(comment) => legacy::Stmt::Comment(
                comment.comment,
            ),
            Stmt::Label(label) => legacy::Stmt::Label (
                label.label,
            ),
            Stmt::Inhale(inhale) => legacy::Stmt::Inhale (
                legacy::Expr::from(inhale.expr),
            ),
            Stmt::Exhale(exhale) => legacy::Stmt::Exhale (
                legacy::Expr::from(exhale.expr),
                legacy::Position::from(exhale.position),
            ),
            Stmt::Assert(assert) => legacy::Stmt::Assert (
                legacy::Expr::from(assert.expr),
                legacy::Position::from(assert.position),
            ),
            Stmt::MethodCall(method_call) => legacy::Stmt::MethodCall (
                method_call.method_name,
                method_call.arguments.into_iter().map(|argument| legacy::Expr::from(argument)).collect(),
                method_call.targets.into_iter().map(|target| legacy::LocalVar::from(target)).collect(),
            ),
            Stmt::Assign(assign) => legacy::Stmt::Assign (
                legacy::Expr::from(assign.target),
                legacy::Expr::from(assign.source),
                legacy::AssignKind::from(assign.kind),
            ),
            Stmt::Fold(fold) => legacy::Stmt::Fold (
                fold.predicate_name,
                fold.arguments.into_iter().map(|argument| legacy::Expr::from(argument)).collect(),
                legacy::PermAmount::from(fold.permission),
                fold.enum_variant.map(|enum_variant_index| legacy::EnumVariantIndex::from(enum_variant_index)),
                legacy::Position::from(fold.position),
            ),
            Stmt::Unfold(unfold) => legacy::Stmt::Unfold (
                unfold.predicate_name,
                unfold.arguments.into_iter().map(|argument| legacy::Expr::from(argument)).collect(),
                legacy::PermAmount::from(unfold.permission),
                unfold.enum_variant.map(|enum_variant_index| legacy::EnumVariantIndex::from(enum_variant_index)),
            ),
            Stmt::Obtain(obtain) => legacy::Stmt::Obtain (
                legacy::Expr::from(obtain.predicate_name),
                legacy::Position::from(obtain.position),
            ),
            Stmt::BeginFrame(_) => legacy::Stmt::BeginFrame,
            Stmt::EndFrame(_) => legacy::Stmt::EndFrame,
            Stmt::TransferPerm(transfer_perm) => legacy::Stmt::TransferPerm (
                legacy::Expr::from(transfer_perm.left),
                legacy::Expr::from(transfer_perm.right),
                transfer_perm.unchecked,
            ),
            Stmt::PackageMagicWand(package_magic_wand) => legacy::Stmt::PackageMagicWand (
                legacy::Expr::from(package_magic_wand.magic_wand),
                package_magic_wand.package_stmts.into_iter().map(|package_stmt| legacy::Stmt::from(package_stmt)).collect(),
                package_magic_wand.label,
                package_magic_wand.variables.into_iter().map(|variable| legacy::LocalVar::from(variable)).collect(),
                legacy::Position::from(package_magic_wand.position),
            ),
            Stmt::ApplyMagicWand(apply_magic_wand) => legacy::Stmt::ApplyMagicWand (
                legacy::Expr::from(apply_magic_wand.magic_wand),
                legacy::Position::from(apply_magic_wand.position),
            ),
            Stmt::ExpireBorrows(expire_borrows) => legacy::Stmt::ExpireBorrows (
                legacy::DAG::from(expire_borrows.dag),
            ),
            Stmt::If(if_stmt) => legacy::Stmt::If (
                legacy::Expr::from(if_stmt.guard),
                if_stmt.then_stmts.into_iter().map(|then_stmt| legacy::Stmt::from(then_stmt)).collect(),
                if_stmt.else_stmts.into_iter().map(|else_stmt| legacy::Stmt::from(else_stmt)).collect(),
            ),
            Stmt::Downcast(downcast) => legacy::Stmt::Downcast (
                legacy::Expr::from(downcast.base),
                legacy::Field::from(downcast.field),
            ),
        }
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl converter::Generic for Stmt {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        match self {
            Stmt::Comment(comment) => Stmt::Comment(comment.substitute(map)),
            Stmt::Label(label) => Stmt::Label(label.substitute(map)),
            Stmt::Inhale(inhale) => Stmt::Inhale(inhale.substitute(map)),
            Stmt::Exhale(exhale) => Stmt::Exhale(exhale.substitute(map)),
            Stmt::Assert(assert) => Stmt::Assert(assert.substitute(map)),
            Stmt::MethodCall(method_call) => Stmt::MethodCall(method_call.substitute(map)),
            Stmt::Assign(assign) =>  Stmt::Assign(assign.substitute(map)),
            Stmt::Fold(fold) => Stmt::Fold(fold.substitute(map)),
            Stmt::Unfold(unfold) => Stmt::Unfold(unfold.substitute(map)),
            Stmt::Obtain(obtain) => Stmt::Obtain(obtain.substitute(map)),
            Stmt::BeginFrame(begin_frame) => Stmt::BeginFrame(begin_frame.substitute(map)),
            Stmt::EndFrame(end_frame) => Stmt::EndFrame(end_frame.substitute(map)),
            Stmt::TransferPerm(transfer_perm) => Stmt::TransferPerm(transfer_perm.substitute(map)),
            Stmt::PackageMagicWand(package_magic_wand) => Stmt::PackageMagicWand(package_magic_wand.substitute(map)),
            Stmt::ApplyMagicWand(apply_magic_wand) => Stmt::ApplyMagicWand(apply_magic_wand.substitute(map)),
            Stmt::ExpireBorrows(expire_borrows) => Stmt::ExpireBorrows(expire_borrows.substitute(map)),
            Stmt::If(if_stmt) => Stmt::If(if_stmt.substitute(map)),
            Stmt::Downcast(downcast) => Stmt::Downcast(downcast.substitute(map)),
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

impl From<AssignKind> for legacy::AssignKind {
    fn from(assign_kind: AssignKind) -> legacy::AssignKind {
        match assign_kind {
            AssignKind::Copy => legacy::AssignKind::Copy,
            AssignKind::Move => legacy::AssignKind::Move,
            AssignKind::MutableBorrow(borrow) => legacy::AssignKind::MutableBorrow(legacy::Borrow::from(borrow)),
            AssignKind::SharedBorrow(borrow) => legacy::AssignKind::SharedBorrow(legacy::Borrow::from(borrow)),
            AssignKind::Ghost => legacy::AssignKind::Ghost,
        }
    }
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

impl converter::Generic for Comment {
    fn substitute(self, _map: &HashMap<TypeVar, Type>) -> Self {
        self
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

impl converter::Generic for Label {
    fn substitute(self, _map: &HashMap<TypeVar, Type>) -> Self {
        self
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

impl converter::Generic for Inhale {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut inhale = self;
        inhale.expr = inhale.expr.substitute(map);
        inhale
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

impl converter::Generic for Exhale {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut exhale = self;
        exhale.expr = exhale.expr.substitute(map);
        exhale
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

impl converter::Generic for Assert {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut assert = self;
        assert.expr = assert.expr.substitute(map);
        assert
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

impl converter::Generic for MethodCall {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut method_call = self;
        method_call.arguments = method_call.arguments.into_iter().map(|argument| argument.substitute(map)).collect();
        method_call.targets = method_call.targets.into_iter().map(|target| target.substitute(map)).collect();
        method_call
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

impl converter::Generic for Assign {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut assign = self;
        assign.target = assign.target.substitute(map);
        assign.source = assign.source.substitute(map);
        assign
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

impl converter::Generic for Fold {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut fold = self;
        fold.arguments = fold.arguments.into_iter().map(|argument| argument.substitute(map)).collect();
        fold.enum_variant = fold.enum_variant.map(|enum_variant_index| enum_variant_index.substitute(map));
        fold
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

impl converter::Generic for Unfold {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut unfold = self;
        unfold.arguments = unfold.arguments.into_iter().map(|argument| argument.substitute(map)).collect();
        unfold.enum_variant = unfold.enum_variant.map(|enum_variant_index| enum_variant_index.substitute(map));
        unfold
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

impl converter::Generic for Obtain {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut obtain = self;
        obtain.predicate_name = obtain.predicate_name.substitute(map);
        obtain
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BeginFrame {}

impl fmt::Display for BeginFrame {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "begin frame")
    }
}

impl converter::Generic for BeginFrame {
    fn substitute(self, _map: &HashMap<TypeVar, Type>) -> Self {
        self
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EndFrame {}

impl fmt::Display for EndFrame {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "end frame")
    }
}

impl converter::Generic for EndFrame {
    fn substitute(self, _map: &HashMap<TypeVar, Type>) -> Self {
        self
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

impl converter::Generic for TransferPerm {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut transfer_perm = self;
        transfer_perm.left = transfer_perm.left.substitute(map);
        transfer_perm.right = transfer_perm.right.substitute(map);
        transfer_perm
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

impl converter::Generic for PackageMagicWand {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut package_magic_wand = self;
        package_magic_wand.magic_wand = package_magic_wand.magic_wand.substitute(map);
        package_magic_wand.package_stmts = package_magic_wand.package_stmts.into_iter().map(|package_stmt| package_stmt.substitute(map)).collect();
        package_magic_wand.variables = package_magic_wand.variables.into_iter().map(|variable| variable.substitute(map)).collect();
        package_magic_wand
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

impl converter::Generic for ApplyMagicWand {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut apply_magic_wand = self;
        apply_magic_wand.magic_wand = apply_magic_wand.magic_wand.substitute(map);
        apply_magic_wand
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

impl converter::Generic for ExpireBorrows {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut expire_borrows = self;
        expire_borrows.dag = expire_borrows.dag.substitute(map);
        expire_borrows
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

impl converter::Generic for If {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut if_stmt = self;
        if_stmt.guard = if_stmt.guard.substitute(map);
        if_stmt.then_stmts = if_stmt.then_stmts.into_iter().map(|then_stmt| then_stmt.substitute(map)).collect();
        if_stmt.else_stmts = if_stmt.else_stmts.into_iter().map(|else_stmt| else_stmt.substitute(map)).collect();
        if_stmt
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

impl converter::Generic for Downcast {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut downcast = self;
        downcast.base = downcast.base.substitute(map);
        downcast.field = downcast.field.substitute(map);
        downcast
    }
}
