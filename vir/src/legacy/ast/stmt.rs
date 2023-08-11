// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::super::{
    borrows::{Borrow, DAG as ReborrowingDAG},
    cfg::CfgBlockIndex,
};
use crate::legacy::ast::*;
use std::{
    fmt,
    hash::{Hash, Hasher},
    mem::discriminant,
    ops::Deref,
};

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Stmt {
    Comment(String),
    Label(String),
    Inhale(Expr, Position),
    Exhale(Expr, Position),
    Assume(Expr, Position),
    Assert(Expr, Position),
    Refute(Expr, Position),
    /// MethodCall: method_name, args, targets
    MethodCall(String, Vec<Expr>, Vec<LocalVar>),
    /// Target, source, kind
    Assign(Expr, Expr, AssignKind),
    /// Fold statement: predicate name, predicate args, perm_amount, variant of enum, position.
    Fold(
        String,
        Vec<Expr>,
        PermAmount,
        MaybeEnumVariantIndex,
        Position,
    ),
    /// Unfold statement: predicate name, predicate args, perm_amount, variant of enum.
    Unfold(String, Vec<Expr>, PermAmount, MaybeEnumVariantIndex),
    /// Obtain: conjunction of Expr::PredicateAccessPredicate or Expr::FieldAccessPredicate
    /// They will be used by the fold/unfold algorithm
    Obtain(Expr, Position),
    /// Mark a CFG point in which all current permissions are framed out
    /// They will be used by the fold/unfold algorithm
    BeginFrame,
    /// Mark a CFG point in which all the permissions of a corresponding `BeginFrame` are framed in
    /// They will be used by the fold/unfold algorithm
    EndFrame,
    /// Move permissions from a place to another.
    /// This is used to restore permissions in the fold/unfold state when a loan expires.
    ///
    /// The last argument indicates if the transfer is unchecked. Unchecked transfer is used for
    /// encoding shared borrows which can be dangling and, therefore, we cannot use the safety
    /// checks.
    TransferPerm(Expr, Expr, bool),
    /// Package a Magic Wand
    /// Arguments: the magic wand, the package statement's body, the
    /// label just before the statement, and ghost variables used inside
    /// the package statement.
    PackageMagicWand(Expr, Vec<Stmt>, String, Vec<LocalVar>, Position),
    /// Apply a Magic Wand.
    /// Arguments: the magic wand.
    ApplyMagicWand(Expr, Position),
    /// Expire borrows given in the reborrowing DAG.
    ExpireBorrows(ReborrowingDAG),
    /// An `if` statement: the guard and the 'then' branch.
    If(Expr, Vec<Stmt>, Vec<Stmt>),
    /// Inform the fold-unfold algorithm that at this program point a enum type can be downcasted
    /// to one of its variants. This statement is a no-op for Viper.
    /// Arguments:
    /// * place to the enumeration instance
    /// * field that encodes the variant
    Downcast(Expr, Field),
}

// This preserves `Stmt == Stmt ==> hash(Stmt) == hash(Stmt)`
#[allow(clippy::derived_hash_with_manual_eq)]
impl Hash for Stmt {
    /// Hash ignoring Comments and ExpireBorrows
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Stmt::Comment(_) => return,
            Stmt::Label(s) => s.hash(state),
            Stmt::Inhale(e, p) => (e, p).hash(state),
            Stmt::Exhale(e, p) => (e, p).hash(state),
            Stmt::Assume(e, p) => (e, p).hash(state),
            Stmt::Assert(e, p) => (e, p).hash(state),
            Stmt::Refute(e, p) => (e, p).hash(state),
            Stmt::MethodCall(s, v1, v2) => (s, v1, v2).hash(state),
            Stmt::Assign(e1, e2, ak) => (e1, e2, ak).hash(state),
            Stmt::Fold(s, v, pa, mevi, p) => (s, v, pa, mevi, p).hash(state),
            Stmt::Unfold(s, ve, pa, mevi) => (s, ve, pa, mevi).hash(state),
            Stmt::Obtain(e, p) => (e, p).hash(state),
            Stmt::BeginFrame => {}
            Stmt::EndFrame => {}
            Stmt::TransferPerm(e1, e2, b) => (e1, e2, b).hash(state),
            Stmt::PackageMagicWand(e, vs, s, vlv, p) => (e, vs, s, vlv, p).hash(state),
            Stmt::ApplyMagicWand(e, p) => (e, p).hash(state),
            Stmt::ExpireBorrows(_) => return,
            Stmt::If(e, vs1, vs2) => (e, vs1, vs2).hash(state),
            Stmt::Downcast(e, f) => (e, f).hash(state),
        }
        discriminant(self).hash(state);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
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

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Stmt::Comment(ref comment) => write!(f, "// {comment}"),
            Stmt::Label(ref label) => write!(f, "label {label}"),
            Stmt::Inhale(ref expr, _) => {
                write!(f, "inhale {expr}")
            }
            Stmt::Exhale(ref expr, _) => write!(f, "exhale {expr}"),
            Stmt::Assume(ref expr, _) => {
                write!(f, "assume {expr}")
            }
            Stmt::Assert(ref expr, _) => {
                write!(f, "assert {expr}")
            }
            Stmt::Refute(ref expr, _) => {
                write!(f, "refute {expr}")
            }
            Stmt::MethodCall(ref name, ref args, ref vars) => write!(
                f,
                "{} := {}({})",
                vars.iter()
                    .map(|f| f.to_string())
                    .collect::<Vec<String>>()
                    .join(", "),
                name,
                args.iter()
                    .map(|f| f.to_string())
                    .collect::<Vec<String>>()
                    .join(", "),
            ),
            Stmt::Assign(ref lhs, ref rhs, kind) => match kind {
                AssignKind::Move => write!(f, "{lhs} := move {rhs}"),
                AssignKind::Copy => write!(f, "{lhs} := copy {rhs}"),
                AssignKind::MutableBorrow(borrow) => {
                    write!(f, "{lhs} := mut borrow {rhs} // {borrow:?}")
                }
                AssignKind::SharedBorrow(borrow) => {
                    write!(f, "{lhs} := borrow {rhs} // {borrow:?}")
                }
                AssignKind::Ghost => write!(f, "{lhs} := ghost {rhs}"),
            },

            Stmt::Fold(ref pred_name, ref args, perm, ref variant, _) => write!(
                f,
                "fold acc({}({}), {})",
                if let Some(variant_index) = variant {
                    format!("{pred_name}<variant {variant_index}>")
                } else {
                    pred_name.to_string()
                },
                args.iter()
                    .map(|f| f.to_string())
                    .collect::<Vec<String>>()
                    .join(", "),
                perm,
            ),

            Stmt::Unfold(ref pred_name, ref args, perm, ref variant) => write!(
                f,
                "unfold acc({}({}), {})",
                if let Some(variant_index) = variant {
                    format!("{pred_name}<variant {variant_index}>")
                } else {
                    pred_name.to_string()
                },
                args.iter()
                    .map(|f| f.to_string())
                    .collect::<Vec<String>>()
                    .join(", "),
                perm,
            ),

            Stmt::Obtain(ref expr, _) => write!(f, "obtain {expr}"),

            Stmt::BeginFrame => write!(f, "begin frame"),

            Stmt::EndFrame => write!(f, "end frame"),

            Stmt::TransferPerm(ref lhs, ref rhs, unchecked) => {
                write!(f, "transfer perm {lhs} --> {rhs} // unchecked: {unchecked}")
            }

            Stmt::PackageMagicWand(
                ref magic_wand,
                ref package_stmts,
                ref label,
                _vars,
                _position,
            ) => {
                if let Expr::MagicWand(ref lhs, ref rhs, None, _) = magic_wand {
                    writeln!(f, "package[{label}] {lhs}")?;
                    writeln!(f, "    --* {rhs}")?;
                } else {
                    writeln!(f, "package[{label}] {magic_wand}")?;
                }
                write!(f, "{{")?;
                if !package_stmts.is_empty() {
                    writeln!(f)?;
                }
                for stmt in package_stmts.iter() {
                    writeln!(f, "    {}", stmt.to_string().replace('\n', "\n    "))?;
                }
                write!(f, "}}")
            }

            Stmt::ApplyMagicWand(Expr::MagicWand(ref lhs, ref rhs, Some(borrow), _), _) => {
                writeln!(f, "apply[{borrow:?}] {lhs} --* {rhs}")
            }

            Stmt::ApplyMagicWand(ref magic_wand, _) => {
                if let Expr::MagicWand(ref lhs, ref rhs, Some(borrow), _) = magic_wand {
                    writeln!(f, "apply[{borrow:?}] {lhs} --* {rhs}")
                } else {
                    writeln!(f, "apply {magic_wand}")
                }
            }

            Stmt::ExpireBorrows(dag) => writeln!(f, "expire_borrows {dag:?}"),

            Stmt::If(ref guard, ref then_stmts, ref else_stmts) => {
                fn write_stmt(f: &mut fmt::Formatter, stmt: &Stmt) -> fmt::Result {
                    writeln!(f, "    {}", stmt.to_string().replace('\n', "\n    "))
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
                write!(f, "if {guard} ")?;
                write_block(f, then_stmts)?;
                write!(f, " else ")?;
                write_block(f, else_stmts)
            }

            Stmt::Downcast(e, v) => writeln!(f, "downcast {e} to {v}"),
        }
    }
}

impl Stmt {
    pub fn is_comment(&self) -> bool {
        matches!(self, Stmt::Comment(_))
    }

    pub fn comment<S: ToString>(comment: S) -> Self {
        Stmt::Comment(comment.to_string())
    }

    pub fn label<S: ToString>(label: S) -> Self {
        Stmt::Label(label.to_string())
    }

    pub fn package_magic_wand(
        lhs: Expr,
        rhs: Expr,
        stmts: Vec<Stmt>,
        label: String,
        vars: Vec<LocalVar>,
        pos: Position,
    ) -> Self {
        Stmt::PackageMagicWand(
            Expr::MagicWand(Box::new(lhs), Box::new(rhs), None, pos),
            stmts,
            label,
            vars,
            pos,
        )
    }

    pub fn apply_magic_wand(lhs: Expr, rhs: Expr, borrow: Borrow, pos: Position) -> Self {
        Stmt::ApplyMagicWand(Expr::magic_wand(lhs, rhs, Some(borrow)), pos)
    }

    pub fn pos(&self) -> Option<&Position> {
        match self {
            Stmt::Inhale(_, ref p)
            | Stmt::Exhale(_, ref p)
            | Stmt::Assume(_, ref p)
            | Stmt::Assert(_, ref p)
            | Stmt::Refute(_, ref p)
            | Stmt::Fold(_, _, _, _, ref p)
            | Stmt::Obtain(_, ref p)
            | Stmt::PackageMagicWand(_, _, _, _, ref p)
            | Stmt::ApplyMagicWand(_, ref p) => Some(p),
            _ => None,
        }
    }

    pub fn pos_mut(&mut self) -> Option<&mut Position> {
        match self {
            Stmt::Inhale(_, ref mut p)
            | Stmt::Exhale(_, ref mut p)
            | Stmt::Assume(_, ref mut p)
            | Stmt::Assert(_, ref mut p)
            | Stmt::Refute(_, ref mut p)
            | Stmt::Fold(_, _, _, _, ref mut p)
            | Stmt::Obtain(_, ref mut p)
            | Stmt::PackageMagicWand(_, _, _, _, ref mut p)
            | Stmt::ApplyMagicWand(_, ref mut p) => Some(p),
            _ => None,
        }
    }

    #[must_use]
    pub fn set_pos(mut self, pos: Position) -> Self {
        self.pos_mut().into_iter().for_each(|p| *p = pos);
        self
    }

    // Replace a Position::default() position with `pos`
    #[must_use]
    pub fn set_default_pos(self, pos: Position) -> Self {
        if self.pos().iter().any(|x| x.is_default()) {
            self.set_pos(pos)
        } else {
            self
        }
    }

    // Replace all Position::default() positions in expressions with `pos`
    #[must_use]
    pub fn set_default_expr_pos(self, pos: Position) -> Self {
        self.map_expr(|e| e.set_default_pos(pos))
    }

    /// Visit each position.
    /// Note: statements like `Stmt::If` can contain multiple positions.
    pub fn visit_positions<F: FnMut(&Position)>(&self, mut visitor: F) {
        // Recursively visiting the statements of the nested Stmt::If statements is difficult; the
        // recursive type constraints are hard to satisfy. So, here is an iterative implementation.
        let mut queue = vec![self];
        while let Some(stmt) = queue.pop() {
            stmt.pos().into_iter().for_each(&mut visitor);
            if let Stmt::If(_, then_stmts, else_stmts) = stmt {
                queue.extend(then_stmts);
                queue.extend(else_stmts);
            }
        }
    }

    /// Mutably visit each position.
    /// Note: statements like `Stmt::If` can contain multiple positions.
    pub fn visit_positions_mut<F: FnMut(&mut Position)>(&mut self, mut visitor: F) {
        // Recursively visiting the statements of the nested Stmt::If statements is difficult; the
        // recursive type constraints are hard to satisfy. So, here is an iterative implementation.
        let mut queue = vec![self];
        while let Some(stmt) = queue.pop() {
            stmt.pos_mut().into_iter().for_each(&mut visitor);
            if let Stmt::If(_, then_stmts, else_stmts) = stmt {
                queue.extend(then_stmts);
                queue.extend(else_stmts);
            }
        }
    }
}

pub trait StmtFolder {
    fn fold(&mut self, e: Stmt) -> Stmt {
        match e {
            Stmt::Comment(s) => self.fold_comment(s),
            Stmt::Label(s) => self.fold_label(s),
            Stmt::Inhale(expr, pos) => self.fold_inhale(expr, pos),
            Stmt::Exhale(e, p) => self.fold_exhale(e, p),
            Stmt::Assume(expr, pos) => self.fold_assume(expr, pos),
            Stmt::Assert(expr, pos) => self.fold_assert(expr, pos),
            Stmt::Refute(expr, pos) => self.fold_refute(expr, pos),
            Stmt::MethodCall(s, ve, vv) => self.fold_method_call(s, ve, vv),
            Stmt::Assign(p, e, k) => self.fold_assign(p, e, k),
            Stmt::Fold(s, ve, perm, variant, p) => self.fold_fold(s, ve, perm, variant, p),
            Stmt::Unfold(s, ve, perm, variant) => self.fold_unfold(s, ve, perm, variant),
            Stmt::Obtain(e, p) => self.fold_obtain(e, p),
            Stmt::BeginFrame => self.fold_begin_frame(),
            Stmt::EndFrame => self.fold_end_frame(),
            Stmt::TransferPerm(a, b, c) => self.fold_transfer_perm(a, b, c),
            Stmt::PackageMagicWand(w, s, l, v, p) => self.fold_package_magic_wand(w, s, l, v, p),
            Stmt::ApplyMagicWand(w, p) => self.fold_apply_magic_wand(w, p),
            Stmt::ExpireBorrows(d) => self.fold_expire_borrows(d),
            Stmt::If(g, t, e) => self.fold_if(g, t, e),
            Stmt::Downcast(e, f) => self.fold_downcast(e, f),
        }
    }

    fn fold_expr(&mut self, expr: Expr) -> Expr {
        expr
    }

    fn fold_comment(&mut self, s: String) -> Stmt {
        Stmt::Comment(s)
    }

    fn fold_label(&mut self, s: String) -> Stmt {
        Stmt::Label(s)
    }

    fn fold_inhale(&mut self, expr: Expr, pos: Position) -> Stmt {
        Stmt::Inhale(self.fold_expr(expr), pos)
    }

    fn fold_exhale(&mut self, e: Expr, p: Position) -> Stmt {
        Stmt::Exhale(self.fold_expr(e), p)
    }

    fn fold_assume(&mut self, expr: Expr, pos: Position) -> Stmt {
        Stmt::Assume(self.fold_expr(expr), pos)
    }

    fn fold_assert(&mut self, expr: Expr, pos: Position) -> Stmt {
        Stmt::Assert(self.fold_expr(expr), pos)
    }

    fn fold_refute(&mut self, expr: Expr, pos: Position) -> Stmt {
        Stmt::Refute(self.fold_expr(expr), pos)
    }

    fn fold_method_call(&mut self, name: String, args: Vec<Expr>, targets: Vec<LocalVar>) -> Stmt {
        Stmt::MethodCall(
            name,
            args.into_iter().map(|e| self.fold_expr(e)).collect(),
            targets,
        )
    }

    fn fold_assign(&mut self, p: Expr, e: Expr, k: AssignKind) -> Stmt {
        Stmt::Assign(self.fold_expr(p), self.fold_expr(e), k)
    }

    fn fold_fold(
        &mut self,
        predicate_name: String,
        args: Vec<Expr>,
        perm_amount: PermAmount,
        variant: MaybeEnumVariantIndex,
        pos: Position,
    ) -> Stmt {
        Stmt::Fold(
            predicate_name,
            args.into_iter().map(|e| self.fold_expr(e)).collect(),
            perm_amount,
            variant,
            pos,
        )
    }

    fn fold_unfold(
        &mut self,
        predicate_name: String,
        args: Vec<Expr>,
        perm_amount: PermAmount,
        variant: MaybeEnumVariantIndex,
    ) -> Stmt {
        Stmt::Unfold(
            predicate_name,
            args.into_iter().map(|e| self.fold_expr(e)).collect(),
            perm_amount,
            variant,
        )
    }

    fn fold_obtain(&mut self, e: Expr, p: Position) -> Stmt {
        Stmt::Obtain(self.fold_expr(e), p)
    }

    fn fold_begin_frame(&mut self) -> Stmt {
        Stmt::BeginFrame
    }

    fn fold_end_frame(&mut self) -> Stmt {
        Stmt::EndFrame
    }

    fn fold_transfer_perm(&mut self, a: Expr, b: Expr, unchecked: bool) -> Stmt {
        Stmt::TransferPerm(self.fold_expr(a), self.fold_expr(b), unchecked)
    }

    fn fold_package_magic_wand(
        &mut self,
        wand: Expr,
        body: Vec<Stmt>,
        label: String,
        vars: Vec<LocalVar>,
        pos: Position,
    ) -> Stmt {
        Stmt::PackageMagicWand(
            self.fold_expr(wand),
            body.into_iter().map(|x| self.fold(x)).collect(),
            label,
            vars,
            pos,
        )
    }

    fn fold_apply_magic_wand(&mut self, w: Expr, p: Position) -> Stmt {
        Stmt::ApplyMagicWand(self.fold_expr(w), p)
    }

    fn fold_expire_borrows(&mut self, dag: ReborrowingDAG) -> Stmt {
        Stmt::ExpireBorrows(dag)
    }

    fn fold_if(&mut self, g: Expr, t: Vec<Stmt>, e: Vec<Stmt>) -> Stmt {
        Stmt::If(
            self.fold_expr(g),
            t.into_iter().map(|x| self.fold(x)).collect(),
            e.into_iter().map(|x| self.fold(x)).collect(),
        )
    }

    fn fold_downcast(&mut self, e: Expr, f: Field) -> Stmt {
        Stmt::Downcast(self.fold_expr(e), f)
    }
}

pub trait FallibleStmtFolder {
    type Error;

    fn fallible_fold(&mut self, e: Stmt) -> Result<Stmt, Self::Error> {
        match e {
            Stmt::Comment(s) => self.fallible_fold_comment(s),
            Stmt::Label(s) => self.fallible_fold_label(s),
            Stmt::Inhale(expr, pos) => self.fallible_fold_inhale(expr, pos),
            Stmt::Exhale(e, p) => self.fallible_fold_exhale(e, p),
            Stmt::Assume(expr, pos) => self.fallible_fold_assume(expr, pos),
            Stmt::Assert(expr, pos) => self.fallible_fold_assert(expr, pos),
            Stmt::Refute(expr, pos) => self.fallible_fold_refute(expr, pos),
            Stmt::MethodCall(s, ve, vv) => self.fallible_fold_method_call(s, ve, vv),
            Stmt::Assign(p, e, k) => self.fallible_fold_assign(p, e, k),
            Stmt::Fold(s, ve, perm, variant, p) => self.fallible_fold_fold(s, ve, perm, variant, p),
            Stmt::Unfold(s, ve, perm, variant) => self.fallible_fold_unfold(s, ve, perm, variant),
            Stmt::Obtain(e, p) => self.fallible_fold_obtain(e, p),
            Stmt::BeginFrame => self.fallible_fold_begin_frame(),
            Stmt::EndFrame => self.fallible_fold_end_frame(),
            Stmt::TransferPerm(a, b, c) => self.fallible_fold_transfer_perm(a, b, c),
            Stmt::PackageMagicWand(w, s, l, v, p) => {
                self.fallible_fold_package_magic_wand(w, s, l, v, p)
            }
            Stmt::ApplyMagicWand(w, p) => self.fallible_fold_apply_magic_wand(w, p),
            Stmt::ExpireBorrows(d) => self.fallible_fold_expire_borrows(d),
            Stmt::If(g, t, e) => self.fallible_fold_if(g, t, e),
            Stmt::Downcast(e, f) => self.fallible_fold_downcast(e, f),
        }
    }

    fn fallible_fold_expr(&mut self, expr: Expr) -> Result<Expr, Self::Error> {
        Ok(expr)
    }

    fn fallible_fold_comment(&mut self, s: String) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Comment(s))
    }

    fn fallible_fold_label(&mut self, s: String) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Label(s))
    }

    fn fallible_fold_inhale(&mut self, expr: Expr, pos: Position) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Inhale(self.fallible_fold_expr(expr)?, pos))
    }

    fn fallible_fold_exhale(&mut self, e: Expr, p: Position) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Exhale(self.fallible_fold_expr(e)?, p))
    }

    fn fallible_fold_assume(&mut self, expr: Expr, pos: Position) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Assume(self.fallible_fold_expr(expr)?, pos))
    }

    fn fallible_fold_assert(&mut self, expr: Expr, pos: Position) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Assert(self.fallible_fold_expr(expr)?, pos))
    }

    fn fallible_fold_refute(&mut self, expr: Expr, pos: Position) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Refute(self.fallible_fold_expr(expr)?, pos))
    }

    fn fallible_fold_method_call(
        &mut self,
        name: String,
        args: Vec<Expr>,
        targets: Vec<LocalVar>,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::MethodCall(
            name,
            args.into_iter()
                .map(|e| self.fallible_fold_expr(e))
                .collect::<Result<_, _>>()?,
            targets,
        ))
    }

    fn fallible_fold_assign(
        &mut self,
        p: Expr,
        e: Expr,
        k: AssignKind,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Assign(
            self.fallible_fold_expr(p)?,
            self.fallible_fold_expr(e)?,
            k,
        ))
    }

    fn fallible_fold_fold(
        &mut self,
        predicate_name: String,
        args: Vec<Expr>,
        perm_amount: PermAmount,
        variant: MaybeEnumVariantIndex,
        pos: Position,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Fold(
            predicate_name,
            args.into_iter()
                .map(|e| self.fallible_fold_expr(e))
                .collect::<Result<_, _>>()?,
            perm_amount,
            variant,
            pos,
        ))
    }

    fn fallible_fold_unfold(
        &mut self,
        predicate_name: String,
        args: Vec<Expr>,
        perm_amount: PermAmount,
        variant: MaybeEnumVariantIndex,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Unfold(
            predicate_name,
            args.into_iter()
                .map(|e| self.fallible_fold_expr(e))
                .collect::<Result<_, _>>()?,
            perm_amount,
            variant,
        ))
    }

    fn fallible_fold_obtain(&mut self, e: Expr, p: Position) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Obtain(self.fallible_fold_expr(e)?, p))
    }

    fn fallible_fold_begin_frame(&mut self) -> Result<Stmt, Self::Error> {
        Ok(Stmt::BeginFrame)
    }

    fn fallible_fold_end_frame(&mut self) -> Result<Stmt, Self::Error> {
        Ok(Stmt::EndFrame)
    }

    fn fallible_fold_transfer_perm(
        &mut self,
        a: Expr,
        b: Expr,
        unchecked: bool,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::TransferPerm(
            self.fallible_fold_expr(a)?,
            self.fallible_fold_expr(b)?,
            unchecked,
        ))
    }

    fn fallible_fold_package_magic_wand(
        &mut self,
        wand: Expr,
        body: Vec<Stmt>,
        label: String,
        vars: Vec<LocalVar>,
        pos: Position,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::PackageMagicWand(
            self.fallible_fold_expr(wand)?,
            body.into_iter()
                .map(|x| self.fallible_fold(x))
                .collect::<Result<_, _>>()?,
            label,
            vars,
            pos,
        ))
    }

    fn fallible_fold_apply_magic_wand(
        &mut self,
        w: Expr,
        p: Position,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::ApplyMagicWand(self.fallible_fold_expr(w)?, p))
    }

    fn fallible_fold_expire_borrows(&mut self, dag: ReborrowingDAG) -> Result<Stmt, Self::Error> {
        Ok(Stmt::ExpireBorrows(dag))
    }

    fn fallible_fold_if(
        &mut self,
        g: Expr,
        t: Vec<Stmt>,
        e: Vec<Stmt>,
    ) -> Result<Stmt, Self::Error> {
        Ok(Stmt::If(
            self.fallible_fold_expr(g)?,
            t.into_iter()
                .map(|x| self.fallible_fold(x))
                .collect::<Result<_, _>>()?,
            e.into_iter()
                .map(|x| self.fallible_fold(x))
                .collect::<Result<_, _>>()?,
        ))
    }

    fn fallible_fold_downcast(&mut self, e: Expr, f: Field) -> Result<Stmt, Self::Error> {
        Ok(Stmt::Downcast(self.fallible_fold_expr(e)?, f))
    }
}

pub trait StmtWalker {
    fn walk(&mut self, e: &Stmt) {
        match e {
            Stmt::Comment(s) => self.walk_comment(s),
            Stmt::Label(s) => self.walk_label(s),
            Stmt::Inhale(expr, pos) => self.walk_inhale(expr, pos),
            Stmt::Exhale(e, p) => self.walk_exhale(e, p),
            Stmt::Assume(expr, pos) => self.walk_assume(expr, pos),
            Stmt::Assert(expr, pos) => self.walk_assert(expr, pos),
            Stmt::Refute(expr, pos) => self.walk_refute(expr, pos),
            Stmt::MethodCall(s, ve, vv) => self.walk_method_call(s, ve, vv),
            Stmt::Assign(p, e, k) => self.walk_assign(p, e, k),
            Stmt::Fold(s, ve, perm, variant, pos) => self.walk_fold(s, ve, perm, variant, pos),
            Stmt::Unfold(s, ve, perm, variant) => self.walk_unfold(s, ve, perm, variant),
            Stmt::Obtain(e, p) => self.walk_obtain(e, p),
            Stmt::BeginFrame => self.walk_begin_frame(),
            Stmt::EndFrame => self.walk_end_frame(),
            Stmt::TransferPerm(a, b, c) => self.walk_transfer_perm(a, b, c),
            Stmt::PackageMagicWand(w, s, l, v, p) => self.walk_package_magic_wand(w, s, l, v, p),
            Stmt::ApplyMagicWand(w, p) => self.walk_apply_magic_wand(w, p),
            Stmt::ExpireBorrows(d) => self.walk_expire_borrows(d),
            Stmt::If(g, t, e) => self.walk_if(g, t, e),
            Stmt::Downcast(e, f) => self.walk_downcast(e, f),
        }
    }

    fn walk_expr(&mut self, _expr: &Expr) {}

    fn walk_local_var(&mut self, _local_var: &LocalVar) {}

    fn walk_comment(&mut self, _text: &str) {}

    fn walk_label(&mut self, _label: &str) {}

    fn walk_inhale(&mut self, expr: &Expr, _pos: &Position) {
        self.walk_expr(expr);
    }

    fn walk_exhale(&mut self, expr: &Expr, _pos: &Position) {
        self.walk_expr(expr);
    }

    fn walk_assume(&mut self, expr: &Expr, _pos: &Position) {
        self.walk_expr(expr);
    }

    fn walk_assert(&mut self, expr: &Expr, _pos: &Position) {
        self.walk_expr(expr);
    }

    fn walk_refute(&mut self, expr: &Expr, _pos: &Position) {
        self.walk_expr(expr);
    }

    fn walk_method_call(&mut self, _method_name: &str, args: &[Expr], targets: &[LocalVar]) {
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
        args: &[Expr],
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
        args: &[Expr],
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
        body: &[Stmt],
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

    fn walk_if(&mut self, g: &Expr, t: &[Stmt], e: &[Stmt]) {
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
        .map(|stmt| format!("{stmt}\n"))
        .collect::<String>()
}
