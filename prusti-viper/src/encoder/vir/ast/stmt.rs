// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// TODO: fix later
#![allow(deprecated)]

use std::fmt;
use encoder::vir::ast::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Stmt {
    Comment(String),
    Label(String),
    Inhale(Expr),
    Exhale(Expr, Position),
    Assert(Expr, Position),
    /// MethodCall: method_name, args, targets
    MethodCall(String, Vec<Expr>, Vec<LocalVar>),
    Assign(Expr, Expr, AssignKind),
    Fold(String, Vec<Expr>, Frac),
    Unfold(String, Vec<Expr>, Frac),
    /// Obtain: conjunction of Expr::PredicateAccessPredicate or Expr::FieldAccessPredicate
    /// They will be used by the fold/unfold algorithm
    Obtain(Expr),
    /// WeakObtain: conjunction of Expr::PredicateAccessPredicate or Expr::FieldAccessPredicate
    /// They will be used by the fold/unfold algorithm
    #[deprecated]
    WeakObtain(Expr),
    /// Havoc: used for emptying the fold/unfold state
    #[deprecated]
    Havoc,
    /// Mark a CFG point in which all current permissions are framed out
    /// They will be used by the fold/unfold algorithm
    BeginFrame,
    /// Mark a CFG point in which all the permissions of a corresponding `BeginFrame` are framed in
    /// They will be used by the fold/unfold algorithm
    EndFrame,
    /// Move permissions from a place to another.
    /// This is used to restore permissions in the fold/unfold state when a loan expires.
    TransferPerm(Expr, Expr),
    /// An `if` statement: the guard, the 'then' branch, the 'else' branch
    /// Note: this is only used to restore permissions of expiring loans, so the fold/unfold
    /// algorithms threats this statement (and statements in the branches) in a very special way.
    ExpireBorrowsIf(Expr, Vec<Stmt>, Vec<Stmt>),
    /// A statement that informs the fold/unfold that we finished restoring a DAG of expiring loans
    /// The argument is a list of the locations that are restored
    StopExpiringLoans(Vec<Expr>),
    /// Package a Magic Wand
    /// Arguments: the magic wand, then the package statements.
    PackageMagicWand(Expr, Vec<Stmt>, Position),
    /// Apply a Magic Wand.
    /// Arguments: the magic wand.
    ApplyMagicWand(Expr),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssignKind {
    /// Encodes a Rust copy.
    /// This assignment can be used iff the Viper type of the `lhs` and `rhs` is *not* Ref.
    Copy,
    /// Encodes a Rust move. The permissions in the rhs move to the `lhs`.
    /// This assignment can be used iff the Viper type of the `lhs` and `rhs` is Ref.
    Move,
    /// Encodes the initialization of a mutable borrow.
    /// The permissions in the `rhs` move to the `lhs`, but they can be restored when the borrow dies.
    MutableBorrow
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Stmt::Comment(ref comment) => write!(f, "// {}", comment),
            Stmt::Label(ref label) => write!(f, "label {}", label),
            Stmt::Inhale(ref expr) => write!(f, "inhale {}", expr),
            Stmt::Exhale(ref expr, _) => write!(f, "exhale {}", expr),
            Stmt::Assert(ref expr, _) => write!(f, "assert {}", expr),
            Stmt::MethodCall(ref name, ref args, ref vars) => write!(
                f, "{} := {}({})",
                vars.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
                name,
                args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
            ),
            Stmt::Assign(ref lhs, ref rhs, kind) => match kind {
                AssignKind::Move => write!(f, "{} := move {}", lhs, rhs),
                AssignKind::Copy => write!(f, "{} := copy {}", lhs, rhs),
                AssignKind::MutableBorrow => write!(f, "{} := borrow {}", lhs, rhs),
            },

            Stmt::Fold(ref pred_name, ref args, frac) => if *frac == Frac::one() {
                write!(
                    f, "fold {}({})",
                    pred_name,
                    args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
                )
            } else {
                write!(
                    f, "fold acc({}({}), {})",
                    pred_name,
                    args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
                    frac,
                )
            },

            Stmt::Unfold(ref pred_name, ref args, frac) => if *frac == Frac::one() {
                write!(
                    f, "unfold {}({})",
                    pred_name,
                    args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
                )
            } else {
                write!(
                    f, "unfold acc({}({}), {})",
                    pred_name,
                    args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
                    frac,
                )
            },

            Stmt::Obtain(ref expr) => write!(f, "obtain {}", expr),

            Stmt::WeakObtain(ref expr) => write!(f, "weak obtain {}", expr),

            Stmt::Havoc => write!(f, "havoc"),

            Stmt::BeginFrame => write!(f, "begin frame"),

            Stmt::EndFrame => write!(f, "end frame"),

            Stmt::TransferPerm(ref lhs, ref rhs) => write!(f, "transfer perm {} --> {}", lhs, rhs),

            Stmt::ExpireBorrowsIf(ref guard, ref then_stmts, ref else_stmts) => {
                write!(f, "expire borrows if {} {{", guard)?;
                if !then_stmts.is_empty() {
                    write!(f, "\n")?;
                }
                for stmt in then_stmts.iter() {
                    writeln!(f, "    {}", stmt.to_string().replace("\n", "\n    "))?;
                }
                write!(f, "}} else {{")?;
                if !else_stmts.is_empty() {
                    write!(f, "\n")?;
                }
                for stmt in else_stmts.iter() {
                    writeln!(f, "    {}", stmt.to_string().replace("\n", "\n    "))?;
                }
                write!(f, "}}")
            }

            Stmt::StopExpiringLoans(ref restored) => write!(
                f,
                "stop expiring borrows {{{}}}",
                restored.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ")
            ),

            Stmt::PackageMagicWand(Expr::MagicWand(ref lhs, ref rhs), ref package_stmts, _position) => {
                writeln!(f, "package {}", lhs)?;
                writeln!(f, "    --* {}", rhs)?;
                write!(f, "{{")?;
                if !package_stmts.is_empty() {
                    write!(f, "\n")?;
                }
                for stmt in package_stmts.iter() {
                    writeln!(f, "    {}", stmt.to_string().replace("\n", "\n    "))?;
                }
                write!(f, "}}")
            }

            Stmt::ApplyMagicWand(Expr::MagicWand(ref lhs, ref rhs)) => {
                writeln!(f, "apply {} --* {}", lhs, rhs)
            }

            ref x => unimplemented!("{:?}", x),
        }
    }
}

impl Stmt {
    pub fn is_comment(&self) -> bool {
        match self {
            Stmt::Comment(_) => true,
            _ => false
        }
    }

    pub fn comment<S: ToString>(comment: S) -> Self {
        Stmt::Comment(comment.to_string())
    }

    pub fn obtain_acc(place: Expr, pos: Position) -> Self {
        assert!(!place.is_local());
        Stmt::Obtain(
            Expr::FieldAccessPredicate(
                box place,
                Frac::one(),
                pos
            )
        )
    }

    pub fn obtain_pred(place: Expr, pos: Position) -> Self {
        let predicate_name = place.typed_ref_name().unwrap();
        Stmt::Obtain(
            Expr::PredicateAccessPredicate(
                predicate_name,
                vec![ place ],
                Frac::one(),
                pos
            )
        )
    }

    pub fn fold_pred(place: Expr, frac: Frac) -> Self {
        let predicate_name = place.typed_ref_name().unwrap();
        Stmt::Fold(
            predicate_name,
            vec![
                place.into()
            ],
            frac
        )
    }

    pub fn unfold_pred(place: Expr, frac: Frac) -> Self {
        let predicate_name = place.typed_ref_name().unwrap();
        Stmt::Unfold(
            predicate_name,
            vec![ place ],
            frac
        )
    }

    pub fn package_magic_wand(lhs: Expr, rhs: Expr, stmts: Vec<Stmt>, pos: Position) -> Self {
        Stmt::PackageMagicWand(
            Expr::MagicWand(box lhs, box rhs, pos.clone()),
            stmts,
            pos
        )
    }

    pub fn apply_magic_wand(lhs: Expr, rhs: Expr, pos: Position) -> Self {
        Stmt::ApplyMagicWand(
            Expr::MagicWand(box lhs, box rhs, pos),
        )
    }
}

pub trait StmtFolder {
    fn fold(&mut self, e: Stmt) -> Stmt {
        match e {
            Stmt::Comment(s) => self.fold_comment(s),
            Stmt::Label(s) => self.fold_label(s),
            Stmt::Inhale(e) => self.fold_inhale(e),
            Stmt::Exhale(e, p) => self.fold_exhale(e, p),
            Stmt::Assert(e, p) => self.fold_assert(e, p),
            Stmt::MethodCall(s, ve, vv) => self.fold_method_call(s, ve, vv),
            Stmt::Assign(p, e, k) => self.fold_assign(p, e, k),
            Stmt::Fold(s, ve, frac) => self.fold_fold(s, ve, frac),
            Stmt::Unfold(s, ve, frac) => self.fold_unfold(s, ve, frac),
            Stmt::Obtain(e) => self.fold_obtain(e),
            Stmt::WeakObtain(e) => self.fold_weak_obtain(e),
            Stmt::Havoc => self.fold_havoc(),
            Stmt::BeginFrame => self.fold_begin_frame(),
            Stmt::EndFrame => self.fold_end_frame(),
            Stmt::TransferPerm(a, b) => self.fold_transfer_perm(a, b),
            Stmt::ExpireBorrowsIf(g, t, e) => self.fold_expire_borrows_if(g, t, e),
            Stmt::StopExpiringLoans(a) => self.fold_stop_expiring_borrows(a),
            Stmt::PackageMagicWand(w, s, p) => self.fold_package_magic_wand(w, s, p),
            Stmt::ApplyMagicWand(w) => self.fold_apply_magic_wand(w),
        }
    }

    fn fold_expr(&mut self, e: Expr) -> Expr {
        e
    }

    fn fold_comment(&mut self, s: String) -> Stmt {
        Stmt::Comment(s)
    }

    fn fold_label(&mut self, s: String) -> Stmt {
        Stmt::Label(s)
    }

    fn fold_inhale(&mut self, e: Expr) -> Stmt {
        Stmt::Inhale(self.fold_expr(e))
    }

    fn fold_exhale(&mut self, e: Expr, p: Position) -> Stmt {
        Stmt::Exhale(self.fold_expr(e), p)
    }

    fn fold_assert(&mut self, e: Expr, p: Position) -> Stmt {
        Stmt::Assert(self.fold_expr(e), p)
    }

    fn fold_method_call(&mut self, s: String, ve: Vec<Expr>, vv: Vec<LocalVar>) -> Stmt {
        Stmt::MethodCall(s, ve.into_iter().map(|e| self.fold_expr(e)).collect(), vv)
    }

    fn fold_assign(&mut self, p: Expr, e: Expr, k: AssignKind) -> Stmt {
        Stmt::Assign(self.fold_expr(p), self.fold_expr(e), k)
    }

    fn fold_fold(&mut self, s: String, ve: Vec<Expr>, frac: Frac) -> Stmt {
        Stmt::Fold(s, ve.into_iter().map(|e| self.fold_expr(e)).collect(), frac)
    }

    fn fold_unfold(&mut self, s: String, ve: Vec<Expr>, frac: Frac) -> Stmt {
        Stmt::Unfold(s, ve.into_iter().map(|e| self.fold_expr(e)).collect(), frac)
    }

    fn fold_obtain(&mut self, e: Expr) -> Stmt {
        Stmt::Obtain(self.fold_expr(e))
    }

    fn fold_weak_obtain(&mut self, e: Expr) -> Stmt {
        Stmt::WeakObtain(self.fold_expr(e))
    }

    fn fold_havoc(&mut self) -> Stmt {
        Stmt::Havoc
    }

    fn fold_begin_frame(&mut self) -> Stmt {
        Stmt::BeginFrame
    }

    fn fold_end_frame(&mut self) -> Stmt {
        Stmt::EndFrame
    }

    fn fold_transfer_perm(&mut self, a: Expr, b: Expr) -> Stmt {
        Stmt::TransferPerm(self.fold_expr(a), self.fold_expr(b))
    }

    fn fold_expire_borrows_if(&mut self, g: Expr, t: Vec<Stmt>, e: Vec<Stmt>) -> Stmt {
        Stmt::ExpireBorrowsIf(
            self.fold_expr(g),
            t.into_iter().map(|x| self.fold(x)).collect(),
            e.into_iter().map(|x| self.fold(x)).collect()
        )
    }

    fn fold_stop_expiring_borrows(&mut self, a: Vec<Expr>) -> Stmt {
        Stmt::StopExpiringLoans(
            a.into_iter().map(|x| self.fold_expr(x)).collect()
        )
    }

    fn fold_package_magic_wand(&mut self, w: Expr, s: Vec<Stmt>, p: Position) -> Stmt {
        Stmt::PackageMagicWand(
            self.fold_expr(w),
            s.into_iter().map(|x| self.fold(x)).collect(),
            p
        )
    }

    fn fold_apply_magic_wand(&mut self, w: Expr) -> Stmt {
        Stmt::ApplyMagicWand(
            self.fold_expr(w),
        )
    }
}
