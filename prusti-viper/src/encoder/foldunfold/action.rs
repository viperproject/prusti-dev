// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::foldunfold::perm::*;
use encoder::vir;
use encoder::vir::{PermAmount, FoldingBehaviour, Position};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Action {
    Fold(String, Vec<vir::Expr>, PermAmount, vir::MaybeEnumVariantIndex, vir::Position),
    Unfold(String, Vec<vir::Expr>, PermAmount, vir::MaybeEnumVariantIndex),
    /// The dropped perm and the missing permission that caused this
    /// perm to be dropped.
    Drop(Perm, Perm),
    Assertion(vir::Expr),
    /// An unfold that must be directly folded back.
    /// This is necessary when dealing with quantified predicate accesses.
    /// TODO: example
    TemporaryUnfold(String, Vec<vir::Expr>, PermAmount, vir::MaybeEnumVariantIndex),
}

impl Action {
    pub fn to_stmt(&self) -> vir::Stmt {
        match self {
            Action::Fold(ref pred, ref args, perm_amount, ref variant, ref pos) => {
                vir::Stmt::Fold(
                    pred.clone(),
                    args.clone(),
                    *perm_amount,
                    variant.clone(),
                    pos.clone()
                )
            }
            Action::Unfold(ref pred, ref args, perm_amount, ref variant) => {
                vir::Stmt::Unfold(pred.clone(), args.clone(), *perm_amount, variant.clone())
            }
            Action::Drop(..) => vir::Stmt::comment(self.to_string()),
            Action::Assertion(assertion) => vir::Stmt::Assert(assertion.clone(), FoldingBehaviour::Expr, Position::default()),
            Action::TemporaryUnfold(..) =>
                // TODO: "use ... instead"
                panic!("A temporary unfold has no equivalent in vir::Stmt")
        }
    }

    pub fn to_expr(&self, inner_expr: vir::Expr) -> vir::Expr {
        match self {
            Action::Fold(ref _pred, ref _args, _perm, ref _variant, _) => {
                // Currently unsupported in Viper
                unimplemented!("action {}", self)
            }

            Action::Unfold(ref pred, ref args, perm, ref variant)
            | Action::TemporaryUnfold(ref pred, ref args, perm, ref variant) => {
                vir::Expr::unfolding(
                    pred.clone(), args.clone(), inner_expr, *perm, variant.clone())
            }

            Action::Drop(..) => inner_expr,

            Action::Assertion(_) => inner_expr, // The assertion has already been taken care of.
        }
    }
}

pub fn actions_to_stmts(actions: Vec<Action>) -> (Vec<vir::Stmt>, Vec<vir::Stmt>) {
    let mut perms = Vec::new();
    let mut to_fold_back = Vec::new();
    for action in actions {
        match action {
            Action::TemporaryUnfold(pred_name, args, perm, variant) => {
                perms.push(vir::Stmt::Unfold(pred_name.clone(), args.clone(), perm, variant.clone()));
                to_fold_back.push(vir::Stmt::Fold(pred_name, args, perm, variant, Position::default()));
            }
            other => perms.push(other.to_stmt()),
        }
    }
    (perms, to_fold_back)
}

impl fmt::Display for Action {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Action::Fold(..) | Action::Unfold(..) => write!(f, "{}", self.to_stmt().to_string()),
            Action::Drop(ref perm, ref missing_perm) => {
                write!(f, "drop {} ({})", perm, missing_perm)
            }
            Action::Assertion(assertion) => write!(f, "assert {}", assertion),
            Action::TemporaryUnfold(ref pred_name, ref args, perm, ref variant) =>
                write!(
                    f, "{}",
                    vir::Stmt::Unfold(pred_name.clone(), args.clone(), *perm, variant.clone())
                        .to_string()
                )
        }
    }
}
