// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::foldunfold::perm::*;
use encoder::vir;
use encoder::vir::PermAmount;
use std::fmt;
use encoder::foldunfold::FoldUnfoldError;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Action {
    Fold(String, Vec<vir::Expr>, PermAmount, vir::MaybeEnumVariantIndex, vir::Position),
    Unfold(String, Vec<vir::Expr>, PermAmount, vir::MaybeEnumVariantIndex),
    /// The dropped perm and the missing permission that caused this
    /// perm to be dropped.
    Drop(Perm, Perm),
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
        }
    }

    pub fn to_expr(&self, inner_expr: vir::Expr) -> Result<vir::Expr, FoldUnfoldError> {
        match self {
            Action::Fold(ref pred, ref args, perm, ref variant, ref position) => {
                // Currently unsupported in Viper
                Err(FoldUnfoldError::RequiresFolding(
                    pred.clone(), args.clone(), *perm, variant.clone(), position.clone()
                ))
            }

            Action::Unfold(ref pred, ref args, perm, ref variant) => {
                Ok(vir::Expr::unfolding(
                    pred.clone(), args.clone(), inner_expr, *perm, variant.clone()))
            }

            Action::Drop(..) => Ok(inner_expr),
        }
    }
}

impl fmt::Display for Action {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Action::Fold(..) | Action::Unfold(..) => write!(f, "{}", self.to_stmt().to_string()),
            Action::Drop(ref perm, ref missing_perm) => {
                write!(f, "drop {} ({})", perm, missing_perm)
            }
        }
    }
}
