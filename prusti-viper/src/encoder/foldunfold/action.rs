// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::foldunfold::{perm::*, FoldUnfoldError};
use std::fmt;
use vir_crate::polymorphic::{self as vir, Expr, Fold, PermAmount, Stmt, Unfold};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[allow(clippy::large_enum_variant)]
pub enum Action {
    Fold(Fold),
    Unfold(Unfold),
    /// The dropped perm and the missing permission that caused this
    /// perm to be dropped.
    Drop(Perm, Perm),
}

impl Action {
    pub fn to_stmt(&self) -> vir::Stmt {
        match self {
            Action::Fold(fold) => vir::Stmt::Fold(fold.clone()),
            Action::Unfold(unfold) => vir::Stmt::Unfold(unfold.clone()),
            Action::Drop(..) => vir::Stmt::comment(self.to_string()),
        }
    }

    pub fn to_expr(&self, inner_expr: vir::Expr) -> Result<vir::Expr, FoldUnfoldError> {
        match self {
            Action::Fold(Fold {
                predicate,
                arguments,
                permission,
                enum_variant,
                position,
            }) => {
                // Currently unsupported in Viper
                Err(FoldUnfoldError::RequiresFolding(
                    predicate.clone(),
                    arguments.clone(),
                    *permission,
                    enum_variant.clone(),
                    *position,
                ))
            }

            Action::Unfold(Unfold {
                predicate,
                arguments,
                permission,
                enum_variant,
            }) => Ok(vir::Expr::unfolding(
                predicate.clone(),
                arguments.clone(),
                inner_expr,
                *permission,
                enum_variant.clone(),
            )),

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
