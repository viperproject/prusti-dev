// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Optimization that removes unused temporary variables.

use crate::vir::polymorphic_vir::{ast, cfg, Const};

/// Remove trivial assertions:
/// * `assert true`
/// * `exhale true`
/// * `inhale true`
pub fn remove_trivial_assertions(mut method: cfg::CfgMethod) -> cfg::CfgMethod {
    method.retain_stmts(|stmt| {
        // Remove those statements marked with `false`
        !matches!(stmt,
            ast::Stmt::Assert( ast::Assert {
                expr: ast::Expr::Const( ast::ConstExpr {
                    value: Const::Bool(true),
                    ..}),
                ..}) |
            ast::Stmt::Exhale( ast::Exhale {
                expr: ast::Expr::Const( ast::ConstExpr {
                    value: Const::Bool(true),
                    ..}),
                ..}) |
            ast::Stmt::Inhale( ast::Inhale {
                expr: ast::Expr::Const( ast::ConstExpr {
                    value: Const::Bool(true),
                    ..}),
                })
        )
    });
    method
}
