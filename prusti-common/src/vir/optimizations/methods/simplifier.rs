// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use log::debug;
use std::mem;
use vir::polymorphic::*;

use crate::vir::optimizations::functions::Simplifier;

/// This optimization simplifies all expressions in a method.
/// It is required when resource access predicates appear on the RHS of
/// implications as implications are transformed into ors which need to be
/// transformed back into implications otherwise, we would have an impure
/// expression in ors which is disallowed in Viper.

pub fn simplify_exprs(mut cfg: CfgMethod) -> CfgMethod {
    debug!("Simplifying exprs in {}", cfg.name());
    let mut sentinel_stmt = Stmt::comment("moved out stmt");
    for block in &mut cfg.basic_blocks {
        for stmt in &mut block.stmts {
            mem::swap(&mut sentinel_stmt, stmt);
            sentinel_stmt = sentinel_stmt.simplify();
            mem::swap(&mut sentinel_stmt, stmt);
        }
    }
    cfg
}

struct StmtSimplifier;

impl Simplifier for Stmt {
    fn simplify(self) -> Self {
        let mut folder = StmtSimplifier;
        folder.fold(self)
    }
}

impl StmtFolder for StmtSimplifier {
    fn fold_expr(&mut self, expr: Expr) -> Expr {
        expr.simplify()
    }
}
