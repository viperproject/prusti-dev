// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use ::vir::polymorphic::*;
use log::debug;
use std::mem;

use crate::vir::optimizations::functions::Simplifier;

/// This optimization transformes ors were the RHS is impure into implications.
/// This happens in the case of an implication with a resource access predicate in the RHS.

pub fn simplify_expr(mut cfg: CfgMethod) -> CfgMethod {
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
