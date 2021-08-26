// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Optimization that removes unused temporary variables.

use crate::vir::polymorphic_vir::{ast, cfg};
use std::collections::HashSet;
use std::mem;

/// Remove unused temporary variables and related inhale statements.
pub fn remove_unused_vars(mut method: cfg::CfgMethod) -> cfg::CfgMethod {
    let mut collector = UsedVarCollector {
        used_vars: HashSet::new(),
    };
    method.walk_statements(|stmt| {
        ast::StmtWalker::walk(&mut collector, stmt);
    });
    method.walk_successors(|successor| match successor {
        cfg::Successor::Undefined |
        cfg::Successor::Return |
        cfg::Successor::Goto(_) => {}
        cfg::Successor::GotoSwitch(conditional_targets, _) => {
            for (expr, _) in conditional_targets {
                ast::ExprWalker::walk(&mut collector, expr);
            }
        }
    });
    let mut unused_vars = HashSet::new();
    let mut used_vars = Vec::new();
    for local_var in method.local_vars {
        if collector.used_vars.contains(&local_var.name) {
            used_vars.push(local_var);
        } else {
            unused_vars.insert(local_var);
        }
    }
    method.local_vars = used_vars;
    let mut remover = UnusedVarRemover {
        unused_vars: unused_vars,
    };
    let mut sentinel_stmt = ast::Stmt::comment("moved out stmt");
    for block in &mut method.basic_blocks {
        for stmt in &mut block.stmts {
            mem::swap(&mut sentinel_stmt, stmt);
            sentinel_stmt = ast::StmtFolder::fold(&mut remover, sentinel_stmt);
            mem::swap(&mut sentinel_stmt, stmt);
        }
    }
    method
}

/// Collects all used variables. A variable is used if it is mentioned
/// somewhere not inside an access predicate.
struct UsedVarCollector {
    used_vars: HashSet<String>,
}

impl ast::ExprWalker for UsedVarCollector {
    fn walk_local_var(&mut self, local_var: &ast::LocalVar) {
        self.used_vars.insert(local_var.name.clone());
    }
    fn walk_predicate_access_predicate(
        &mut self,
        _typ: &ast::Type,
        _arg: &ast::Expr,
        _perm_amount: ast::PermAmount,
        _pos: &ast::Position,
    ) {
    }
    fn walk_field_access_predicate(
        &mut self,
        _expr: &ast::Expr,
        _perm_amount: ast::PermAmount,
        _pos: &ast::Position,
    ) {
    }
}

impl ast::StmtWalker for UsedVarCollector {
    fn walk_expr(&mut self, expr: &ast::Expr) {
        ast::ExprWalker::walk(self, expr);
    }
    fn walk_local_var(&mut self, local_var: &ast::LocalVar) {
        self.used_vars.insert(local_var.name.clone());
    }
    fn walk_package_magic_wand(
        &mut self,
        wand: &ast::Expr,
        body: &Vec<ast::Stmt>,
        _label: &str,
        vars: &[ast::LocalVar],
        _p: &ast::Position,
    ) {
        self.walk_expr(wand);
        for statement in body {
            self.walk(statement);
        }
        for var in vars {
            self.used_vars.remove(&var.name);
        }
    }
}

struct UnusedVarRemover {
    unused_vars: HashSet<ast::LocalVar>,
}

impl ast::ExprFolder for UnusedVarRemover {
    fn fold_predicate_access_predicate(
        &mut self,
        typ: ast::Type,
        arg: Box<ast::Expr>,
        perm_amount: ast::PermAmount,
        pos: ast::Position,
    ) -> ast::Expr {
        match arg {
            box ast::Expr::Local( ast::Local {variable: ref var, ..} ) => {
                if self.unused_vars.contains(var) {
                    return true.into();
                }
            }
            _ => {}
        }
        ast::Expr::PredicateAccessPredicate( ast::PredicateAccessPredicate {
            predicate_type: typ,
            argument: arg,
            permission: perm_amount,
            position: pos,
        })
    }
    fn fold_field_access_predicate(
        &mut self,
        expr: Box<ast::Expr>,
        perm_amount: ast::PermAmount,
        pos: ast::Position,
    ) -> ast::Expr {
        let var = expr.get_base();
        if self.unused_vars.contains(&var) {
            return true.into();
        }
        ast::Expr::FieldAccessPredicate( ast::FieldAccessPredicate {
            base: expr,
            permission: perm_amount,
            position: pos,
        })
    }
}

impl ast::StmtFolder for UnusedVarRemover {
    fn fold_expr(&mut self, e: ast::Expr) -> ast::Expr {
        ast::ExprFolder::fold(self, e)
    }
}
