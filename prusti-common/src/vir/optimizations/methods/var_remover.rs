// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Optimization that removes unused temporary variables.

use crate::vir::polymorphic_vir::{ast, cfg};
use std::{collections::HashSet, mem};

/// Remove unused temporary variables and related inhale statements.
pub fn remove_unused_vars(mut method: cfg::CfgMethod) -> cfg::CfgMethod {
    let mut collector = UsedVarCollector {
        used_vars: HashSet::new(),
    };
    method.walk_statements(|stmt| {
        ast::StmtWalker::walk(&mut collector, stmt);
    });
    method.walk_successors(|successor| match successor {
        cfg::Successor::Undefined | cfg::Successor::Return | cfg::Successor::Goto(_) => {}
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
    let mut remover = UnusedVarRemover { unused_vars };
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
        _predicate_access_predicate: &ast::PredicateAccessPredicate,
    ) {
    }
    fn walk_field_access_predicate(&mut self, _field_access_predicate: &ast::FieldAccessPredicate) {
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
        ast::PackageMagicWand {
            magic_wand,
            package_stmts,
            variables,
            ..
        }: &ast::PackageMagicWand,
    ) {
        self.walk_expr(magic_wand);
        for statement in package_stmts {
            self.walk(statement);
        }
        for var in variables {
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
        ast::PredicateAccessPredicate {
            predicate_type,
            argument,
            permission,
            position,
        }: ast::PredicateAccessPredicate,
    ) -> ast::Expr {
        if let box ast::Expr::Local(ast::Local {
            variable: ref var, ..
        }) = argument
        {
            if self.unused_vars.contains(var) {
                return true.into();
            }
        }
        ast::Expr::PredicateAccessPredicate(ast::PredicateAccessPredicate {
            predicate_type,
            argument,
            permission,
            position,
        })
    }
    fn fold_field_access_predicate(
        &mut self,
        ast::FieldAccessPredicate {
            base,
            permission,
            position,
        }: ast::FieldAccessPredicate,
    ) -> ast::Expr {
        let var = base.get_base();
        if self.unused_vars.contains(&var) {
            return true.into();
        }
        ast::Expr::FieldAccessPredicate(ast::FieldAccessPredicate {
            base,
            permission,
            position,
        })
    }
}

impl ast::StmtFolder for UnusedVarRemover {
    fn fold_expr(&mut self, e: ast::Expr) -> ast::Expr {
        ast::ExprFolder::fold(self, e)
    }
}
