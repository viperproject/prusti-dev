// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Optimisation that purifies heap allocated local variables into pure
//! local variables.
//!
//! For example, `_1.val_int` will become `_1i` where `_1i` is of type Int.

use super::super::super::ast;
use super::super::super::cfg;
use std::collections::{HashSet, HashMap};
use std::mem;

/// Purify vars.
pub fn purify_vars(mut method: cfg::CfgMethod) -> cfg::CfgMethod {
    let mut collector = VarCollector {
        all_vars: HashSet::new(),
        impure_vars: HashSet::new(),
        is_pure_context: false,
    };
    method.walk_statements(|stmt| {
        error!("stmt: {}", stmt);
        ast::StmtWalker::walk(&mut collector, stmt);
    });
    method.walk_successors(|successor| match successor {
        cfg::Successor::Undefined | cfg::Successor::Return |
        cfg::Successor::Goto(_) | cfg::Successor::BackEdge(_) => {}
        cfg::Successor::GotoSwitch(conditional_targets, _) => {
            for (expr, _) in conditional_targets {
                error!("target: {}", expr);
                ast::ExprWalker::walk(&mut collector, expr);
            }
        }
    });
    let impure_vars = &collector.impure_vars;
    let pure_vars = collector.all_vars
        .into_iter()
        .filter(|var| !impure_vars.contains(var))
        .collect();
    for var in &pure_vars {
        error!("pure var: {}", var);
    }
    let mut purifier = VarPurifier {
        pure_vars: pure_vars,
        replacements: HashMap::new(),
    };
    let mut sentinel_stmt = ast::Stmt::Comment(String::from("moved out stmt"));
    for block in &mut method.basic_blocks {
        for stmt in &mut block.stmts {
            mem::swap(&mut sentinel_stmt, stmt);
            sentinel_stmt = ast::StmtFolder::fold(&mut purifier, sentinel_stmt);
            mem::swap(&mut sentinel_stmt, stmt);
        }
    }
    // TODO: fold successors
    let fix_var = |var| {
        if purifier.replacements.contains_key(&var) {
            purifier.replacements[&var].clone()
        } else {
            var
        }
    };
    method.formal_args = method.formal_args.into_iter().map(fix_var).collect();
    method.formal_returns = method.formal_returns.into_iter().map(fix_var).collect();
    method.local_vars = method.local_vars.into_iter().map(fix_var).collect();
    method
}

fn is_purifiable_predicate(name: &str) -> bool {
    name == "usize"
}

/// Collects all variables that cannot be purified.
struct VarCollector {
    all_vars: HashSet<ast::LocalVar>,
    /// Vars that cannot be purified.
    impure_vars: HashSet<ast::LocalVar>,
    /// Are we in a pure context?
    is_pure_context: bool,
}

impl VarCollector {
    fn check_local_var(&mut self, local_var: &ast::LocalVar) {
        self.all_vars.insert(local_var.clone());
        if !self.is_pure_context {
            assert!(local_var.name != "_2");
            self.impure_vars.insert(local_var.clone());
        }
    }
}

impl ast::ExprWalker for VarCollector {
    fn walk_local_var(&mut self, local_var: &ast::LocalVar) {
        self.check_local_var(local_var);
    }
    fn walk_predicate_access_predicate(
        &mut self,
        name: &str,
        arg: &ast::Expr,
        _perm_amount: ast::PermAmount,
        _pos: &ast::Position
    ) {
        let old_pure_context = self.is_pure_context;
        if is_purifiable_predicate(&name) {
            if let ast::Expr::Local(_, _) = arg {
                self.is_pure_context = true;
            }
        }
        self.walk(arg);
        self.is_pure_context = old_pure_context;
    }
    fn walk_unfolding(
        &mut self,
        name: &str,
        args: &Vec<ast::Expr>,
        body: &ast::Expr,
        _perm: ast::PermAmount,
        _variant: &ast::MaybeEnumVariantIndex,
        _pos: &ast::Position
    ) {
        let old_pure_context = self.is_pure_context;
        if is_purifiable_predicate(&name) {
            if let ast::Expr::Local(_, _) = args[0] {
                self.is_pure_context = true;
            }
        }
        for arg in args {
            self.walk(arg);
        }
        self.walk(body);
        self.is_pure_context = old_pure_context;
    }
    fn walk_field(&mut self, receiver: &ast::Expr, field: &ast::Field, _pos: &ast::Position) {
        let old_pure_context = self.is_pure_context;
        if field.name == "val_int" {
            self.is_pure_context = true;
        }
        self.walk(receiver);
        self.is_pure_context = old_pure_context;
    }
}

impl ast::StmtWalker for VarCollector {
    fn walk_expr(&mut self, expr: &ast::Expr) {
        error!("expr: {}", expr);
        ast::ExprWalker::walk(self, expr);
    }
    fn walk_local_var(&mut self, local_var: &ast::LocalVar) {
        self.check_local_var(local_var);
    }
    fn walk_unfold(
        &mut self,
        predicate_name: &str,
        args: &Vec<ast::Expr>,
        _perm: &ast::PermAmount,
        _variant: &ast::MaybeEnumVariantIndex,
    ) {
        let old_pure_context = self.is_pure_context;
        if is_purifiable_predicate(predicate_name) {
            if let ast::Expr::Local(_, _) = args[0] {
                self.is_pure_context = true;
            }
        }
        for arg in args {
            self.walk_expr(arg);
        }
        self.is_pure_context = old_pure_context;
    }
    fn walk_fold(
        &mut self,
        predicate_name: &str,
        args: &Vec<ast::Expr>,
        _perm: &ast::PermAmount,
        _variant: &ast::MaybeEnumVariantIndex,
        _pos: &ast::Position,
    ) {
        let old_pure_context = self.is_pure_context;
        if is_purifiable_predicate(predicate_name) {
            if let ast::Expr::Local(_, _) = args[0] {
                self.is_pure_context = true;
            }
        }
        for arg in args {
            self.walk_expr(arg);
        }
        self.is_pure_context = old_pure_context;
    }
}

struct VarPurifier {
    pure_vars: HashSet<ast::LocalVar>,
    replacements: HashMap<ast::LocalVar, ast::LocalVar>,
}

impl VarPurifier {
    fn is_pure(&self, expr: &ast::Expr) -> bool {
        if let ast::Expr::Local(var, _) = expr {
            self.pure_vars.contains(var)
        } else {
            false
        }
    }
}

impl ast::ExprFolder for VarPurifier {
    fn fold_local(&mut self, local_var: ast::LocalVar, pos: ast::Position) -> ast::Expr {
        assert!(!self.pure_vars.contains(&local_var), "local_var: {}", local_var);
        ast::Expr::Local(local_var, pos)
    }
    fn fold_predicate_access_predicate(
        &mut self,
        name: String,
        arg: Box<ast::Expr>,
        perm_amount: ast::PermAmount,
        pos: ast::Position,
    ) -> ast::Expr {
        if is_purifiable_predicate(&name) && self.is_pure(&arg) {
            true.into()
        } else {
            ast::Expr::PredicateAccessPredicate(name, self.fold_boxed(arg), perm_amount, pos)
        }
    }
    fn fold_field_access_predicate(
        &mut self,
        receiver: Box<ast::Expr>,
        perm_amount: ast::PermAmount,
        pos: ast::Position
    ) -> ast::Expr {
        if let box ast::Expr::Field(box ast::Expr::Local(var, _), _, _) = &receiver {
            if self.pure_vars.contains(var) {
                return true.into();
            }
        }
        ast::Expr::FieldAccessPredicate(self.fold_boxed(receiver), perm_amount, pos)
    }
    fn fold_unfolding(
        &mut self,
        name: String,
        args: Vec<ast::Expr>,
        expr: Box<ast::Expr>,
        perm: ast::PermAmount,
        variant: ast::MaybeEnumVariantIndex,
        pos: ast::Position,
    ) -> ast::Expr {
        assert!(args.len() == 1);
        if is_purifiable_predicate(&name) && self.is_pure(&args[0]) {
            self.fold(*expr)
        } else  {
            ast::Expr::Unfolding(
                name,
                args,
                self.fold_boxed(expr),
                perm,
                variant,
                pos,
            )
        }
    }
    fn fold_field(
        &mut self,
        receiver: Box<ast::Expr>,
        field: ast::Field,
        pos: ast::Position
    ) -> ast::Expr {
        if self.is_pure(&receiver) {
            if let box ast::Expr::Local(mut var, _) = receiver {
                let original = var.clone();
                var.typ = field.typ;
                self.replacements.insert(original, var.clone());
                return ast::Expr::Local(var, pos);
            }
            unreachable!();
        }
        ast::Expr::Field(self.fold_boxed(receiver), field, pos)
    }
}

impl ast::StmtFolder for VarPurifier {
    fn fold_expr(&mut self, e: ast::Expr) -> ast::Expr {
        error!("expr: {}", e);
        ast::ExprFolder::fold(self, e)
    }

    fn fold_unfold(
        &mut self,
        predicate_name: String,
        args: Vec<ast::Expr>,
        perm_amount: ast::PermAmount,
        variant: ast::MaybeEnumVariantIndex,
    ) -> ast::Stmt {
        assert!(args.len() == 1);
        if is_purifiable_predicate(&predicate_name) && self.is_pure(&args[0]) {
            ast::Stmt::Inhale(true.into(), ast::FoldingBehaviour::Stmt)
        } else {
            ast::Stmt::Unfold(
                predicate_name,
                args.into_iter().map(|e| self.fold_expr(e)).collect(),
                perm_amount,
                variant,
            )
        }
    }

    fn fold_fold(
        &mut self,
        predicate_name: String,
        args: Vec<ast::Expr>,
        perm_amount: ast::PermAmount,
        variant: ast::MaybeEnumVariantIndex,
        pos: ast::Position
    ) -> ast::Stmt {
        assert!(args.len() == 1);
        if is_purifiable_predicate(&predicate_name) && self.is_pure(&args[0]) {
            ast::Stmt::Inhale(true.into(), ast::FoldingBehaviour::Stmt)
        } else {
            ast::Stmt::Fold(
                predicate_name,
                args.into_iter().map(|e| self.fold_expr(e)).collect(),
                perm_amount,
                variant,
                pos,
            )
        }
    }
}
