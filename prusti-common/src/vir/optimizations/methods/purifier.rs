// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Optimization that purifies heap allocated local variables into pure
//! local variables.
//!
//! For example, `_1.val_int` will become `_1i` where `_1i` is of type Int.

use crate::{
    config,
    vir::polymorphic_vir::{ast, cfg},
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{self, mem};

/// Purify vars.
pub fn purify_vars(mut method: cfg::CfgMethod) -> cfg::CfgMethod {
    let mut collector = VarCollector {
        all_vars: FxHashSet::default(),
        impure_vars: FxHashSet::default(),
        is_pure_context: false,
        replacements: FxHashMap::default(),
    };
    // Since we cannot purify the return value, mark it as impure.
    for return_var in method.get_formal_returns() {
        collector.impure_vars.insert(return_var.clone());
    }
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
    let impure_vars = &collector.impure_vars;
    let pure_vars = collector
        .all_vars
        .into_iter()
        .filter(|var| !impure_vars.contains(var))
        .collect();
    let mut purifier = VarPurifier {
        pure_vars,
        replacements: collector.replacements,
    };
    let mut sentinel_stmt = ast::Stmt::comment("moved out stmt");
    for block in &mut method.basic_blocks {
        for stmt in &mut block.stmts {
            mem::swap(&mut sentinel_stmt, stmt);
            sentinel_stmt = ast::StmtFolder::fold(&mut purifier, sentinel_stmt);
            mem::swap(&mut sentinel_stmt, stmt);
        }
    }
    // TODO: fold successors
    let fix_var = |var| {
        if purifier.pure_vars.contains(&var) {
            purifier.replacements[&var].clone()
        } else {
            var
        }
    };
    method.local_vars = method.local_vars.into_iter().map(fix_var).collect();
    method
}

fn is_purifiable_predicate(typ: &ast::Type) -> bool {
    typ.name() == "usize" || typ.name() == "isize"
}

fn is_purifiable_method(name: &str) -> bool {
    name == "builtin$havoc_ref"
}

/// Collects all variables that cannot be purified.
struct VarCollector {
    all_vars: FxHashSet<ast::LocalVar>,
    /// Vars that cannot be purified.
    impure_vars: FxHashSet<ast::LocalVar>,
    /// Are we in a pure context?
    is_pure_context: bool,
    /// Variable replacement map.
    replacements: FxHashMap<ast::LocalVar, ast::LocalVar>,
}

impl VarCollector {
    fn check_local_var(&mut self, local_var: &ast::LocalVar) {
        self.all_vars.insert(local_var.clone());
        if !self.is_pure_context {
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
        ast::PredicateAccessPredicate {
            predicate_type,
            box argument,
            ..
        }: &ast::PredicateAccessPredicate,
    ) {
        let old_pure_context = self.is_pure_context;
        if is_purifiable_predicate(predicate_type) {
            if let ast::Expr::Local(ast::Local { variable: var, .. }) = argument {
                let mut new_var = var.clone();
                let original = var.clone();
                let name = &predicate_type.name()[..];
                new_var.typ = match name {
                    "usize" => ast::Type::Int,
                    "isize" => ast::Type::Int,
                    x => unreachable!("{}", x),
                };
                self.replacements.insert(original, new_var);
                self.is_pure_context = true;
            }
        }
        self.walk(argument);
        self.is_pure_context = old_pure_context;
    }
    fn walk_unfolding(
        &mut self,
        ast::Unfolding {
            predicate,
            arguments,
            base,
            ..
        }: &ast::Unfolding,
    ) {
        let old_pure_context = self.is_pure_context;
        if is_purifiable_predicate(predicate) {
            if let ast::Expr::Local(_) = arguments[0] {
                self.is_pure_context = true;
            }
        }
        for arg in arguments {
            self.walk(arg);
        }
        self.walk(base);
        self.is_pure_context = old_pure_context;
    }
    fn walk_field(
        &mut self,
        ast::FieldExpr {
            box base, field, ..
        }: &ast::FieldExpr,
    ) {
        let old_pure_context = self.is_pure_context;
        if field.name == "val_int" {
            self.is_pure_context = true;
            if let ast::Expr::Local(ast::Local { variable: var, .. }) = base {
                let mut new_var = var.clone();
                let original = var.clone();
                new_var.typ = field.typ.clone();
                self.replacements.insert(original, new_var);
            }
        }
        self.walk(base);
        self.is_pure_context = old_pure_context;
    }
    fn walk_let_expr(
        &mut self,
        ast::LetExpr {
            variable,
            def,
            body,
            ..
        }: &ast::LetExpr,
    ) {
        self.walk(def);
        self.walk(body);
        // TODO: This is not bullet proof against name collisions.
        self.all_vars.remove(variable);
    }
    fn walk_forall(
        &mut self,
        ast::ForAll {
            variables, body, ..
        }: &ast::ForAll,
    ) {
        self.walk(body);
        for var in variables {
            // TODO: This is not bullet proof against name collisions.
            self.all_vars.remove(var);
        }
    }
}

impl ast::StmtWalker for VarCollector {
    fn walk_expr(&mut self, expr: &ast::Expr) {
        ast::ExprWalker::walk(self, expr);
    }
    fn walk_local_var(&mut self, local_var: &ast::LocalVar) {
        self.check_local_var(local_var);
    }
    fn walk_method_call(
        &mut self,
        ast::MethodCall {
            method_name,
            arguments,
            targets,
        }: &ast::MethodCall,
    ) {
        let old_pure_context = self.is_pure_context;
        if is_purifiable_method(method_name) {
            self.is_pure_context = true;
        }
        assert!(arguments.is_empty());
        for target in targets {
            self.walk_local_var(target);
        }
        self.is_pure_context = old_pure_context;
    }
    fn walk_unfold(
        &mut self,
        ast::Unfold {
            predicate,
            arguments,
            ..
        }: &ast::Unfold,
    ) {
        let old_pure_context = self.is_pure_context;
        if is_purifiable_predicate(predicate) {
            if let ast::Expr::Local(_) = arguments[0] {
                self.is_pure_context = true;
            }
        }
        for arg in arguments {
            self.walk_expr(arg);
        }
        self.is_pure_context = old_pure_context;
    }
    fn walk_fold(
        &mut self,
        ast::Fold {
            predicate,
            arguments,
            ..
        }: &ast::Fold,
    ) {
        let old_pure_context = self.is_pure_context;
        if is_purifiable_predicate(predicate) {
            if let ast::Expr::Local(_) = arguments[0] {
                self.is_pure_context = true;
            }
        }
        for arg in arguments {
            self.walk_expr(arg);
        }
        self.is_pure_context = old_pure_context;
    }
}

struct VarPurifier {
    pure_vars: FxHashSet<ast::LocalVar>,
    replacements: FxHashMap<ast::LocalVar, ast::LocalVar>,
}

impl VarPurifier {
    fn is_pure(&self, expr: &ast::Expr) -> bool {
        if let ast::Expr::Local(ast::Local { variable: var, .. }) = expr {
            self.pure_vars.contains(var)
        } else {
            false
        }
    }
    fn get_replacement(&self, expr: &ast::Expr) -> ast::Expr {
        let ast::Expr::Local(ast::Local {variable: var, position: pos}) = expr else { unreachable!() };
        let replacement = self
            .replacements
            .get(var)
            .unwrap_or_else(|| panic!("key: {var}"))
            .clone();
        ast::Expr::Local(ast::Local {
            variable: replacement,
            position: *pos,
        })
    }
    fn get_replacement_bounds(&self, predicate: &ast::Type, var_expr: &ast::Expr) -> ast::Expr {
        let replacement = self.get_replacement(var_expr);
        if config::check_overflows() {
            match predicate.name().as_ref() {
                "usize" => ast::Expr::and(
                    ast::Expr::ge_cmp(replacement.clone(), std::usize::MIN.into()),
                    ast::Expr::ge_cmp(std::usize::MAX.into(), replacement),
                ),
                "isize" => ast::Expr::and(
                    ast::Expr::ge_cmp(replacement.clone(), std::isize::MIN.into()),
                    ast::Expr::ge_cmp(std::isize::MAX.into(), replacement),
                ),
                _ => unreachable!(),
            }
        } else if config::encode_unsigned_num_constraint() {
            ast::Expr::ge_cmp(replacement, 0.into())
        } else {
            true.into()
        }
    }
}

impl ast::ExprFolder for VarPurifier {
    fn fold_local(&mut self, ast::Local { variable, position }: ast::Local) -> ast::Expr {
        assert!(!self.pure_vars.contains(&variable), "local_var: {variable}");
        ast::Expr::local_with_pos(variable, position)
    }
    fn fold_predicate_access_predicate(
        &mut self,
        ast::PredicateAccessPredicate {
            predicate_type,
            argument,
            permission,
            position,
        }: ast::PredicateAccessPredicate,
    ) -> ast::Expr {
        if is_purifiable_predicate(&predicate_type) && self.is_pure(&argument) {
            self.get_replacement_bounds(&predicate_type, &argument)
        } else {
            ast::Expr::PredicateAccessPredicate(ast::PredicateAccessPredicate {
                predicate_type,
                argument: self.fold_boxed(argument),
                permission,
                position,
            })
        }
    }
    fn fold_field_access_predicate(
        &mut self,
        ast::FieldAccessPredicate {
            base: receiver,
            permission,
            position,
        }: ast::FieldAccessPredicate,
    ) -> ast::Expr {
        if let box ast::Expr::Field(ast::FieldExpr {
            base: box ast::Expr::Local(ast::Local { variable: var, .. }),
            ..
        }) = &receiver
        {
            if self.pure_vars.contains(var) {
                return true.into();
            }
        }
        ast::Expr::FieldAccessPredicate(ast::FieldAccessPredicate {
            base: self.fold_boxed(receiver),
            permission,
            position,
        })
    }
    fn fold_unfolding(
        &mut self,
        ast::Unfolding {
            predicate,
            arguments,
            base,
            permission,
            variant,
            position,
        }: ast::Unfolding,
    ) -> ast::Expr {
        assert!(arguments.len() == 1);
        if is_purifiable_predicate(&predicate) && self.is_pure(&arguments[0]) {
            self.fold(*base)
        } else {
            ast::Expr::Unfolding(ast::Unfolding {
                predicate,
                arguments,
                base: self.fold_boxed(base),
                permission,
                variant,
                position,
            })
        }
    }
    fn fold_field(
        &mut self,
        ast::FieldExpr {
            base,
            field,
            position,
        }: ast::FieldExpr,
    ) -> ast::Expr {
        if self.is_pure(&base) {
            self.get_replacement(&base)
        } else {
            ast::Expr::Field(ast::FieldExpr {
                base: self.fold_boxed(base),
                field,
                position,
            })
        }
    }
}

impl ast::StmtFolder for VarPurifier {
    fn fold_expr(&mut self, e: ast::Expr) -> ast::Expr {
        ast::ExprFolder::fold(self, e)
    }

    fn fold_unfold(
        &mut self,
        ast::Unfold {
            predicate,
            arguments,
            permission,
            enum_variant,
        }: ast::Unfold,
    ) -> ast::Stmt {
        assert!(arguments.len() == 1);
        if is_purifiable_predicate(&predicate) && self.is_pure(&arguments[0]) {
            let new_expr = self.get_replacement_bounds(&predicate, &arguments[0]);
            ast::Stmt::Inhale(ast::Inhale { expr: new_expr })
        } else {
            ast::Stmt::Unfold(ast::Unfold {
                predicate,
                arguments: arguments.into_iter().map(|e| self.fold_expr(e)).collect(),
                permission,
                enum_variant,
            })
        }
    }

    fn fold_fold(
        &mut self,
        ast::Fold {
            predicate,
            arguments,
            permission,
            enum_variant,
            position,
        }: ast::Fold,
    ) -> ast::Stmt {
        assert!(arguments.len() == 1);
        if is_purifiable_predicate(&predicate) && self.is_pure(&arguments[0]) {
            let new_expr = self.get_replacement_bounds(&predicate, &arguments[0]);
            ast::Stmt::Assert(ast::Assert {
                expr: new_expr,
                position,
            })
        } else {
            ast::Stmt::Fold(ast::Fold {
                predicate,
                arguments: arguments.into_iter().map(|e| self.fold_expr(e)).collect(),
                permission,
                enum_variant,
                position,
            })
        }
    }

    fn fold_method_call(
        &mut self,
        ast::MethodCall {
            mut method_name,
            arguments,
            mut targets,
        }: ast::MethodCall,
    ) -> ast::Stmt {
        assert!(targets.len() == 1);
        if self.pure_vars.contains(&targets[0]) {
            let target = &targets[0];
            let replacement = self
                .replacements
                .get(target)
                .unwrap_or_else(|| panic!("key: {target}"))
                .clone();
            method_name = match replacement.typ {
                ast::Type::Int => "builtin$havoc_int".to_string(),
                ast::Type::Bool => "builtin$havoc_bool".to_string(),
                ast::Type::Float(ast::Float::F32) => "builtin$havoc_f32".to_string(),
                ast::Type::Float(ast::Float::F64) => "builtin$havoc_f64".to_string(),
                ast::Type::BitVector(value) => format!("builtin$havoc_{value}"),
                ast::Type::TypedRef(_) => "builtin$havoc_ref".to_string(),
                ast::Type::TypeVar(_) => "builtin$havoc_ref".to_string(),
                ast::Type::Domain(_)
                | ast::Type::Ref
                | ast::Type::Snapshot(_)
                | ast::Type::Seq(_)
                | ast::Type::Map(..) => unreachable!(),
            };
            targets = vec![replacement];
        }
        ast::Stmt::MethodCall(ast::MethodCall {
            method_name,
            arguments: arguments.into_iter().map(|e| self.fold_expr(e)).collect(),
            targets,
        })
    }
}
