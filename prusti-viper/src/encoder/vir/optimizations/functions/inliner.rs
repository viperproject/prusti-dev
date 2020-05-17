// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Inliner of pure functions.

use super::super::super::ast;
use super::super::super::cfg;
use std::collections::HashMap;
use std::mem;

/// Convert functions whose body does not depend on arguments such as
///
/// ```viper
/// function foo(this: Ref): Bool
///     requires Foo(this)
/// {
///     true
/// }
/// ```
///
/// to pure functions:
///
/// ```viper
/// function foo(this: Ref): Bool
/// {
///     true
/// }
/// ```
///
/// And then inline them on call sites.
///
/// The optimization is performed until a fix-point.
pub fn inline_constant_functions(
    mut methods: Vec<cfg::CfgMethod>,
    mut functions: Vec<ast::Function>
) -> (Vec<cfg::CfgMethod>, Vec<ast::Function>) {
    trace!("[enter] purify_constant_functions");
    let mut non_pure_functions = Vec::new();
    let mut pure_function_map = HashMap::new();
    let mut changed = true;
    while changed {
        changed = false;
        for mut function in functions.into_iter() {
            if let Some(body) = try_purify(&mut function) {
                pure_function_map.insert(function.name.clone(), body);
                changed = true;
            } else {
                non_pure_functions.push(function);
            }
        }
        functions = non_pure_functions
            .into_iter()
            .map(|function| inline_into(function, &pure_function_map))
            .collect();
        non_pure_functions = Vec::new();
    }
    methods = inline_into_methods(methods, pure_function_map);
    (methods, functions)
}

/// Try converting the function to pure by removing permissions from the
/// precondition. Returns true if successful.
fn try_purify(function: &mut ast::Function) -> Option<ast::Expr> {
    trace!("[enter] try_purify(name={})", function.name);
    if function.has_constant_body() {
        if function.pres.iter().all(|cond| cond.is_only_permissions()) &&
            function.posts.is_empty() {

            function.pres.clear();
            return function.body.clone();
        }
    }
    None
}

impl ast::Function {
    /// Does the function has a body that does not depend neither on
    /// function parameters nor on the heap?
    fn has_constant_body(&self) -> bool {
        match self.body {
            Some(ref expr) => expr.is_constant(),
            None => false,
        }
    }
}

impl ast::Expr {
    /// Is this expression a constant?
    fn is_constant(&self) -> bool {
        match self {
            ast::Expr::Const(_, _) => true,
            ast::Expr::UnaryOp(_, box subexpr, _) => subexpr.is_constant(),
            ast::Expr::BinOp(_, box subexpr1, box subexpr2, _) => {
                subexpr1.is_constant() && subexpr2.is_constant()
            }
            _ => false,
        }
    }
}

/// Inline all calls to constant functions.
struct ConstantFunctionInliner<'a> {
    pure_function_map: &'a HashMap<String, ast::Expr>,
}

fn inline_into(
    mut function: ast::Function,
    pure_function_map: &HashMap<String, ast::Expr>,
) -> ast::Function {
    function.body = function.body.map(|body| {
        let mut inliner = ConstantFunctionInliner {
            pure_function_map,
        };
        ast::ExprFolder::fold(&mut inliner, body)
    });
    function
}

impl<'a> ast::StmtFolder for ConstantFunctionInliner<'a> {
    fn fold_expr(&mut self, expr: ast::Expr) -> ast::Expr {
        ast::ExprFolder::fold(self, expr)
    }
}

impl<'a> ast::ExprFolder for ConstantFunctionInliner<'a> {
    fn fold_func_app(
        &mut self,
        name: String,
        args: Vec<ast::Expr>,
        formal_args: Vec<ast::LocalVar>,
        return_type: ast::Type,
        pos: ast::Position,
    ) -> ast::Expr {
        if self.pure_function_map.contains_key(&name) {
            self.pure_function_map[&name].clone()
        } else {
            ast::Expr::FuncApp(
                name,
                args.into_iter().map(|e| self.fold(e)).collect(),
                formal_args,
                return_type,
                pos
            )
        }
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
        let body = self.fold_boxed(expr);
        if body.is_constant() {
            *body
        } else {
            ast::Expr::Unfolding(
                name,
                args.into_iter().map(|e| self.fold(e)).collect(),
                body,
                perm,
                variant,
                pos,
            )
        }
    }

}

fn inline_into_methods(
    methods: Vec<cfg::CfgMethod>,
    pure_function_map: HashMap<String, ast::Expr>
) -> Vec<cfg::CfgMethod> {
    let mut inliner = ConstantFunctionInliner {
        pure_function_map: &pure_function_map,
    };
    methods
        .into_iter()
        .map(|mut method| {
            let mut sentinel_stmt = ast::Stmt::Comment(String::from("moved out stmt"));
            for block in &mut method.basic_blocks {
                for stmt in &mut block.stmts {
                    mem::swap(&mut sentinel_stmt, stmt);
                    sentinel_stmt = ast::StmtFolder::fold(&mut inliner, sentinel_stmt);
                    mem::swap(&mut sentinel_stmt, stmt);
                }
            }
            method
        })
        .collect()
}
