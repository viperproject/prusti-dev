// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Inliner of pure functions.

use std::collections::HashMap;
use std::mem;
use super::super::super::ast;

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
/// The optimisation is performed until a fix-point.
pub fn inline_constant_functions(mut functions: Vec<ast::Function>) -> Vec<ast::Function> {
    trace!("[enter] purify_constant_functions");
    let mut pure_functions = Vec::new();
    let mut non_pure_functions = Vec::new();
    let mut pure_function_map = HashMap::new();
    let mut changed = true;
    while changed {
        changed = false;
        for mut function in functions.into_iter() {
            if let Some(body) = try_purify(&mut function) {
                pure_function_map.insert(function.name.clone(), body);
                pure_functions.push(function);
                changed = true;
            } else {
                non_pure_functions.push(function);
            }
        }
        for function in &mut non_pure_functions {
            function.inline_constant_functions(&pure_function_map);
        }
        functions = non_pure_functions;
        non_pure_functions = Vec::new();
    }
    functions.extend(pure_functions);
    functions
}

/// Try converting the function to pure by removing permissions from the
/// precondition. Returns true if successful.
fn try_purify(function: &mut ast::Function) -> Option<ast::Expr> {
    trace!("[enter] try_purify(name={})", function.name);
    if function.has_constant_body() && function.pres.len() == 1 {
        match function.pres[0] {
            ast::Expr::PredicateAccessPredicate(_, _, _, _) |
            ast::Expr::FieldAccessPredicate(_, _, _) => {
                function.pres.clear();
                return function.body.clone();
            },
            _ => {},
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
            ast::Expr::Const(_, _) =>
                true,
            ast::Expr::UnaryOp(_, box subexpr, _) =>
                subexpr.is_constant(),
            ast::Expr::BinOp(_, box subexpr1, box subexpr2, _) =>
                subexpr1.is_constant() && subexpr2.is_constant(),
            _ => false,
        }
    }
}

trait ConstantFunctionInliner {

    /// Replace ``unfolding P(...) in f(...)`` with ``f(...)`` if ``f`` is pure.
    fn inline_constant_functions(
        &mut self,
        pure_function_map: &HashMap<String, ast::Expr>,
    );

}

impl ConstantFunctionInliner for ast::Function {

    fn inline_constant_functions(
        &mut self,
        pure_function_map: &HashMap<String, ast::Expr>,
    ) {
        match self.body {
            Some(ref mut body) => body.inline_constant_functions(pure_function_map),
            None => {},
        }
    }

}

fn is_constant_function_call(
    expr: &ast::Expr,
    pure_function_map: &HashMap<String, ast::Expr>
) -> Option<ast::Expr> {
    match expr {
        ast::Expr::Unfolding(_, _, box ast::Expr::FuncApp(name, _, _, _, _), _, _) => {
            pure_function_map.get(name).cloned()
        },
        _ => {
            None
        },
    }
}

impl ConstantFunctionInliner for ast::Expr {

    fn inline_constant_functions(
        &mut self,
        pure_function_map: &HashMap<String, ast::Expr>,
    ) {
        if let Some(mut expr) = is_constant_function_call(self, pure_function_map) {
            mem::swap(self, &mut expr);
        } else {
            match self {
                ast::Expr::UnaryOp(_, box subexpr, _) => {
                    subexpr.inline_constant_functions(pure_function_map)
                },
                ast::Expr::BinOp(_, box subexpr1, box subexpr2, _) => {
                    subexpr1.inline_constant_functions(pure_function_map);
                    subexpr2.inline_constant_functions(pure_function_map);
                },
                _ => {},
            }
        }
    }

}
