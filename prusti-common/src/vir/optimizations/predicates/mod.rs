// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::vir::{ast::*, cfg, cfg::CfgMethod, Successor};

mod delete_unused_predicates;
mod remove_unnecessary_bodies;

pub use self::{
    delete_unused_predicates::delete_unused_predicates,
    remove_unnecessary_bodies::remove_unnecessary_bodies,
};

/// Walks all Statements and Expressions in the provided methods
fn walk_methods(methods: &[CfgMethod], walker: &mut (impl StmtWalker + ExprWalker)) {
    for method in methods {
        method.walk_statements(|stmt| {
            StmtWalker::walk(walker, stmt);
        });
        method.walk_successors(|successor| match successor {
            cfg::Successor::Undefined | cfg::Successor::Return | cfg::Successor::Goto(_) => {}
            cfg::Successor::GotoSwitch(conditional_targets, _) => {
                for (expr, _) in conditional_targets {
                    ExprWalker::walk(walker, expr);
                }
            }
        });
    }
}

/// Walks all Expressions in the provided functions (including pre and post condidions)
fn walk_functions(functions: &[Function], walker: &mut (impl ExprWalker)) {
    for function in functions {
        for e in &function.pres {
            ExprWalker::walk(walker, e);
        }

        for e in &function.posts {
            ExprWalker::walk(walker, e);
        }

        for e in &function.body {
            ExprWalker::walk(walker, e);
        }
    }
}
