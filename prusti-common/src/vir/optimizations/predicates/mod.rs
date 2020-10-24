use std::collections::BTreeSet;
use vir::{ast::*, cfg::CfgMethod};

use vir::CfgBlock;

use crate::vir::{cfg, Successor};

mod delete_unused_predicates;
mod remove_not_needed_bodies;

pub use self::delete_unused_predicates::delete_unused_predicates;

pub use self::remove_not_needed_bodies::remove_not_needed_bodies;

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
