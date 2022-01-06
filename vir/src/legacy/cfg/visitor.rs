// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::legacy::{ast::*, cfg::method::*, to_string::ToString};
use std::fmt::Debug;

pub trait CheckNoOpAction {
    /// Is the action a no operation?
    fn is_noop(&self) -> bool;
}

pub trait SuccessorFolder {
    fn fold(&mut self, s: Successor) -> Successor {
        match s {
            Successor::Undefined => self.fold_undefined(),
            Successor::Return => self.fold_return(),
            Successor::Goto(target) => self.fold_goto(target),
            Successor::GotoSwitch(guarded_targets, default_target) => {
                self.fold_goto_switch(guarded_targets, default_target)
            }
        }
    }

    fn fold_expr(&mut self, expr: Expr) -> Expr {
        expr
    }

    fn fold_target(&mut self, target: CfgBlockIndex) -> CfgBlockIndex {
        target
    }

    fn fold_undefined(&mut self) -> Successor {
        Successor::Undefined
    }

    fn fold_return(&mut self) -> Successor {
        Successor::Undefined
    }

    fn fold_goto(&mut self, target: CfgBlockIndex) -> Successor {
        Successor::Goto(self.fold_target(target))
    }

    fn fold_goto_switch(
        &mut self,
        guarded_targets: Vec<(Expr, CfgBlockIndex)>,
        default_target: CfgBlockIndex,
    ) -> Successor {
        Successor::GotoSwitch(
            guarded_targets
                .into_iter()
                .map(|(cond, targ)| (self.fold_expr(cond), targ))
                .collect(),
            self.fold_target(default_target),
        )
    }
}

impl CfgMethod {
    pub fn walk_statements<F: FnMut(&Stmt)>(&self, mut walker: F) {
        for block in self.basic_blocks.iter() {
            for stmt in block.stmts.iter() {
                walker(stmt);
            }
        }
    }

    // TODO: maybe just let basic_blocks be public and modify those directly?
    pub fn patch_statements<E, F: FnMut(Stmt) -> Result<Stmt, E>>(
        mut self,
        mut walker: F,
    ) -> Result<Self, E> {
        for block in self.basic_blocks.iter_mut() {
            block.stmts = block
                .stmts
                .drain(..)
                .map(&mut walker)
                .collect::<Result<Vec<_>, _>>()?;
        }
        Ok(self)
    }

    pub fn walk_successors<F: FnMut(&Successor)>(&self, mut walker: F) {
        for block in self.basic_blocks.iter() {
            walker(&block.successor);
        }
    }

    /// Visit each expression used in a statement or successor.
    /// Note: sub-expressions of expressions will not be visited.
    pub fn walk_expressions<F: FnMut(&Expr)>(&self, mut walker: F) {
        struct ExprStmtWalker<'a, T: FnMut(&Expr)> {
            walker: &'a mut T,
        }
        impl<'a, T: FnMut(&Expr)> StmtWalker for ExprStmtWalker<'a, T> {
            fn walk_expr(&mut self, expr: &Expr) {
                (self.walker)(expr);
            }
        }
        let mut stmt_walker = ExprStmtWalker {
            walker: &mut walker,
        };
        self.walk_statements(|stmt| stmt_walker.walk(stmt));
        self.walk_successors(|succ| {
            if let Successor::GotoSwitch(targets, _) = succ {
                for (guard, _) in targets {
                    walker(guard);
                }
            }
        });
    }

    /// Remove all statements `s` such that `f(&s)` returns `false`
    pub fn retain_stmts<F: Fn(&Stmt) -> bool>(&mut self, f: F) {
        for block in &mut self.basic_blocks {
            block.stmts.retain(|stmt| f(stmt))
        }
    }
}
