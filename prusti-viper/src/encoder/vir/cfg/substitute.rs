// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir;
use encoder::vir::cfg::method::*;
use std::fmt;

impl CfgMethod {
    pub fn substitute_expr<F>(&mut self, substitutor: F) where F: Fn(vir::Expr) -> vir::Expr {
        trace!("CfgMethod::substitute_place_in_old_expr {}", self.method_name);
        for block in &mut self.basic_blocks {
            for stmt in &mut block.stmts {
                *stmt = stmt.clone().map_expr(|x| substitutor(x));
            }
            block.successor = block.successor.clone().map_expr(|x| substitutor(x));
        }
    }
}

impl Successor {
    pub fn map_expr<F>(self, f: F) -> Self where F: Fn(vir::Expr) -> vir::Expr {
        trace!("Successor::map_expr {:?}", self);
        match self {
            Successor::GotoSwitch(guarded_targets, default_target) => Successor::GotoSwitch(
                guarded_targets.into_iter().map(|(guard, target)| (f(guard), target)).collect(),
                default_target
            ),

            Successor::GotoIf(guard, then_target, else_target) => Successor::GotoIf(
                f(guard),
                then_target,
                else_target
            ),

            x => x
        }
    }
}
