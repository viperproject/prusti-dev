// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use log::trace;
use rustc_hash::FxHashMap;
use std::{
    fmt::{self, Debug, Display},
    mem,
};
use vir_crate::polymorphic as vir;

#[derive(Clone, Debug)]
pub struct ExprBackwardInterpreterState {
    /// None if the expression is undefined.
    expr: Option<vir::Expr>,
    substs: FxHashMap<vir::TypeVar, vir::Type>,
}

impl Display for ExprBackwardInterpreterState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(expr) = self.expr.as_ref() {
            write!(f, "expr={expr}")
        } else {
            write!(f, "expr=undefined")
        }
    }
}

impl ExprBackwardInterpreterState {
    pub fn new(expr: Option<vir::Expr>) -> Self {
        ExprBackwardInterpreterState {
            expr,
            substs: FxHashMap::default(),
        }
    }

    pub fn new_defined(expr: vir::Expr) -> Self {
        ExprBackwardInterpreterState {
            expr: Some(expr),
            substs: FxHashMap::default(),
        }
    }

    pub fn expr(&self) -> Option<&vir::Expr> {
        self.expr.as_ref()
    }

    pub fn expr_mut(&mut self) -> Option<&mut vir::Expr> {
        self.expr.as_mut()
    }

    pub fn into_expr(self) -> Option<vir::Expr> {
        self.expr
    }

    pub fn substitute_value(&mut self, target: &vir::Expr, replacement: vir::Expr) {
        trace!("substitute_value {:?} --> {:?}", target, replacement);
        let target = target.clone().patch_types(&self.substs);
        let replacement = replacement.patch_types(&self.substs);

        if let Some(curr_expr) = self.expr.as_mut() {
            // Replace two times to avoid cloning `expr`, which could be big.
            let expr = mem::replace(curr_expr, true.into());
            let new_expr = expr.replace_place(&target, &replacement).simplify_addr_of();
            let _ = mem::replace(curr_expr, new_expr);
        }
    }

    pub fn uses_place(&self, sub_target: &vir::Expr) -> bool {
        trace!("use_place {:?}", sub_target);
        let sub_target = sub_target.clone().patch_types(&self.substs);
        self.expr
            .as_ref()
            .map(|expr| expr.find(&sub_target))
            .unwrap_or(false)
    }
}
