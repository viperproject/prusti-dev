// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_hash::FxHashMap;
use std::{
    fmt::{self, Display},
    mem,
};

use vir_crate::high::{self as vir_high, Generic};

#[derive(Clone, Debug)]
// FIXME: Refactor pure encoder and specification encoder into subitems of a
// single entity.
pub(in super::super) struct ExprBackwardInterpreterState {
    /// None if the expression is undefined.
    expr: Option<vir_high::Expression>,
    substs: FxHashMap<vir_high::ty::TypeVar, vir_high::Type>,
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
    pub(in super::super) fn new(expr: Option<vir_high::Expression>) -> Self {
        ExprBackwardInterpreterState {
            expr,
            substs: FxHashMap::default(),
        }
    }

    pub(in super::super) fn new_defined(
        expr: vir_high::Expression,
    ) -> ExprBackwardInterpreterState {
        ExprBackwardInterpreterState {
            expr: Some(expr),
            substs: FxHashMap::default(),
        }
    }

    pub(super) fn expr(&self) -> Option<&vir_high::Expression> {
        self.expr.as_ref()
    }

    pub(in super::super) fn into_expr(self) -> Option<vir_high::Expression> {
        self.expr
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub(super) fn substitute_value(
        &mut self,
        target: &vir_high::Expression,
        replacement: vir_high::Expression,
    ) {
        let target = target.clone().substitute_types(&self.substs);
        let replacement = replacement.substitute_types(&self.substs);

        if let Some(curr_expr) = self.expr.as_mut() {
            // Replace two times to avoid cloning `expr`, which could be big.
            let expr = mem::replace(curr_expr, true.into());
            // target = target.erase_lifetime();
            // replacement = replacement.erase_lifetime();
            let new_expr = expr.replace_place(&target, &replacement); //.simplify_addr_of();
            let mut new_expr = new_expr.simplify_out_constructors();
            mem::swap(curr_expr, &mut new_expr);
        }
    }

    #[tracing::instrument(level = "trace", skip(self), ret)]
    pub(super) fn uses_place(&self, sub_target: &vir_high::Expression) -> bool {
        let sub_target = sub_target.clone().substitute_types(&self.substs);
        self.expr
            .as_ref()
            .map(|expr| expr.find(&sub_target))
            .unwrap_or(false)
    }
}
