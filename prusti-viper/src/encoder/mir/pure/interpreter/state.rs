use std::{
    collections::HashMap,
    fmt::{self, Display},
    mem,
};

use log::trace;
use vir_crate::high::{self as vir_high, Generic};

#[derive(Clone, Debug)]
// FIXME: Refactor pure encoder and specification encoder into subitems of a
// single entity.
pub(in super::super) struct ExprBackwardInterpreterState {
    /// None if the expression is undefined.
    expr: Option<vir_high::Expression>,
    substs: HashMap<vir_high::ty::TypeVar, vir_high::Type>,
}

impl Display for ExprBackwardInterpreterState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(expr) = self.expr.as_ref() {
            write!(f, "expr={}", expr)
        } else {
            write!(f, "expr=undefined")
        }
    }
}

impl ExprBackwardInterpreterState {
    pub(super) fn new(expr: Option<vir_high::Expression>) -> Self {
        ExprBackwardInterpreterState {
            expr,
            substs: HashMap::new(),
        }
    }

    pub(super) fn new_defined(expr: vir_high::Expression) -> ExprBackwardInterpreterState {
        ExprBackwardInterpreterState {
            expr: Some(expr),
            substs: HashMap::new(),
        }
    }

    pub(in super::super) fn new_undefined() -> Self {
        ExprBackwardInterpreterState {
            expr: None,
            substs: HashMap::new(),
        }
    }

    pub(in super::super) fn new_defined_with_substs(
        expr: vir_high::Expression,
        substs: HashMap<vir_high::ty::TypeVar, vir_high::Type>,
    ) -> Self {
        ExprBackwardInterpreterState {
            expr: Some(expr),
            substs,
        }
    }

    pub(super) fn expr(&self) -> Option<&vir_high::Expression> {
        self.expr.as_ref()
    }

    pub(in super::super) fn into_expr(self) -> Option<vir_high::Expression> {
        self.expr
    }

    pub(super) fn substitute_value(
        &mut self,
        target: &vir_high::Expression,
        replacement: vir_high::Expression,
    ) {
        trace!("substitute_value {:?} --> {:?}", target, replacement);
        let target = target.clone().substitute_types(&self.substs);
        let replacement = replacement.substitute_types(&self.substs);

        if let Some(curr_expr) = self.expr.as_mut() {
            // Replace two times to avoid cloning `expr`, which could be big.
            let expr = mem::replace(curr_expr, true.into());
            let mut new_expr = expr.replace_place(&target, &replacement); //.simplify_addr_of();
            mem::swap(curr_expr, &mut new_expr);
        }
    }

    pub(super) fn uses_place(&self, sub_target: &vir_high::Expression) -> bool {
        trace!("use_place {:?}", sub_target);
        let sub_target = sub_target.clone().substitute_types(&self.substs);
        self.expr
            .as_ref()
            .map(|expr| expr.find(&sub_target))
            .unwrap_or(false)
    }
}
