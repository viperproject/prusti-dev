// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub(super) mod interface;

use vir_crate::polymorphic::{
    BinOp, BinaryOpKind, Cond, Expr, ExprFolder, ExprIterator, FallibleExprWalker,
    ResourceAccessPredicate, UnaryOp, UnaryOpKind,
};

use super::errors::{EncodingError, EncodingResult};

struct Changer<'a> {
    scope_ids: &'a [isize],
}
impl<'a> ExprFolder for Changer<'a> {
    fn fold_resource_access_predicate(&mut self, expr: ResourceAccessPredicate) -> Expr {
        self.scope_ids
            .iter()
            .map(|&scope_id| expr.replace_scope_id(scope_id))
            .conjoin()
    }
}

pub fn change_scope_id(expr: Expr, scope_ids: &[isize]) -> Expr {
    let mut remover = Changer { scope_ids };
    remover.fold(expr)
}

// Founds resource predicates and if they appear in incorrect position such as in the negative form, in the condition of a conditional, in the gard of an implication or inside other resource predicates
#[derive(Default)]
struct ResourceFinder {
    // track if we have found a resource predicate
    resource_found: bool,
    // counts the negativity of the current expression
    negativity: usize,
    // counts the number of conditions of a conditional, gards of an implication, or resource predicates traversed
    depth: usize,
}

impl ResourceFinder {
    fn inc_depth(&mut self) {
        self.depth += 1;
    }

    fn dec_depth(&mut self) {
        assert!(self.depth > 0);
        self.depth -= 1;
    }

    fn inc_negativity(&mut self) {
        self.negativity += 1;
    }

    fn dec_negativity(&mut self) {
        assert!(self.negativity > 0);
        self.negativity -= 1;
    }
}

impl FallibleExprWalker for ResourceFinder {
    type Error = EncodingError;

    fn fallible_walk_resource_access_predicate(
        &mut self,
        expr: &ResourceAccessPredicate,
    ) -> Result<(), Self::Error> {
        if self.negativity % 2 == 1 {
            return Err(EncodingError::incorrect(
                "Found a resource predicate in a negative position!",
            ));
        }
        if self.depth > 0 {
            return Err(EncodingError::incorrect(
                "Found a resource predicate in the condition of a conditional, \
                 or in the guard of an implication, or a resource predicate inside an other!",
            ));
        }
        self.resource_found = true;
        self.inc_depth();
        self.fallible_walk(&expr.amount)?;
        self.dec_depth();
        Ok(())
    }

    fn fallible_walk_cond(&mut self, expr: &Cond) -> Result<(), Self::Error> {
        let Cond {
            guard,
            then_expr,
            else_expr,
            ..
        } = expr;
        self.inc_depth();
        self.fallible_walk(guard)?;
        self.dec_depth();
        self.fallible_walk(then_expr)?;
        self.fallible_walk(else_expr)?;
        Ok(())
    }

    fn fallible_walk_unary_op(&mut self, expr: &UnaryOp) -> Result<(), Self::Error> {
        let UnaryOp {
            op_kind, argument, ..
        } = expr;
        let is_not = matches!(op_kind, UnaryOpKind::Not);
        if is_not {
            self.inc_negativity();
        }
        self.fallible_walk(argument)?;
        if is_not {
            self.dec_negativity();
        }
        Ok(())
    }

    fn fallible_walk_bin_op(&mut self, expr: &BinOp) -> Result<(), Self::Error> {
        let BinOp {
            op_kind,
            left,
            right,
            ..
        } = expr;
        let is_implies = matches!(op_kind, BinaryOpKind::Implies);
        if is_implies {
            self.inc_depth();
        }
        self.fallible_walk(left)?;
        if is_implies {
            self.dec_depth();
        }
        self.fallible_walk(right)?;
        Ok(())
    }
}

pub fn contains_resource_access_predicate(expr: &Expr) -> EncodingResult<bool> {
    let mut finder: ResourceFinder = Default::default();
    finder.fallible_walk(expr)?;
    assert!(finder.negativity == 0);
    assert!(finder.depth == 0);
    Ok(finder.resource_found)
}
