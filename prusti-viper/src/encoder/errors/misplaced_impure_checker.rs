// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use vir_crate::polymorphic::{Position, program::Program, CfgMethod, ExprWalker, Expr, BinaryOpKind, BinOp, UnaryOpKind, UnaryOp, Cond, PredicateAccessPredicate, FieldAccessPredicate, ResourceAccessPredicate, ObligationAccessPredicate};
use crate::encoder::errors::PositionManager;
use prusti_interface::PrustiError;

#[derive(Clone, Debug)]
struct MisplacedImpureError {
    impurity_pos: Position,
    operator_pos: Position,
    message: String,
}

impl MisplacedImpureError {
    fn to_prusti_error(self, position_manager: &PositionManager) -> PrustiError {
        // TODO: remove dangerous unwrap
        let error = PrustiError::incorrect(self.message, position_manager.source_span.get(&self.impurity_pos.id()).unwrap().clone());
        error.push_primary_span(position_manager.source_span.get(&self.operator_pos.id()))
    }
}

impl MisplacedImpureError {
    fn new(impurity_pos: Position, operator_pos: Position, message: String) -> Self {
        Self {
            impurity_pos,
            operator_pos,
            message,
        }
    }
}

pub struct MisplacedImpureChecker {
    errors: Vec<MisplacedImpureError>
}

impl MisplacedImpureChecker {
    fn new() -> Self {
        Self {
            errors: Vec::new()
        }
    }

    fn check_method(&mut self, method: &CfgMethod) {
        method.walk_expressions(|expr| self.walk(expr));
    }

    fn check_program(&mut self, program: &Program) {
        for method in &program.methods {
            self.check_method(method);
        }
    }

    pub fn check_for_misplaced_impure(programs: &Vec<Program>, position_manager: &PositionManager) -> Vec<PrustiError> {
        let mut checker = Self::new();
        for program in programs {
            checker.check_program(program);
        }
        checker.errors.into_iter().map(|e| e.to_prusti_error(position_manager)).collect()
    }

    fn walk_and_check_for_impurities(&mut self, expr: &Expr, outer_pos: &Position, message: &str) {
        let err_count_before = self.errors.len();
        self.walk(expr);
        let err_count_after = self.errors.len();
        if err_count_before == err_count_after {
            if let Some(impurity_pos) = ImpurityFinder::find_impurity(expr) {
                self.errors.push(MisplacedImpureError::new(impurity_pos, *outer_pos, message.to_string()));
            }
        }
    }
}

impl ExprWalker for MisplacedImpureChecker {
    fn walk_bin_op(&mut self, BinOp { op_kind, left, right, position }: &BinOp) {
        match op_kind {
            BinaryOpKind::Or => {
                self.walk_and_check_for_impurities(left, position, "resource access is illegal inside disjunctions");
                self.walk_and_check_for_impurities(right, position, "resource access is illegal inside disjunctions");
            }
            BinaryOpKind::Implies => {
                self.walk_and_check_for_impurities(left, position, "resource access is illegal on the left-hand side of implications");
                self.walk(right)
            }
            BinaryOpKind::EqCmp | BinaryOpKind::NeCmp => {
                self.walk_and_check_for_impurities(left, position, "resource access is illegal inside equality comparisons");
                self.walk_and_check_for_impurities(right, position, "resource access is illegal inside equality comparisons");
            }
            _ => {
                self.walk(left);
                self.walk(right);
            }
        }
    }

    fn walk_unary_op(&mut self, UnaryOp { op_kind, argument, position }: &UnaryOp) {
        match op_kind {
            UnaryOpKind::Not => {
                self.walk_and_check_for_impurities(argument, position, "resource access is illegal inside negations");
            }
            _ => {
                self.walk(argument);
            }
        }
    }

    fn walk_cond(&mut self, Cond { guard, then_expr, else_expr, position }: &Cond) {
        self.walk_and_check_for_impurities(guard, position, "resource access is illegal in guards of conditionals");
        self.walk(then_expr);
        self.walk(else_expr);
    }
}

struct ImpurityFinder {
    impurity_pos: Option<Position>
}

impl ImpurityFinder {
    fn find_impurity(expr: &Expr) -> Option<Position> {
        let mut finder = ImpurityFinder {
            impurity_pos: None
        };
        finder.walk(expr);
        finder.impurity_pos
    }
}

impl ExprWalker for ImpurityFinder {
    fn walk_predicate_access_predicate(
        &mut self,
        predicate_access_predicate: &PredicateAccessPredicate,
        ) {
        self.impurity_pos = Some(predicate_access_predicate.position);
    }

    fn walk_field_access_predicate(
        &mut self,
        field_access_predicate: &FieldAccessPredicate,
        ) {
        self.impurity_pos = Some(field_access_predicate.position);
    }

    fn walk_resource_access_predicate(
        &mut self,
        resource_access_predicate: &ResourceAccessPredicate,
        ) {
        self.impurity_pos = Some(resource_access_predicate.position);
    }

    fn walk_obligation_access_predicate(
        &mut self,
        obligation_access_predicate: &ObligationAccessPredicate,
        ) {
        self.impurity_pos = Some(obligation_access_predicate.position);
    }
}
