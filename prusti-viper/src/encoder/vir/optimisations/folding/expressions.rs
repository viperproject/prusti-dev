// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! An optimisation that pulls `unfolding` expressions as much up as
//! possible in this way hoping to reduce the number of unfolds. We
//! cannot pull unfolding if:
//!
//! 1.  There is a conflicting folding requirement coming from a
//!     function application.
//! 2.  There is an implication that branches on a enum discriminant.


use super::super::super::{ast, borrows};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::mem;


pub trait FoldingOptimiser {
    fn optimise(self) -> Self;
}

impl FoldingOptimiser for ast::Function {
    fn optimise(mut self) -> Self {
        trace!("function name={}", self.name);
        self.body = self.body.map(|e| e.optimise());
        trace!("end function name={}", self.name);
        self
    }
}

impl FoldingOptimiser for ast::Expr {
    fn optimise(self) -> Self {
        let mut optimiser = ExprOptimiser {
            unfoldings: HashMap::new(),
            requirements: HashSet::new(),
        };
        let new_expr = ast::ExprFolder::fold(&mut optimiser, self);
        restore_unfoldings(optimiser.get_unfoldings(), new_expr)
        //new_expr
    }
}

type UnfoldingMap = HashMap<ast::Expr, (String, ast::PermAmount, ast::MaybeEnumVariantIndex)>;
type RequirementSet = HashSet<ast::Expr>;

struct ExprOptimiser {
    /// Predicate argument → (predicate name, amount, enum index).
    unfoldings: UnfoldingMap,
    /// Unfolding requirements: how deeply a specific place should be unfolded.
    requirements: RequirementSet,
}

impl ExprOptimiser {
    fn get_unfoldings(&mut self) -> UnfoldingMap {
        mem::replace(&mut self.unfoldings, HashMap::new())
    }
    fn get_requirements(&mut self) -> RequirementSet {
        mem::replace(&mut self.requirements, HashSet::new())
    }
    fn add_requirements(&mut self, requirements: impl Iterator<Item=ast::Expr>) {
        self.requirements.extend(requirements);
    }
    /// Same as add_requirements, just drops all places that have the added places as prefixes.
    fn update_requirements<'a>(&mut self, requirements: impl Iterator<Item=&'a ast::Expr>) {
        for place in requirements {
            assert!(place.is_place());
            self.requirements.retain(|p| !p.has_prefix(place));
            self.requirements.insert(place.clone());
        }
    }
}

fn restore_unfoldings_boxed(unfolding_map: UnfoldingMap, expr: Box<ast::Expr>) -> Box<ast::Expr> {
    box restore_unfoldings(unfolding_map, *expr)
}

/// Restore unfoldings on a given expression.
fn restore_unfoldings(unfolding_map: UnfoldingMap, mut expr: ast::Expr) -> ast::Expr {
    let mut unfoldings: Vec<_> = unfolding_map.into_iter().collect();
    unfoldings.sort_by(|(k1, _), (k2, _)| {
        if k1 == k2 {
            Ordering::Equal
        } else {
            let base_k1 = k1.get_base().name;
            let base_k2 = k2.get_base().name;
            if base_k1 < base_k2 {
                Ordering::Less
            } else if base_k1 > base_k2 {
                Ordering::Greater
            } else {
                if k2.has_prefix(k1) {
                    Ordering::Greater
                } else if k1.has_prefix(k2) {
                    Ordering::Less
                } else {
                    format!("{}", k1).cmp(&format!("{}", k2))
                }
            }
        }
    });
    for (arg, (name, perm_amount, variant)) in unfoldings {
        let position = expr.pos().clone();
        expr = ast::Expr::Unfolding(
            name,
            vec![arg],
            box expr,
            perm_amount,
            variant,
            position,
        );
    }
    expr
}

/// Check whether the requirements are conflicting.
fn check_requirements_conflict(reqs1: &RequirementSet, reqs2: &RequirementSet) -> bool {
    for place1 in reqs1 {
        for place2 in reqs2 {
            // Check if we require the same place to be unfolded at a different depth.
            if place1.has_proper_prefix(place2) && !reqs1.contains(place2) {
                return true;
            }
            if place2.has_proper_prefix(place1) && !reqs2.contains(place1) {
                return true;
            }
            // Check if we have different variants.
            if place1.get_base() == place2.get_base() &&
                !place1.has_prefix(place2) &&
                !place2.has_prefix(place1) {
                let (base1, components1) = place1.explode_place();
                let (base2, components2) = place2.explode_place();
                assert!(base1 == base2);
                let mut len1 = components1.len();
                let mut len2 = components2.len();
                for (part1, part2) in components1.into_iter().zip(components2.into_iter()) {
                    len1 -= 1;
                    len2 -= 1;
                    if part1 != part2 {
                        match (part1, part2) {
                            (ast::PlaceComponent::Variant(..),
                             ast::PlaceComponent::Variant(..)) => {
                                if len1 != 0 || len2 != 0 {
                                    // If variant is the last component of the place, then we are
                                    // still fine because we will try to unfold under implication.
                                    return true;
                                }
                            }
                            _ => {}
                        }
                        break;
                    }
                }
            }
        }
    }
    false
}

impl ast::ExprFolder for ExprOptimiser {

    fn fold(&mut self, expr: ast::Expr) -> ast::Expr {
        match expr {
            ast::Expr::LabelledOld(..) => expr,
            ast::Expr::Unfolding(name, mut args, box body, perm, variant, _) => {
                assert!(args.len() == 1);
                let new_expr = self.fold(body);
                self.unfoldings.insert(args.pop().unwrap(), (name, perm, variant));
                new_expr
            }
            _ => {
                if expr.is_place() {
                    self.requirements.insert(expr.clone());
                    expr
                } else {
                    ast::default_fold_expr(self, expr)
                }
            }
        }
    }
    fn fold_unfolding(
        &mut self,
        name: String,
        mut args: Vec<ast::Expr>,
        expr: Box<ast::Expr>,
        perm: ast::PermAmount,
        variant: ast::MaybeEnumVariantIndex,
        pos: ast::Position,
    ) -> ast::Expr {
        unreachable!();
    }
    fn fold_labelled_old(
        &mut self,
        label: String,
        body: Box<ast::Expr>,
        pos: ast::Position
    ) -> ast::Expr {
        unreachable!();
    }
    fn fold_magic_wand(
        &mut self,
        lhs: Box<ast::Expr>,
        rhs: Box<ast::Expr>,
        borrow: Option<borrows::Borrow>,
        pos: ast::Position,
    ) -> ast::Expr {
        unimplemented!()
    }
    fn fold_predicate_access_predicate(
        &mut self,
        name: String,
        arg: Box<ast::Expr>,
        perm_amount: ast::PermAmount,
        pos: ast::Position,
    ) -> ast::Expr {
        unimplemented!()
    }
    fn fold_field_access_predicate(
        &mut self,
        receiver: Box<ast::Expr>,
        perm_amount: ast::PermAmount,
        pos: ast::Position
    ) -> ast::Expr {
        unimplemented!()
    }
    fn fold_bin_op(
        &mut self,
        kind: ast::BinOpKind,
        first: Box<ast::Expr>,
        second: Box<ast::Expr>,
        pos: ast::Position
    ) -> ast::Expr {
        let first_folded = self.fold_boxed(first);
        let first_unfoldings = self.get_unfoldings();
        let first_requirements = self.get_requirements();

        let second_folded = self.fold_boxed(second);

        if check_requirements_conflict(&first_requirements, &self.requirements) {
            let second_unfoldings = self.get_unfoldings();
            self.add_requirements(first_requirements.into_iter());
            self.update_requirements(first_unfoldings.keys());
            self.update_requirements(second_unfoldings.keys());
            let first_restored = restore_unfoldings_boxed(first_unfoldings, first_folded);
            let second_restored = restore_unfoldings_boxed(second_unfoldings, second_folded);
            ast::Expr::BinOp(kind, first_restored, second_restored, pos)
        } else {
            self.requirements.extend(first_requirements);
            self.unfoldings.extend(first_unfoldings);
            ast::Expr::BinOp(kind, first_folded, second_folded, pos)
        }
    }
    fn fold_cond(
        &mut self,
        guard: Box<ast::Expr>,
        then_expr: Box<ast::Expr>,
        else_expr: Box<ast::Expr>,
        pos: ast::Position
    ) -> ast::Expr {
        let guard_folded = self.fold_boxed(guard);
        let guard_unfoldings = self.get_unfoldings();
        let guard_requirements = self.get_requirements();

        let then_folded = self.fold_boxed(then_expr);
        let then_unfoldings = self.get_unfoldings();
        let then_requirements = self.get_requirements();

        let else_folded = self.fold_boxed(else_expr);

        if check_requirements_conflict(&guard_requirements, &self.requirements) ||
            check_requirements_conflict(&guard_requirements, &then_requirements) ||
            check_requirements_conflict(&then_requirements, &self.requirements) {

            let else_unfoldings = self.get_unfoldings();
            self.add_requirements(guard_requirements.into_iter());
            self.add_requirements(then_requirements.into_iter());
            self.update_requirements(guard_unfoldings.keys());
            self.update_requirements(then_unfoldings.keys());
            self.update_requirements(else_unfoldings.keys());

            let guard_restored = restore_unfoldings_boxed(guard_unfoldings, guard_folded);
            let then_restored = restore_unfoldings_boxed(then_unfoldings, then_folded);
            let else_restored = restore_unfoldings_boxed(else_unfoldings, else_folded);
            ast::Expr::Cond(
                guard_restored,
                then_restored,
                else_restored,
                pos,
            )
        } else {
            self.requirements.extend(guard_requirements);
            self.requirements.extend(then_requirements);
            self.unfoldings.extend(guard_unfoldings);
            self.unfoldings.extend(then_unfoldings);
            ast::Expr::Cond(
                guard_folded,
                then_folded,
                else_folded,
                pos,
            )
        }
    }
    fn fold_let_expr(
        &mut self,
        var: ast::LocalVar,
        expr: Box<ast::Expr>,
        body: Box<ast::Expr>,
        pos: ast::Position
    ) -> ast::Expr {
        let expr_folded = self.fold_boxed(expr);
        let expr_unfoldings = self.get_unfoldings();
        let expr_requirements = self.get_requirements();

        let body_folded = self.fold_boxed(body);

        if check_requirements_conflict(&expr_requirements, &self.requirements) {
            let body_unfoldings = self.get_unfoldings();
            self.add_requirements(expr_requirements.into_iter());
            self.update_requirements(expr_unfoldings.keys());
            self.update_requirements(body_unfoldings.keys());
            let expr_restored = restore_unfoldings_boxed(expr_unfoldings, expr_folded);
            let body_restored = restore_unfoldings_boxed(body_unfoldings, body_folded);
            ast::Expr::LetExpr(var, expr_restored, body_restored, pos)
        } else {
            self.requirements.extend(expr_requirements);
            self.unfoldings.extend(expr_unfoldings);
            ast::Expr::LetExpr(var, expr_folded, body_folded, pos)
        }
    }
}

struct RequirementsCollector {
    /// Unfolding requirements: how deeply a specific place should be unfolded.
    requirements: RequirementSet,
}

impl ast::ExprWalker for RequirementsCollector {
    fn walk(&mut self, e: &ast::Expr) {
        if e.is_place() {
            self.requirements.insert(e.clone());
        } else {
            ast::default_walk_expr(self, e);
        }
    }
    fn walk_unfolding(
        &mut self,
        _name: &str,
        args: &Vec<ast::Expr>,
        _body: &ast::Expr,
        _perm: ast::PermAmount,
        _variant: &ast::MaybeEnumVariantIndex,
        _pos: &ast::Position
    ) {
        debug_assert!(args.len() == 1);
        let arg = args[0].clone();
        assert!(arg.is_place());
        self.requirements.insert(arg);
    }
    fn walk_labelled_old(&mut self, _label: &str, _body: &ast::Expr, _pos: &ast::Position) {
        // We do not collect requirements from old expressions.
    }
}
