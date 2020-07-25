// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::vir;
use std::collections::HashMap;
use std::mem;
use log::debug;

/// Optimizations currently done:
///
/// 1.  Replace all `old(...)` inside `forall ..` with `let tmp == (old(..)) in forall ..`.
/// 2.  Pull out all `unfolding ... in` that are inside `forall` to outside of `forall`.
/// 3.  Replace all arithmetic expressions inside `forall` that do not depend on bound variables
///     with `let tmp == (...) in forall ..`.
///
/// Note: this seems to be required to workaround some Silicon incompleteness.
pub fn rewrite(cfg: vir::CfgMethod) -> vir::CfgMethod {
    let mut optimizer = Optimizer::new();
    optimizer.replace_cfg(cfg)
}

struct Optimizer {}

impl Optimizer {
    fn new() -> Self {
        Self {}
    }

    fn replace_cfg(&mut self, mut cfg: vir::CfgMethod) -> vir::CfgMethod {
        let mut sentinel_stmt = vir::Stmt::Comment(String::from("moved out stmt"));
        for block in &mut cfg.basic_blocks {
            for stmt in &mut block.stmts {
                mem::swap(&mut sentinel_stmt, stmt);
                sentinel_stmt = self.replace_stmt(sentinel_stmt);
                mem::swap(&mut sentinel_stmt, stmt);
            }
        }
        cfg
    }

    fn replace_stmt(&mut self, stmt: vir::Stmt) -> vir::Stmt {
        use self::vir::StmtFolder;
        self.fold(stmt)
    }

    fn replace_expr_old(&mut self, expr: vir::Expr) -> vir::Expr {
        use self::vir::ExprFolder;
        self.fold(expr)
    }

    fn replace_expr_unfolding(&mut self, expr: vir::Expr) -> vir::Expr {
        let mut unfolding_extractor = UnfoldingExtractor {
            unfoldings: HashMap::new(),
            in_quantifier: false,
        };
        use self::vir::ExprFolder;
        unfolding_extractor.fold(expr)
    }
}

impl vir::StmtFolder for Optimizer {
    fn fold_assert(
        &mut self,
        expr: vir::Expr,
        folding: vir::FoldingBehaviour,
        pos: vir::Position,
    ) -> vir::Stmt {
        let pulled_unfodling = self.replace_expr_unfolding(expr);
        let replaced_old = self.replace_expr_old(pulled_unfodling);
        vir::Stmt::Assert(replaced_old, folding, pos)
    }
    fn fold_inhale(&mut self, expr: vir::Expr, folding: vir::FoldingBehaviour) -> vir::Stmt {
        let pulled_unfodling = self.replace_expr_unfolding(expr);
        vir::Stmt::Inhale(pulled_unfodling, folding)
    }
}

impl vir::ExprFolder for Optimizer {
    fn fold_forall(
        &mut self,
        variables: Vec<vir::LocalVar>,
        triggers: Vec<vir::Trigger>,
        body: Box<vir::Expr>,
        pos: vir::Position,
    ) -> vir::Expr {
        debug!("original body: {}", body);
        let mut replacer = Replacer::new(&variables);
        let replaced_body = replacer.fold_boxed(body);
        debug!("replaced body: {}", replaced_body);
        let mut forall = vir::Expr::ForAll(variables, triggers, replaced_body, pos);

        if replacer.counter > 0 {
            for (expr, variable) in replacer.map {
                forall = vir::Expr::LetExpr(variable, box expr, box forall, pos);
            }
            debug!("replaced quantifier: {}", forall);
        }

        forall
    }
}

struct Replacer {
    counter: u32,
    map: HashMap<vir::Expr, vir::LocalVar>,
    bound_vars: Vec<vir::Expr>,
}

impl Replacer {
    fn new(bound_vars: &Vec<vir::LocalVar>) -> Self {
        Self {
            counter: 0,
            map: HashMap::new(),
            bound_vars: bound_vars.iter().cloned().map(|v| v.into()).collect(),
        }
    }

    fn construct_fresh_local(&mut self, ty: &vir::Type) -> vir::LocalVar {
        let name = format!("_LET_{}", self.counter);
        self.counter += 1;
        vir::LocalVar {
            name: name,
            typ: ty.clone(),
        }
    }
}

impl vir::ExprFolder for Replacer {
    fn fold_labelled_old(
        &mut self,
        label: String,
        expr: Box<vir::Expr>,
        pos: vir::Position,
    ) -> vir::Expr {
        let original_expr = vir::Expr::LabelledOld(label, expr.clone(), pos);
        if expr.is_place() {
            if let Some(local) = self.map.get(&original_expr) {
                vir::Expr::Local(local.clone(), pos)
            } else {
                let ty = expr.get_type();
                let local = self.construct_fresh_local(ty);
                self.map.insert(original_expr, local.clone());
                vir::Expr::Local(local, pos)
            }
        } else {
            original_expr
        }
    }
    fn fold_bin_op(
        &mut self,
        kind: vir::BinOpKind,
        first: Box<vir::Expr>,
        second: Box<vir::Expr>,
        pos: vir::Position,
    ) -> vir::Expr {
        let folded_first = self.fold_boxed(first);
        let folded_second = self.fold_boxed(second);
        let original_expr = vir::Expr::BinOp(kind, folded_first, folded_second, pos);
        if (kind == vir::BinOpKind::Add
            || kind == vir::BinOpKind::Sub
            || kind == vir::BinOpKind::Mul
            || kind == vir::BinOpKind::Div
            || kind == vir::BinOpKind::Mod)
            && !self.bound_vars.iter().any(|v| original_expr.find(v))
        {
            if let Some(local) = self.map.get(&original_expr) {
                vir::Expr::Local(local.clone(), pos)
            } else {
                let local = self.construct_fresh_local(&vir::Type::Int);
                self.map.insert(original_expr, local.clone());
                vir::Expr::Local(local, pos)
            }
        } else {
            original_expr
        }
    }
}

struct UnfoldingExtractor {
    unfoldings: HashMap<
        (String, Vec<vir::Expr>),
        (vir::PermAmount, vir::MaybeEnumVariantIndex, vir::Position),
    >,
    in_quantifier: bool,
}

impl vir::ExprFolder for UnfoldingExtractor {
    fn fold_forall(
        &mut self,
        variables: Vec<vir::LocalVar>,
        triggers: Vec<vir::Trigger>,
        body: Box<vir::Expr>,
        pos: vir::Position,
    ) -> vir::Expr {
        assert!(
            self.unfoldings.is_empty(),
            "Nested quantifiers are not supported."
        );
        debug!("original body: {}", body);

        self.in_quantifier = true;
        let replaced_body = self.fold_boxed(body);
        self.in_quantifier = false;

        let mut forall = vir::Expr::ForAll(variables, triggers, replaced_body, pos);

        let unfoldings = mem::replace(&mut self.unfoldings, HashMap::new());

        for ((name, args), (perm_amount, variant, _)) in unfoldings {
            forall =
                vir::Expr::Unfolding(name, args, box forall, perm_amount, variant, pos);
        }
        debug!("replaced quantifier: {}", forall);

        forall
    }
    fn fold_unfolding(
        &mut self,
        name: String,
        args: Vec<vir::Expr>,
        expr: Box<vir::Expr>,
        perm: vir::PermAmount,
        variant: vir::MaybeEnumVariantIndex,
        pos: vir::Position,
    ) -> vir::Expr {
        if self.in_quantifier {
            self.unfoldings.insert((name, args), (perm, variant, pos));
            self.fold(*expr)
        } else {
            vir::Expr::Unfolding(name, args, expr, perm, variant, pos)
        }
    }
    fn fold_labelled_old(
        &mut self,
        label: String,
        body: Box<vir::Expr>,
        pos: vir::Position,
    ) -> vir::Expr {
        vir::Expr::LabelledOld(label, body, pos)
    }
}
