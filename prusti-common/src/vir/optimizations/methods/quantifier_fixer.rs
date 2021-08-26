// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::config;
use crate::vir::polymorphic_vir as vir;
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
pub fn fix_quantifiers(cfg: vir::CfgMethod) -> vir::CfgMethod {
    let mut optimizer = Optimizer::new();
    optimizer.replace_cfg(cfg)
}

struct Optimizer {
    counter: u32,
}

impl Optimizer {
    fn new() -> Self {
        Self { counter: 0 }
    }

    fn replace_cfg(&mut self, mut cfg: vir::CfgMethod) -> vir::CfgMethod {
        let mut sentinel_stmt = vir::Stmt::comment("moved out stmt");
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
        pos: vir::Position,
    ) -> vir::Stmt {
        let pulled_unfodling = self.replace_expr_unfolding(expr);
        let replaced_old = self.replace_expr_old(pulled_unfodling);
        vir::Stmt::Assert( vir::Assert {
            expr: replaced_old,
            position: pos,
        })
    }
    fn fold_inhale(&mut self, expr: vir::Expr) -> vir::Stmt {
        let pulled_unfodling = self.replace_expr_unfolding(expr);
        let replaced_old = self.replace_expr_old(pulled_unfodling);
        vir::Stmt::Inhale( vir::Inhale {
            expr: replaced_old,
        })
    }
}

impl vir::ExprFolder for Optimizer {
    fn fold_magic_wand(&mut self, lhs: Box<vir::Expr>, rhs: Box<vir::Expr>, borrow: Option<vir::borrows::Borrow>, pos: vir::Position) -> vir::Expr {
        vir::Expr::MagicWand( vir::MagicWand {
            left: lhs,
            right: rhs,
            borrow,
            position: pos,
        })
    }
    fn fold_forall(
        &mut self,
        variables: Vec<vir::LocalVar>,
        triggers: Vec<vir::Trigger>,
        body: Box<vir::Expr>,
        pos: vir::Position,
    ) -> vir::Expr {
        debug!("original body: {}", body);
        let folded_body = self.fold_boxed(body);
        debug!("Folded body: {}", folded_body);
        let old_counter = self.counter;
        let mut replacer = Replacer::new(&variables, &mut self.counter);
        let replaced_body = replacer.fold_boxed(folded_body);
        debug!("replaced body: {}", replaced_body);
        let mut forall = vir::Expr::ForAll( vir::ForAll {
            variables, triggers,
            body: replaced_body,
            position: pos
        });

        if *replacer.counter > old_counter {
            for (expr, variable) in replacer.map {
                forall = vir::Expr::LetExpr( vir::LetExpr {
                    variable,
                    def: box expr,
                    body: box forall,
                    position: pos});
            }
            debug!("replaced quantifier: {}", forall);
        }

        forall
    }
}

struct Replacer<'a> {
    counter: &'a mut u32,
    map: HashMap<vir::Expr, vir::LocalVar>,
    bound_vars: Vec<vir::Expr>,
}

impl<'a> Replacer<'a> {
    fn new(bound_vars: &Vec<vir::LocalVar>, counter: &'a mut u32) -> Self {
        Self {
            counter: counter,
            map: HashMap::new(),
            bound_vars: bound_vars.iter().cloned().map(|v| v.into()).collect(),
        }
    }

    fn construct_fresh_local(&mut self, ty: &vir::Type) -> vir::LocalVar {
        let name = format!("_LET_{}", self.counter);
        (*self.counter) += 1;
        vir::LocalVar {
            name: name,
            typ: ty.clone(),
        }
    }

    fn replace_expr(&mut self, original_expr: vir::Expr, pos: vir::Position) -> vir::Expr {
        if let Some(local) = self.map.get(&original_expr) {
            vir::Expr::Local( vir::Local {variable: local.clone(), position: pos} )
        } else {
            let typ = original_expr.get_type();
            let local = self.construct_fresh_local(&typ);
            self.map.insert(original_expr, local.clone());
            vir::Expr::Local( vir::Local {variable: local, position: pos} )
        }
    }
}

impl<'a> vir::ExprFolder for Replacer<'a> {
    fn fold_labelled_old(
        &mut self,
        label: String,
        expr: Box<vir::Expr>,
        pos: vir::Position,
    ) -> vir::Expr {
        let original_expr = vir::Expr::LabelledOld( vir::LabelledOld {
            label,
            base: expr.clone(),
            position: pos,
        });
        if expr.is_place() {
            if let Some(local) = self.map.get(&original_expr) {
                vir::Expr::Local( vir::Local {
                    variable: local.clone(),
                    position: pos,
                })
            } else {
                let ty = expr.get_type();
                let local = self.construct_fresh_local(ty);
                self.map.insert(original_expr, local.clone());
                vir::Expr::Local( vir::Local {
                    variable: local,
                    position: pos,
                })
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
        let first_contains_bounded = self.bound_vars.iter().any(|v| first.find(v));
        let second_contains_bounded = self.bound_vars.iter().any(|v| second.find(v));

        if first_contains_bounded || second_contains_bounded {
            // The expression contains bounded variables. Cannot pull it out.
            let folded_first = self.fold_boxed(first);
            let folded_second = self.fold_boxed(second);
            vir::Expr::BinOp( vir::BinOp {
                op_kind: kind,
                left: folded_first,
                right: folded_second,
                position: pos,
            })
        } else {
            // Pull out the expression.
            let original_expr = vir::Expr::BinOp( vir::BinOp {
                op_kind: kind,
                left: first,
                right: second,
                position: pos,
            });
            self.replace_expr(original_expr, pos)
        }
    }
    fn fold_field(&mut self, receiver: Box<vir::Expr>, field: vir::Field, pos: vir::Position) -> vir::Expr {
        match &*receiver {
            vir::Expr::Local(_) => {
                let original_expr = vir::Expr::Field( vir::FieldExpr {
                    base: receiver,
                    field,
                    position: pos,
                });
                self.replace_expr(original_expr, pos)
            }
            _ => {
                vir::Expr::Field( vir::FieldExpr {
                    base: receiver,
                    field,
                    position: pos,
                })
            }
        }
    }
    fn fold_forall(
        &mut self,
        variables: Vec<vir::LocalVar>,
        triggers: Vec<vir::Trigger>,
        body: Box<vir::Expr>,
        pos: vir::Position,
    ) -> vir::Expr {
        vir::Expr::ForAll( vir::ForAll {
            variables,
            triggers,
            body,
            position: pos,
        })
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

        let mut forall = vir::Expr::ForAll( vir::ForAll {
            variables,
            triggers,
            body: replaced_body,
            position: pos,
        });

        let unfoldings = mem::replace(&mut self.unfoldings, HashMap::new());

        for ((name, args), (perm_amount, variant, _)) in unfoldings {
            forall =
                vir::Expr::Unfolding( vir::Unfolding {
                    predicate_name: name,
                    arguments: args,
                    base: box forall,
                    permission: perm_amount,
                    variant,
                    position: pos,
                });
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
            vir::Expr::Unfolding( vir::Unfolding {
                predicate_name: name,
                arguments: args,
                base: expr,
                permission: perm,
                variant,
                position: pos,
            })
        }
    }
    fn fold_labelled_old(
        &mut self,
        label: String,
        body: Box<vir::Expr>,
        pos: vir::Position,
    ) -> vir::Expr {
        vir::Expr::LabelledOld( vir::LabelledOld {
            label,
            base: body,
            position: pos,
        })
    }
}
