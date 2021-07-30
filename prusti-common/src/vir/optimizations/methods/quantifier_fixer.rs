// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::vir::{self, Expr, Type, Position};
use std::collections::HashSet;
use std::mem;

pub fn fix_quantifiers(cfg: vir::CfgMethod) -> vir::CfgMethod {
    let mut fixer = CfgFixer::new();
    fixer.replace_cfg(cfg)
}

struct CfgFixer {
    counter: u32,
}

impl CfgFixer {
    fn new() -> Self {
        Self { counter: 0 }
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

    fn replace_expr(&mut self, expr: Expr) -> Expr {
        use self::vir::ExprFolder;
        self.fold(expr)
    }
}

impl vir::StmtFolder for CfgFixer {
    fn fold_assert(
        &mut self,
        expr: Expr,
        pos: Position,
    ) -> vir::Stmt {
        vir::Stmt::Assert(self.replace_expr(expr), pos)
    }

    fn fold_inhale(&mut self, expr: Expr) -> vir::Stmt {
        vir::Stmt::Inhale(self.replace_expr(expr))
    }
}

impl vir::ExprFolder for CfgFixer {
    fn fold_magic_wand(
        &mut self,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        borrow: Option<vir::borrows::Borrow>,
        pos: Position,
    ) -> Expr {
        // TODO: this keeps magic wands intact, but why?
        Expr::MagicWand(lhs, rhs, borrow, pos)
    }

    fn fold_forall(
        &mut self,
        variables: Vec<vir::LocalVar>,
        triggers: Vec<vir::Trigger>,
        body: Box<Expr>,
        pos: Position,
    ) -> Expr {
        ExprFixer::new(&mut self.counter).fold(Expr::ForAll(
            variables,
            triggers,
            body,
            pos,
        )).expr
    }

    fn fold_exists(
        &mut self,
        variables: Vec<vir::LocalVar>,
        triggers: Vec<vir::Trigger>,
        body: Box<Expr>,
        pos: Position,
    ) -> Expr {
        ExprFixer::new(&mut self.counter).fold(Expr::Exists(
            variables,
            triggers,
            body,
            pos,
        )).expr
    }
}

enum ExprFixerWrapper {
    Unfolding {
        name: String,
        args: Vec<Expr>,
        perm: vir::PermAmount,
        variant: vir::MaybeEnumVariantIndex,
        pos: Position,
    },
    TempVar {
        local: vir::LocalVar,
        var_expr: Expr,
        pos: Position,
    },
}

fn apply_wrappers(mut expr: Expr, wrappers: Vec<ExprFixerWrapper>) -> Expr {
    for wrapper in wrappers.into_iter().rev() {
        expr = match wrapper {
            ExprFixerWrapper::Unfolding { name, args, perm, variant, pos }
                => Expr::Unfolding(name, args, box expr, perm, variant, pos),
            ExprFixerWrapper::TempVar { local, var_expr, pos }
                => Expr::LetExpr(local, box var_expr, box expr, pos),
        };
    }
    expr
}

struct QuantifierScope {
    bound_vars: HashSet<vir::LocalVar>,
    wrappers: Vec<ExprFixerWrapper>,
}

struct ExprFixer<'a> {
    counter: &'a mut u32,
    scopes: Vec<QuantifierScope>,
}

#[derive(Debug)]
struct FixerResult {
    expr: Expr,
    dependencies: HashSet<usize>,
    is_const: bool,
}

impl<'a> ExprFixer<'a> {
    fn new(counter: &'a mut u32) -> Self {
        Self {
            counter,
            scopes: vec![],
        }
    }

    fn push_scope(&mut self, bound_vars: Vec<vir::LocalVar>) -> usize {
        self.scopes.push(QuantifierScope {
            bound_vars: bound_vars.iter().cloned().collect(),
            wrappers: vec![],
        });
        self.scopes.len()
    }

    fn pop_scope(&mut self) -> QuantifierScope {
        self.scopes.pop().unwrap()
    }

    fn push_temp(&mut self, expr: &FixerResult) -> Expr {
        let max_depth = *expr.dependencies.iter().max().unwrap_or(&0);
        if expr.is_const || max_depth >= self.scopes.len() {
            return expr.expr.clone();
        }
        // TODO: store repeated expressions?
        //let local = if let Some(local) = self.stored_exprs.get(&var_expr) {
        //    local.clone()
        //} else {
            let name = format!("_LET_{}", self.counter);
            (*self.counter) += 1;
            let local = vir::LocalVar {
                name: name,
                typ: expr.expr.get_type().clone(),
            };
            let pos = expr.expr.pos();
            self.scopes[max_depth].wrappers.push(ExprFixerWrapper::TempVar {
                local: local.clone(),
                var_expr: expr.expr.clone(),
                pos,
            });
            local.into()
        //};
        //local.into()
    }

    fn combine<F: FnOnce(Vec<Expr>) -> Expr>(
        &mut self,
        sub_exprs: &[Expr],
        combine_func: F,
    ) -> FixerResult {
        let folded_exprs = sub_exprs.iter()
            .map(|expr| self.fold(expr.clone()))
            .collect::<Vec<_>>();
        let dependencies = folded_exprs.iter()
            .fold(HashSet::new(), |deps, expr| &deps | &expr.dependencies);
        let pulled_exprs = if dependencies.is_empty() {
            folded_exprs.into_iter()
                .map(|expr| expr.expr)
                .collect::<Vec<_>>()
        } else {
            let max_depth = *dependencies.iter().max().unwrap();
            folded_exprs.into_iter()
                .map(|expr| {
                    if !expr.dependencies.contains(&max_depth) {
                        self.push_temp(&expr)
                    } else {
                        expr.expr
                    }
                })
                .collect::<Vec<_>>()
        };
        FixerResult {
            expr: combine_func(pulled_exprs),
            dependencies,
            is_const: false,
        }
    }

    // quantifiers add the bound vars to the scope
    fn fold_forall(
        &mut self,
        variables: Vec<vir::LocalVar>,
        triggers: Vec<vir::Trigger>,
        body: Box<Expr>,
        pos: Position,
    ) -> FixerResult {
        let quant_depth = self.push_scope(variables.clone());
        let mut fixed_body = self.fold(*body);
        fixed_body.expr = self.push_temp(&fixed_body);
        fixed_body.dependencies.remove(&quant_depth);
        let wrappers = self.pop_scope().wrappers;
        FixerResult {
            expr: apply_wrappers(Expr::ForAll(
                variables,
                triggers,
                box fixed_body.expr,
                pos,
            ), wrappers),
            dependencies: fixed_body.dependencies,
            is_const: false,
        }
    }

    // same as fold_forall
    fn fold_exists(
        &mut self,
        variables: Vec<vir::LocalVar>,
        triggers: Vec<vir::Trigger>,
        body: Box<Expr>,
        pos: Position,
    ) -> FixerResult {
        let quant_depth = self.push_scope(variables.clone());
        let mut fixed_body = self.fold(*body);
        fixed_body.expr = self.push_temp(&fixed_body);
        fixed_body.dependencies.remove(&quant_depth);
        let wrappers = self.pop_scope().wrappers;
        FixerResult {
            expr: apply_wrappers(Expr::Exists(
                variables,
                triggers,
                box fixed_body.expr,
                pos,
            ), wrappers),
            dependencies: fixed_body.dependencies,
            is_const: false,
        }
    }

    // unfolding is strictly heap-dependent, so should be always pulled out
    // (all the way), because we don't quantify over Refs
    fn fold_unfolding(
        &mut self,
        name: String,
        args: Vec<Expr>,
        expr: Box<Expr>,
        perm: vir::PermAmount,
        variant: vir::MaybeEnumVariantIndex,
        pos: Position,
    ) -> FixerResult {
        self.scopes[0].wrappers.push(ExprFixerWrapper::Unfolding {
            name,
            args,
            perm,
            variant,
            pos,
        });
        self.fold(*expr)
    }

    fn fold_local(&mut self, v: vir::LocalVar, p: Position) -> FixerResult {
        let mut dependencies = HashSet::new();
        for i in (0..self.scopes.len()).rev() {
            if self.scopes[i].bound_vars.contains(&v) {
                dependencies.insert(i + 1);
                break;
            }
        }
        FixerResult {
            expr: Expr::Local(v, p),
            dependencies,
            is_const: false,
        }
    }

    fn fold_magic_wand(
        &mut self,
        _lhs: Box<Expr>,
        _rhs: Box<Expr>,
        _borrow: Option<vir::borrows::Borrow>,
        _pos: Position,
    ) -> FixerResult {
        unimplemented!("magic wand should not appear in a quantifier")
    }

    fn fold_let_expr(
        &mut self,
        _var: vir::LocalVar,
        _expr: Box<Expr>,
        _body: Box<Expr>,
        _pos: Position,
    ) -> FixerResult {
        unimplemented!("let expression should not appear in a quantifier")
    }

    fn fold(&mut self, e: Expr) -> FixerResult {
        match e {
            Expr::Local(v, p) => self.fold_local(v, p),
            Expr::Variant(base, variant, p) => self.fold_variant(base, variant, p),
            Expr::Field(e, f, p) => self.fold_field(e, f, p),
            Expr::AddrOf(e, t, p) => self.fold_addr_of(e, t, p),
            Expr::Const(x, p) => self.fold_const(x, p),
            Expr::LabelledOld(x, y, p) => self.fold_labelled_old(x, y, p),
            Expr::MagicWand(x, y, b, p) => self.fold_magic_wand(x, y, b, p),
            Expr::PredicateAccessPredicate(x, y, z, p) => {
                self.fold_predicate_access_predicate(x, y, z, p)
            }
            Expr::FieldAccessPredicate(x, y, p) => self.fold_field_access_predicate(x, y, p),
            Expr::UnaryOp(x, y, p) => self.fold_unary_op(x, y, p),
            Expr::BinOp(x, y, z, p) => self.fold_bin_op(x, y, z, p),
            Expr::Unfolding(x, y, z, perm, variant, p) => {
                self.fold_unfolding(x, y, z, perm, variant, p)
            },
            Expr::Cond(x, y, z, p) => self.fold_cond(x, y, z, p),
            Expr::ForAll(x, y, z, p) => self.fold_forall(x, y, z, p),
            Expr::Exists(x, y, z, p) => self.fold_exists(x, y, z, p),
            Expr::LetExpr(x, y, z, p) => self.fold_let_expr(x, y, z, p),
            Expr::FuncApp(x, y, z, k, p) => self.fold_func_app(x, y, z, k, p),
            Expr::DomainFuncApp(x, y, p) => self.fold_domain_func_app(x, y, p),
            // TODO Expr::DomainFuncApp(u, v, w, x, y, p) => self.fold_domain_func_app(u,v,w,x,y,p),
            Expr::InhaleExhale(x, y, p) => self.fold_inhale_exhale(x, y, p),
            Expr::Downcast(b, p, f) => self.fold_downcast(b, p, f),
            Expr::SnapApp(e, p) => self.fold_snap_app(e, p),
            Expr::ContainerOp(x, y, z, p) => self.fold_container_op(x, y, z, p),
            Expr::Seq(x, y, p) => self.fold_seq(x, y, p),
        }
    }

    fn fold_variant(&mut self, base: Box<Expr>, variant: vir::Field, p: Position) -> FixerResult {
        self.combine(
            &[*base],
            |ops| Expr::Variant(box ops[0].clone(), variant, p),
        )
    }
    fn fold_field(&mut self, receiver: Box<Expr>, field: vir::Field, pos: Position) -> FixerResult {
        self.combine(
            &[*receiver],
            |ops| Expr::Field(box ops[0].clone(), field, pos),
        )
    }
    fn fold_addr_of(&mut self, e: Box<Expr>, t: Type, p: Position) -> FixerResult {
        self.combine(
            &[*e],
            |ops| Expr::AddrOf(box ops[0].clone(), t, p),
        )
    }
    fn fold_const(&mut self, x: vir::Const, p: Position) -> FixerResult {
        FixerResult {
            expr: Expr::Const(x, p),
            dependencies: HashSet::new(),
            is_const: true,
        }
    }
    fn fold_labelled_old(
        &mut self,
        label: String,
        body: Box<Expr>,
        pos: Position
    ) -> FixerResult {
        self.combine(
            &[*body],
            |ops| Expr::LabelledOld(label, box ops[0].clone(), pos),
        )
    }
    fn fold_predicate_access_predicate(
        &mut self,
        name: String,
        arg: Box<Expr>,
        perm_amount: vir::PermAmount,
        pos: Position,
    ) -> FixerResult {
        self.combine(
            &[*arg],
            |ops| Expr::PredicateAccessPredicate(
                name,
                box ops[0].clone(),
                perm_amount,
                pos,
            ),
        )
    }
    fn fold_field_access_predicate(
        &mut self,
        receiver: Box<Expr>,
        perm_amount: vir::PermAmount,
        pos: Position
    ) -> FixerResult {
        self.combine(
            &[*receiver],
            |ops| Expr::FieldAccessPredicate(box ops[0].clone(), perm_amount, pos),
        )
    }
    fn fold_unary_op(&mut self, x: vir::UnaryOpKind, y: Box<Expr>, p: Position) -> FixerResult {
        self.combine(
            &[*y],
            |ops| Expr::UnaryOp(x, box ops[0].clone(), p),
        )
    }
    fn fold_bin_op(
        &mut self,
        kind: vir::BinOpKind,
        first: Box<Expr>,
        second: Box<Expr>,
        pos: Position
    ) -> FixerResult {
        self.combine(
            &[*first, *second],
            |ops| Expr::BinOp(
                kind,
                box ops[0].clone(),
                box ops[1].clone(),
                pos,
            ),
        )
    }
    fn fold_cond(
        &mut self,
        guard: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
        pos: Position
    ) -> FixerResult {
        self.combine(
            &[*guard, *then_expr, *else_expr],
            |ops| Expr::Cond(
                box ops[0].clone(),
                box ops[1].clone(),
                box ops[2].clone(),
                pos,
            ),
        )
    }
    fn fold_func_app(
        &mut self,
        name: String,
        args: Vec<Expr>,
        formal_args: Vec<vir::LocalVar>,
        return_type: Type,
        pos: Position,
    ) -> FixerResult {
        self.combine(
            &args,
            |ops| Expr::FuncApp(
                name,
                ops.clone(),
                formal_args,
                return_type,
                pos,
            ),
        )
    }
    fn fold_domain_func_app(
        &mut self,
        func: vir::DomainFunc,
        args: Vec<Expr>,
        pos: Position,
    ) -> FixerResult {
        self.combine(
            &args,
            |ops| Expr::DomainFuncApp(
                func,
                ops.clone(),
                pos,
            ),
        )
    }
    /* TODO
    fn fold_domain_func_app(
        &mut self,
        function_name: String,
        args: Vec<Expr>,
        formal_args: Vec<LocalVar>,
        return_type: Type,
        domain_name: String,
        pos: Position,
    ) -> FixerResult {
        self.combine(
            &args,
            |ops| Expr::DomainFuncApp(
                function_name,
                ops.clone(),
                formal_args,
                return_type,
                domain_name,
                pos,
            ),
        )
    }
    */
    fn fold_inhale_exhale(
        &mut self,
        _inhale_expr: Box<Expr>,
        _exhale_expr: Box<Expr>,
        _pos: Position,
    ) -> FixerResult {
        unimplemented!("inhale/exhale expression should not appear in a quantifier")
    }
    fn fold_downcast(
        &mut self,
        base: Box<Expr>,
        enum_place: Box<Expr>,
        field: vir::Field,
    ) -> FixerResult {
        self.combine(
            &[*base, *enum_place],
            |ops| Expr::Downcast(box ops[0].clone(), box ops[1].clone(), field),
        )
    }
    fn fold_snap_app(&mut self, e: Box<Expr>, p: Position) -> FixerResult {
        self.combine(
            &[*e],
            |ops| Expr::SnapApp(box ops[0].clone(), p),
        )
    }
    fn fold_container_op(
        &mut self,
        kind: vir::ContainerOpKind,
        l: Box<Expr>,
        r: Box<Expr>,
        p: Position,
    ) -> FixerResult {
        self.combine(
            &[*l, *r],
            |ops| Expr::ContainerOp(
                kind,
                box ops[0].clone(),
                box ops[1].clone(),
                p,
            ),
        )
    }
    fn fold_seq(&mut self, t: Type, elems: Vec<Expr>, p: Position) -> FixerResult {
        self.combine(
            &elems,
            |ops| Expr::Seq(t, ops.clone(), p),
        )
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_fixer() {
        use super::*;
        use crate::vir_local;

        // no-op
        assert_eq!(
            vir! { true },
            CfgFixer::new().replace_expr(vir! { true }),
        );

        // same behaviour on forall and exists
        assert_eq!(
            Expr::LetExpr(
                vir_local!(_LET_0: Int),
                box vir! { ([ Expr::from(1) ] + [ Expr::from(2) ]) },
                box vir! { forall x: Int :: {} [ Expr::local(vir_local!(_LET_0: Int)) ] },
                Position::default(),
            ),
            CfgFixer::new().replace_expr(vir! {
                forall x: Int :: {}
                    ([ Expr::from(1) ] + [ Expr::from(2) ])
            }),
        );
        assert_eq!(
            Expr::LetExpr(
                vir_local!(_LET_0: Int),
                box vir! { ([ Expr::from(1) ] + [ Expr::from(2) ]) },
                box vir! { exists x: Int :: {} [ Expr::local(vir_local!(_LET_0: Int)) ] },
                Position::default(),
            ),
            CfgFixer::new().replace_expr(vir! {
                exists x: Int :: {}
                    ([ Expr::from(1) ] + [ Expr::from(2) ])
            }),
        );

        // multiple temporary vars
        assert_eq!(
            Expr::LetExpr(
                vir_local!(_LET_0: Int),
                box vir! { ([ Expr::from(1) ] + [ Expr::from(2) ]) },
                box Expr::LetExpr(
                    vir_local!(_LET_1: Int),
                    box vir! { ([ Expr::from(3) ] + [ Expr::from(4) ]) },
                    box vir! {
                        forall x: Int :: {}
                            (([ Expr::local(vir_local!(_LET_0: Int)) ]
                                + [ Expr::local(vir_local!(x: Int)) ])
                            + [ Expr::local(vir_local!(_LET_1: Int)) ])
                    },
                    Position::default(),
                ),
                Position::default(),
            ),
            CfgFixer::new().replace_expr(vir! {
                forall x: Int :: {}
                    ((([ Expr::from(1) ] + [ Expr::from(2) ])
                        + [ Expr::local(vir_local!(x: Int)) ])
                    + ([ Expr::from(3) ] + [ Expr::from(4) ]))
            }),
        );

        // binop with bound vars
        assert_eq!(
            Expr::LetExpr(
                vir_local!(_LET_0: Int),
                box vir! { ([ Expr::from(1) ] + [ Expr::from(2) ]) },
                box vir! {
                    forall x: Int :: {}
                        ([ Expr::local(vir_local!(_LET_0: Int)) ] + [ Expr::local(vir_local!(x: Int)) ])
                },
                Position::default(),
            ),
            CfgFixer::new().replace_expr(vir! {
                forall x: Int :: {}
                    (([ Expr::from(1) ] + [ Expr::from(2) ]) + [ Expr::local(vir_local!(x: Int)) ])
            }),
        );

        // nested quantifiers
        assert_eq!(
            Expr::LetExpr(
                vir_local!(_LET_0: Int),
                box vir! { ([ Expr::from(1) ] + [ Expr::from(2) ]) },
                box vir! {
                    forall x: Int :: {}
                        [Expr::LetExpr(
                            vir_local!(_LET_1: Int),
                            box vir! { ([ Expr::local(vir_local!(_LET_0: Int)) ]
                                            + [ Expr::local(vir_local!(x: Int)) ]) },
                            box vir! {
                                exists y: Int :: {}
                                    ([ Expr::local(vir_local!(_LET_1: Int)) ]
                                    * [ Expr::local(vir_local!(y: Int)) ])
                            },
                            Position::default(),
                        )]
                },
                Position::default(),
            ),
            CfgFixer::new().replace_expr(vir! {
                forall x: Int :: {}
                    (exists y: Int :: {}
                        ((([ Expr::from(1) ] + [ Expr::from(2) ])
                            + [ Expr::local(vir_local!(x: Int)) ])
                        * [ Expr::local(vir_local!(y: Int)) ]))
            }),
        );

        // shadowing (shouldn't happen in Prusti-generated VIR)
        assert_eq!(
            Expr::LetExpr(
                vir_local!(_LET_0: Bool),
                box vir! {
                    ((([ Expr::local(vir_local!(y: Int)) ] + [ Expr::from(1) ]) == [ Expr::from(2) ])
                    && (exists y: Int :: {}
                        [ Expr::local(vir_local!(y: Int)) ]))
                },
                box vir! {
                    forall x: Int :: {}
                        [ Expr::local(vir_local!(_LET_0: Bool)) ]
                },
                Position::default(),
            ),
            CfgFixer::new().replace_expr(vir! {
                forall x: Int :: {}
                    ((([ Expr::local(vir_local!(y: Int)) ] + [ Expr::from(1) ]) == [ Expr::from(2) ])
                    && (exists y: Int :: {}
                        [ Expr::local(vir_local!(y: Int)) ]))
            }),
        );
    }
}
