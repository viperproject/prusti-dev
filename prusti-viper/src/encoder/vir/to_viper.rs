// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// TODO: Remove this and fix.
#![allow(deprecated)]

use encoder::vir::ast::*;
use viper;
use viper::AstFactory;
use prusti_interface::config;

pub trait ToViper<'v, T> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> T;
}

pub trait ToViperDecl<'v, T> {
    fn to_viper_decl(&self, ast: &AstFactory<'v>) -> T;
}

impl<'v> ToViper<'v, viper::Type<'v>> for Type {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Type<'v> {
        match self {
            &Type::Int => ast.int_type(),
            &Type::Bool => ast.bool_type(),
            //&Type::Ref |
            &Type::TypedRef(_) => ast.ref_type(),
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for LocalVar {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        if self.name == "__result" {
            ast.result(self.typ.to_viper(ast))
        } else {
            ast.local_var(&self.name, self.typ.to_viper(ast))
        }
    }
}

impl<'v> ToViperDecl<'v, viper::LocalVarDecl<'v>> for LocalVar {
    fn to_viper_decl(&self, ast: &AstFactory<'v>) -> viper::LocalVarDecl<'v> {
        ast.local_var_decl(&self.name, self.typ.to_viper(ast))
    }
}

impl<'v> ToViper<'v, viper::Field<'v>> for Field {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Field<'v> {
        ast.field(&self.name, self.typ.to_viper(ast))
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for Place {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        match self {
            Place::Base(local_var) => local_var.to_viper(ast),
            Place::Field(base, field) => ast.field_access(
                base.to_viper(ast),
                field.to_viper(ast),
            ),
            Place::AddrOf(..) => unreachable!(),
        }
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for Stmt {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        match self {
            &Stmt::Comment(ref comment) => ast.comment(&comment),
            &Stmt::Label(ref label) => ast.label(&label, &[]),
            &Stmt::Inhale(ref expr) => {
                let fake_position = ast.identifier_position(0, 0, "TODO");
                ast.inhale(expr.to_viper(ast), fake_position)
            },
            &Stmt::Exhale(ref expr, ref pos) => {
                let position = ast.identifier_position(pos.line(), pos.column(), &pos.id());
                ast.exhale(expr.to_viper(ast), position)
            },
            &Stmt::Assert(ref expr, ref pos) => {
                let position = ast.identifier_position(pos.line(), pos.column(), &pos.id());
                ast.assert(expr.to_viper(ast), position)
            },
            &Stmt::MethodCall(ref method_name, ref args, ref targets) => ast.method_call(
                &method_name,
                &args.to_viper(ast),
                &targets.to_viper(ast)
            ),
            &Stmt::Assign(ref lhs, ref rhs, _) => ast.abstract_assign(
                lhs.to_viper(ast),
                rhs.to_viper(ast)
            ),
            &Stmt::Fold(ref pred_name, ref args, frac) => ast.fold(
                ast.predicate_access_predicate(
                    ast.predicate_access(
                        &args.to_viper(ast),
                        &pred_name
                    ),
                    ast.fractional_perm(
                        ast.int_lit(*frac.numer() as i64),
                        ast.int_lit(*frac.denom() as i64),
                    )
                )
            ),
            &Stmt::Unfold(ref pred_name, ref args, frac) => ast.unfold(
                ast.predicate_access_predicate(
                    ast.predicate_access(
                        &args.to_viper(ast),
                        &pred_name
                    ),
                    ast.fractional_perm(
                        ast.int_lit(*frac.numer() as i64),
                        ast.int_lit(*frac.denom() as i64),
                    )
                )
            ),
            &Stmt::Obtain(ref expr) => {
                // Skip
                ast.comment(&self.to_string())
            }
            &Stmt::WeakObtain(ref expr) => {
                // Skip
                ast.comment(&self.to_string())
            }
            &Stmt::Havoc => {
                // Skip
                ast.comment(&self.to_string())
            }
            &Stmt::BeginFrame => {
                // Skip
                ast.comment(&self.to_string())
            }
            &Stmt::EndFrame => {
                // Skip
                ast.comment(&self.to_string())
            }
            &Stmt::TransferPerm(ref expiring, ref restored) => {
                // Skip
                ast.comment(&self.to_string())
            }
            &Stmt::ExpireBorrowsIf(ref guard, ref then_stmts, ref else_stmts) => {
                ast.if_stmt(
                    guard.to_viper(ast),
                    ast.seqn(
                        &then_stmts.to_viper(ast),
                        &[],
                    ),
                    ast.seqn(
                        &else_stmts.to_viper(ast),
                        &[],
                    ),
                )
            }
            &Stmt::StopExpiringLoans => {
                // Skip
                ast.comment(&self.to_string())
            }
            &Stmt::PackageMagicWand(ref lhs, ref rhs, ref package_stmts, ref then_stmts) => {
                let mut encoded_stmts = vec![];
                encoded_stmts.push(
                    ast.package(
                        ast.magic_wand(
                            lhs.to_viper(ast),
                            rhs.to_viper(ast),
                        ),
                        ast.seqn(
                            &package_stmts.to_viper(ast),
                            &[],
                        )
                    )
                );
                encoded_stmts.extend(
                    then_stmts.to_viper(ast)
                );
                ast.seqn(
                    &encoded_stmts,
                    &[],
                )
            }
            &Stmt::ApplyMagicWand(ref lhs, ref rhs) => {
                ast.apply(
                    ast.magic_wand(
                        lhs.to_viper(ast),
                        rhs.to_viper(ast),
                    ),
                )
            }
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for Expr {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        let expr = match self {
            &Expr::Const(ref val) => val.to_viper(ast),
            &Expr::Place(ref place) => place.to_viper(ast),
            &Expr::LabelledOld(ref old_label, ref expr) => ast.labelled_old(
                expr.to_viper(ast),
                old_label,
            ),
            &Expr::MagicWand(ref lhs, ref rhs) => ast.magic_wand(
                lhs.to_viper(ast),
                rhs.to_viper(ast)
            ),
            &Expr::PredicateAccessPredicate(ref predicate_name, ref args, frac) => ast.predicate_access_predicate(
                ast.predicate_access(
                    &args.to_viper(ast)[..],
                    &predicate_name
                ),
                ast.fractional_perm(
                    ast.int_lit(*frac.numer() as i64),
                    ast.int_lit(*frac.denom() as i64),
                )
            ),
            &Expr::FieldAccessPredicate(ref loc, frac) => ast.field_access_predicate(
                loc.to_viper(ast),
                ast.fractional_perm(
                    ast.int_lit(*frac.numer() as i64),
                    ast.int_lit(*frac.denom() as i64),
                )
            ),
            &Expr::UnaryOp(op, ref expr) => {
                match op {
                    UnaryOpKind::Not => ast.not(expr.to_viper(ast)),
                    UnaryOpKind::Minus => ast.minus(expr.to_viper(ast)),
                }
            },
            &Expr::BinOp(op, ref left, ref right) => {
                match op {
                    BinOpKind::EqCmp => ast.eq_cmp(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::GtCmp => ast.gt_cmp(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::GeCmp => ast.ge_cmp(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::LtCmp => ast.lt_cmp(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::LeCmp => ast.le_cmp(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::Add => ast.add(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::Sub => ast.sub(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::Mul => ast.mul(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::Div => ast.div(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::Mod => ast.module(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::And => ast.and(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::Or => ast.or(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::Implies => ast.implies(left.to_viper(ast), right.to_viper(ast)),
                }
            },
            &Expr::Unfolding(ref predicate_name, ref args, ref expr, frac) => ast.unfolding(
                ast.predicate_access_predicate(
                    ast.predicate_access(
                        &args.to_viper(ast)[..],
                        &predicate_name
                    ),
                    ast.fractional_perm(
                        ast.int_lit(*frac.numer() as i64),
                        ast.int_lit(*frac.denom() as i64),
                    )
                ),
                expr.to_viper(ast)
            ),
            &Expr::Cond(ref guard, ref left, ref right) => ast.cond_exp(
                guard.to_viper(ast),
                left.to_viper(ast),
                right.to_viper(ast)
            ),
            &Expr::ForAll(ref vars, ref triggers, ref body) => ast.forall(
                &vars.to_viper_decl(ast)[..],
                &triggers.to_viper(ast),
                body.to_viper(ast)
            ),
            &Expr::FuncApp(ref function_name, ref args, ref formal_args, ref return_type, ref pos) => {
                let position = ast.identifier_position(pos.line(), pos.column(), &pos.id());
                ast.func_app(
                    &function_name,
                    &args.to_viper(ast),
                    &formal_args.to_viper_decl(ast)[..],
                    return_type.to_viper(ast),
                    position
                )
            }
        };
        if config::simplify_expressions() {
            ast.simplified_expression(expr)
        } else {
            expr
        }
    }
}

impl<'v> ToViper<'v, viper::Trigger<'v>> for Trigger {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Trigger<'v> {
        ast.trigger(
            &self.elements().to_viper(ast)[..]
        )
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for Const {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        match self {
            &Const::Bool(true) => ast.true_lit(),
            &Const::Bool(false) => ast.false_lit(),
            &Const::Null => ast.null_lit(),
            &Const::Int(x) => ast.int_lit(x),
            &Const::BigInt(ref x) => ast.int_lit_from_ref(x),
        }
    }
}

impl<'v> ToViper<'v, viper::Predicate<'v>> for Predicate {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Predicate<'v> {
        ast.predicate(
            &self.name,
            &self.args.to_viper_decl(ast)[..],
            self.body.as_ref()
                .map(|b| b.to_viper(ast))
        )
    }
}

impl<'v> ToViper<'v, viper::Method<'v>> for BodylessMethod {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Method<'v> {
        (&self).to_viper(ast)
    }
}

impl<'a, 'v> ToViper<'v, viper::Method<'v>> for &'a BodylessMethod {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Method<'v> {
        ast.method(
            &self.name,
            &self.formal_args.to_viper_decl(ast),
            &self.formal_returns.to_viper_decl(ast),
            &[],
            &[],
            None
        )
    }
}

impl<'v> ToViper<'v, viper::Function<'v>> for Function {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Function<'v> {
        (&self).to_viper(ast)
    }
}

impl<'a, 'v> ToViper<'v, viper::Function<'v>> for &'a Function {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Function<'v> {
        ast.function(
            &self.name,
            &self.formal_args.to_viper_decl(ast),
            self.return_type.to_viper(ast),
            &self.pres.to_viper(ast),
            &self.posts.to_viper(ast),
            self.body.as_ref().map(|b| b.to_viper(ast))
        )
    }
}

// Vectors

impl<'v> ToViper<'v, Vec<viper::Field<'v>>> for Vec<Field> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Field<'v>> {
        self.iter().map(|x| x.to_viper(ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::Expr<'v>>> for Vec<LocalVar> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Expr<'v>> {
        self.iter().map(|x| x.to_viper(ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::Trigger<'v>>> for Vec<Trigger> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Trigger<'v>> {
        self.iter().map(|x| x.to_viper(ast)).collect()
    }
}

impl<'v> ToViperDecl<'v, Vec<viper::LocalVarDecl<'v>>> for Vec<LocalVar> {
    fn to_viper_decl(&self, ast: &AstFactory<'v>) -> Vec<viper::LocalVarDecl<'v>> {
        self.iter().map(|x| x.to_viper_decl(ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::Expr<'v>>> for Vec<Expr> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Expr<'v>> {
        self.iter().map(|x| x.to_viper(ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::Stmt<'v>>> for Vec<Stmt> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Stmt<'v>> {
        self.iter().map(|x| x.to_viper(ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::Predicate<'v>>> for Vec<Predicate> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Predicate<'v>> {
        self.iter().map(|x| x.to_viper(ast)).collect()
    }
}
