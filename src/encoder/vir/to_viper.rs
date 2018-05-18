// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper;
use viper::AstFactory;
use encoder::vir::ast::*;

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
        ast.local_var(&self.name, self.typ.to_viper(ast))
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
            )
        }
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for Stmt {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        match self {
            &Stmt::Comment(ref comment) => ast.comment(&comment),
            &Stmt::Label(ref label) => ast.label(&label, &[]),
            &Stmt::Inhale(ref expr) => ast.inhale(expr.to_viper(ast), ast.no_position()),
            &Stmt::Exhale(ref expr, _) => ast.exhale(expr.to_viper(ast), ast.no_position()),
            &Stmt::Assert(ref expr, _) => ast.assert(expr.to_viper(ast), ast.no_position()),
            &Stmt::MethodCall(ref method_name, ref args, ref targets) => ast.method_call(
                &method_name,
                &args.to_viper(ast),
                &targets.to_viper(ast)
            ),
            &Stmt::Assign(ref lhs, ref rhs) => ast.abstract_assign(
                lhs.to_viper(ast),
                rhs.to_viper(ast)
            ),
            &Stmt::New(ref local_var, ref fields) => ast.new_stmt(
                local_var.to_viper(ast),
                &fields.to_viper(ast)
            ),
            &Stmt::Fold(ref pred_name, ref args) => ast.fold(
                ast.predicate_access_predicate(
                    ast.predicate_access(
                        &args.to_viper(ast),
                        &pred_name
                    ),
                    ast.full_perm()
                )
            ),
            &Stmt::Unfold(ref pred_name, ref args) => ast.unfold(
                ast.predicate_access_predicate(
                    ast.predicate_access(
                        &args.to_viper(ast),
                        &pred_name
                    ),
                    ast.full_perm()
                )
            ),
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for Expr {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        match self {
            &Expr::Const(ref val) => val.to_viper(ast),
            &Expr::Place(ref place) => place.to_viper(ast),
            &Expr::Old(ref expr) => ast.old(expr.to_viper(ast)),
            &Expr::LabelledOld(ref expr, ref old_label) => ast.labelled_old(
                expr.to_viper(ast),
                old_label
            ),
            &Expr::MagicWand(ref lhs, ref rhs) => ast.magic_wand(
                lhs.to_viper(ast),
                rhs.to_viper(ast)
            ),
            &Expr::PredicateAccess(ref predicate_name, ref args) => ast.predicate_access(
                &args.to_viper(ast)[..],
                &predicate_name
            ),
            &Expr::PredicateAccessPredicate(ref loc, perm) => ast.predicate_access_predicate(
                loc.to_viper(ast),
                perm.to_viper(ast)
            ),
            &Expr::FieldAccessPredicate(ref loc, perm) => ast.field_access_predicate(
                loc.to_viper(ast),
                perm.to_viper(ast)
            ),
            &Expr::UnaryOp(op, ref expr) => {
                match op {
                    UnaryOpKind::Minus => ast.minus(expr.to_viper(ast)),
                    UnaryOpKind::Not => ast.not(expr.to_viper(ast))
                }
            },
            &Expr::BinOp(op, ref left, ref right) => {
                match op {
                    BinOpKind::EqCmp => ast.eq_cmp(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::GtCmp => ast.gt_cmp(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::LeCmp => ast.le_cmp(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::Add => ast.add(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::Sub => ast.sub(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::And => ast.and(left.to_viper(ast), right.to_viper(ast)),
                    BinOpKind::Implies => ast.implies(left.to_viper(ast), right.to_viper(ast)),
                }
            }
        }
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

impl<'v> ToViper<'v, viper::Expr<'v>> for Perm {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        if self.den != 0 && self.num == self.den {
            ast.full_perm()
        } else if self.den != 0 && self.num == 0 {
            ast.no_perm()
        } else {
            ast.fractional_perm(
                Expr::from(self.num).to_viper(ast),
                Expr::from(self.den).to_viper(ast)
            )
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
