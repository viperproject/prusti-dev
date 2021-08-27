// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::config;
use std::collections::HashMap;
use viper::{self, AstFactory};
use crate::vir::{
    ast::*,
    cfg::{CfgMethod, CfgBlock, Successor, RETURN_LABEL},
    borrows::borrow_id,
    Program,
};
use prusti_utils::force_matches;
use itertools::Itertools;

pub trait ToViper<'v, T> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> T;
}

pub trait ToViperDecl<'v, T> {
    fn to_viper_decl(&self, ast: &AstFactory<'v>) -> T;
}

impl<'v> ToViper<'v, viper::Program<'v>> for Program {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Program<'v> {
        let domains = self.domains.to_viper(ast);
        let fields = self.fields.to_viper(ast);

        let mut viper_methods: Vec<_> = self.methods.iter().map(|m| m.to_viper(ast)).collect();
        viper_methods.extend(self.builtin_methods.iter().map(|m| m.to_viper(ast)));
        if config::verify_only_preamble() {
            viper_methods = Vec::new();
        }

        let mut viper_functions: Vec<_> = self.functions.iter().map(|f| f.to_viper(ast)).collect();
        let predicates = self.viper_predicates.to_viper(ast);

        info!(
            "Viper encoding uses {} domains, {} fields, {} functions, {} predicates, {} methods",
            domains.len(),
            fields.len(),
            viper_functions.len(),
            predicates.len(),
            viper_methods.len()
        );

        // Add a function that represents the symbolic read permission amount.
        viper_functions.push(ast.function(
            "read$",
            &[],
            ast.perm_type(),
            &[],
            &[
                ast.lt_cmp(ast.no_perm(), ast.result_with_pos(ast.perm_type(), ast.no_position())),
                ast.lt_cmp(ast.result_with_pos(ast.perm_type(), ast.no_position()), ast.full_perm()),
            ],
            ast.no_position(),
            None,
        ));

        ast.program(
            &domains,
            &fields,
            &viper_functions,
            &predicates,
            &viper_methods,
        )
    }
}

impl<'v> ToViper<'v, viper::Position<'v>> for Position {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Position<'v> {
        ast.identifier_position(self.line(), self.column(), self.id().to_string())
    }
}

impl<'v> ToViper<'v, viper::Type<'v>> for Type {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Type<'v> {
        match self {
            Type::Int => ast.int_type(),
            Type::Bool => ast.bool_type(),
            //Type::Ref |
            Type::TypedRef(_) => ast.ref_type(),
            Type::Domain(ref name) => ast.domain_type(&name, &[], &[]),
            Type::Snapshot(ref name) => ast.domain_type(&format!("Snap${}", name), &[], &[]),
            Type::Seq(ref elem_ty) => ast.seq_type(elem_ty.to_viper(ast))
        }
    }
}

impl<'v, 'a, 'b> ToViper<'v, viper::Expr<'v>> for (&'a LocalVar, &'b Position) {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        if self.0.name == "__result" {
            ast.result_with_pos(self.0.typ.to_viper(ast), self.1.to_viper(ast))
        } else {
            ast.local_var_with_pos(&self.0.name, self.0.typ.to_viper(ast), self.1.to_viper(ast))
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

impl<'v> ToViper<'v, viper::Stmt<'v>> for Stmt {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        match self {
            Stmt::Comment(ref comment) => ast.comment(&comment),
            Stmt::Label(ref label) => ast.label(&label, &[]),
            Stmt::Inhale(ref expr) => {
                let fake_position = Position::default();
                ast.inhale(expr.to_viper(ast), fake_position.to_viper(ast))
            }
            Stmt::Exhale(ref expr, ref pos) => {
                assert!(!pos.is_default(), "stmt with default pos: {}", self);
                ast.exhale(expr.to_viper(ast), pos.to_viper(ast))
            }
            Stmt::Assert(ref expr, ref pos) => {
                ast.assert(expr.to_viper(ast), pos.to_viper(ast))
            }
            Stmt::MethodCall(ref method_name, ref args, ref targets) => {
                let fake_position = Position::default();
                ast.method_call(
                    &method_name,
                    &args.to_viper(ast),
                    &(targets, &fake_position).to_viper(ast),
                )
            }
            Stmt::Assign(ref lhs, ref rhs, _) => {
                ast.abstract_assign(lhs.to_viper(ast), rhs.to_viper(ast))
            }
            Stmt::Fold(ref pred_name, ref args, perm, ref _variant, ref pos) => ast.fold_with_pos(
                ast.predicate_access_predicate_with_pos(
                    ast.predicate_access_with_pos(
                        &args.to_viper(ast),
                        &pred_name,
                        pos.to_viper(ast),
                    ),
                    perm.to_viper(ast),
                    pos.to_viper(ast),
                ),
                pos.to_viper(ast),
            ),
            Stmt::Unfold(ref pred_name, ref args, perm, ref _variant) => {
                ast.unfold(ast.predicate_access_predicate(
                    ast.predicate_access(&args.to_viper(ast), &pred_name),
                    perm.to_viper(ast),
                ))
            }
            Stmt::Obtain(ref _expr, _) => {
                // Skip
                ast.comment(&self.to_string())
            }
            Stmt::BeginFrame => {
                // Skip
                ast.comment(&self.to_string())
            }
            Stmt::EndFrame => {
                // Skip
                ast.comment(&self.to_string())
            }
            Stmt::TransferPerm(ref _expiring, ref _restored, _unchecked) => {
                // Skip
                ast.comment(&self.to_string())
            }
            Stmt::PackageMagicWand(ref wand, ref package_stmts, ref _label, ref vars, ref pos) => {
                // FIXME: When packaging a magic wand, Silicon needs help in showing that it has
                // access to the needed paths.
                fn stmt_to_viper_in_packge<'v>(
                    stmt: &Stmt,
                    ast: &AstFactory<'v>,
                ) -> viper::Stmt<'v> {
                    let create_footprint_asserts = |expr: &Expr, perm| -> Vec<viper::Stmt> {
                        expr.compute_footprint(perm)
                            .into_iter()
                            .map(|access| {
                                let fake_position = Position::default();
                                let assert =
                                    Stmt::Assert(access, fake_position);
                                assert.to_viper(ast)
                            })
                            .collect()
                    };
                    match stmt {
                        Stmt::Assign(ref lhs, ref rhs, _) => {
                            let mut stmts = create_footprint_asserts(rhs, PermAmount::Read);
                            stmts.push(ast.abstract_assign(lhs.to_viper(ast), rhs.to_viper(ast)));
                            ast.seqn(stmts.as_slice(), &[])
                        }
                        Stmt::Exhale(ref expr, ref pos) => {
                            assert!(!pos.is_default());
                            let mut stmts = create_footprint_asserts(expr, PermAmount::Read);
                            stmts.push(ast.exhale(expr.to_viper(ast), pos.to_viper(ast)));
                            ast.seqn(stmts.as_slice(), &[])
                        }
                        Stmt::Fold(ref pred_name, ref args, perm, ref _variant, ref pos) => {
                            assert_eq!(args.len(), 1);
                            let place = &args[0];
                            assert!(place.is_place());
                            let mut stmts = create_footprint_asserts(place, PermAmount::Read);
                            stmts.push(ast.fold_with_pos(
                                ast.predicate_access_predicate_with_pos(
                                    ast.predicate_access_with_pos(
                                        &args.to_viper(ast),
                                        &pred_name,
                                        pos.to_viper(ast),
                                    ),
                                    perm.to_viper(ast),
                                    pos.to_viper(ast),
                                ),
                                pos.to_viper(ast),
                            ));
                            ast.seqn(stmts.as_slice(), &[])
                        }
                        Stmt::If(ref guard, ref then_stmts, ref else_stmts) => {
                            let then_stmts: Vec<_> = then_stmts.iter()
                                .map(|stmt| stmt_to_viper_in_packge(stmt, ast))
                                .collect();
                            let else_stmts: Vec<_> = else_stmts.iter()
                                .map(|stmt| stmt_to_viper_in_packge(stmt, ast))
                                .collect();
                            ast.if_stmt(
                                guard.to_viper(ast),
                                ast.seqn(&then_stmts, &[]),
                                ast.seqn(&else_stmts, &[]),
                            )
                        }
                        _ => stmt.to_viper(ast),
                    }
                }
                let stmts: Vec<_> = package_stmts
                    .iter()
                    .map(|stmt| stmt_to_viper_in_packge(stmt, ast))
                    .collect();
                let var_decls: Vec<_> = vars
                    .into_iter()
                    .map(|var| var.to_viper_decl(ast).into())
                    .collect();
                ast.package(
                    wand.to_viper(ast),
                    ast.seqn(&stmts, &var_decls),
                    pos.to_viper(ast),
                )
            }
            Stmt::ApplyMagicWand(ref wand, ref pos) => {
                let inhale = force_matches!(wand, Expr::MagicWand(_, _, Some(borrow), _) => {
                    let borrow: usize = borrow_id(*borrow);
                    let borrow: Expr = borrow.into();
                    ast.inhale(
                        ast.predicate_access_predicate(
                            ast.predicate_access(&[borrow.to_viper(ast)], "DeadBorrowToken$"),
                            ast.full_perm(),
                        ),
                        pos.to_viper(ast),
                    )
                });
                let position = ast.identifier_position(pos.line(), pos.column(), &pos.id().to_string());
                let apply = ast.apply(wand.to_viper(ast), position);
                ast.seqn(&[inhale, apply], &[])
            }
            Stmt::ExpireBorrows(_) => {
                // Skip
                ast.comment(&self.to_string())
            }
            Stmt::If(ref guard, ref then_stmts, ref else_stmts) => ast.if_stmt(
                guard.to_viper(ast),
                ast.seqn(&then_stmts.to_viper(ast), &[]),
                ast.seqn(&else_stmts.to_viper(ast), &[]),
            ),
            Stmt::Downcast(..) => {
                // Skip
                ast.comment(&self.to_string())
            }
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for PermAmount {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        match self {
            PermAmount::Write => ast.full_perm(),
            PermAmount::Read => ast.func_app("read$", &[], ast.perm_type(), ast.no_position()),
            PermAmount::Remaining => ast.perm_sub(
                PermAmount::Write.to_viper(ast),
                PermAmount::Read.to_viper(ast),
            ),
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for FracPermAmount {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        ast.fractional_perm(self.left().to_viper(ast), self.right().to_viper(ast))
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for Expr {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        let expr = match self {
            Expr::Local(ref local_var, ref pos) => (local_var, pos).to_viper(ast),
            Expr::Variant(ref base, ref field, ref pos) => ast.field_access_with_pos(
                base.to_viper(ast),
                field.to_viper(ast),
                pos.to_viper(ast),
            ),
            Expr::Field(ref base, ref field, ref pos) => ast.field_access_with_pos(
                base.to_viper(ast),
                field.to_viper(ast),
                pos.to_viper(ast),
            ),
            Expr::AddrOf(..) => unreachable!(),
            Expr::Const(ref val, ref pos) => (val, pos).to_viper(ast),
            Expr::LabelledOld(ref old_label, ref expr, ref pos) => {
                ast.labelled_old_with_pos(expr.to_viper(ast), old_label, pos.to_viper(ast))
            }
            Expr::MagicWand(ref lhs, ref rhs, maybe_borrow, ref pos) => {
                let borrow_id = if let Some(borrow) = maybe_borrow {
                    borrow_id(*borrow) as isize
                } else {
                    -1
                };
                let borrow: Expr = borrow_id.into();
                let token = ast.predicate_access_predicate(
                    ast.predicate_access(&[borrow.to_viper(ast)], "DeadBorrowToken$"),
                    ast.full_perm(),
                );
                ast.magic_wand_with_pos(
                    ast.and_with_pos(token, lhs.to_viper(ast), pos.to_viper(ast)),
                    rhs.to_viper(ast),
                    pos.to_viper(ast),
                )
            }
            Expr::PredicateInstance(ref predicate_name, ref args, ref pos) => ast
                .predicate_access_with_pos(
                    &args.iter().map(|arg| arg.to_viper(ast)).collect::<Vec<_>>(),
                    predicate_name,
                    pos.to_viper(ast)
                ),
            Expr::PredicateAccessPredicate(ref predicate_name, ref arg, perm, ref pos) => ast
                .predicate_access_predicate_with_pos(
                    ast.predicate_access(&[arg.to_viper(ast)], predicate_name),
                    perm.to_viper(ast),
                    pos.to_viper(ast),
                ),
            Expr::CreditAccessPredicate(ref predicate_name, ref args, ref frac_perm, ref pos) => ast
                .predicate_access_predicate_with_pos(
                    ast.predicate_access(
                        &args.iter()
                            .map(|arg| arg.to_viper(ast))
                            .collect::<Vec<_>>(),
                        predicate_name),
                    frac_perm.to_viper(ast),
                    pos.to_viper(ast),
                ),
            Expr::FieldAccessPredicate(ref loc, perm, ref pos) => ast
                .field_access_predicate_with_pos(
                    loc.to_viper(ast),
                    perm.to_viper(ast),
                    pos.to_viper(ast),
                ),
            Expr::PermEquality(ref expr, ref frac_perm, ref pos) => ast
                .eq_cmp_with_pos(
                    ast.current_perm(expr.to_viper(ast)),
                    frac_perm.to_viper(ast),
                    pos.to_viper(ast)
                ),
            Expr::UnaryOp(op, ref expr, ref pos) => match op {
                UnaryOpKind::Not => ast.not_with_pos(expr.to_viper(ast), pos.to_viper(ast)),
                UnaryOpKind::Minus => ast.minus_with_pos(expr.to_viper(ast), pos.to_viper(ast)),
            },
            Expr::BinOp(op, ref left, ref right, ref pos) => match op {
                BinOpKind::EqCmp => {
                    ast.eq_cmp_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
                BinOpKind::NeCmp => {
                    ast.ne_cmp_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
                BinOpKind::GtCmp => {
                    ast.gt_cmp_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
                BinOpKind::GeCmp => {
                    ast.ge_cmp_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
                BinOpKind::LtCmp => {
                    ast.lt_cmp_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
                BinOpKind::LeCmp => {
                    ast.le_cmp_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
                BinOpKind::Add => {
                    ast.add_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
                BinOpKind::Sub => {
                    ast.sub_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
                BinOpKind::Mul => {
                    ast.mul_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
                BinOpKind::Div => {
                    ast.div_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
                BinOpKind::Mod => {
                    ast.module_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
                BinOpKind::And => {
                    ast.and_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
                BinOpKind::Or => {
                    ast.or_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
                BinOpKind::Implies => {
                    ast.implies_with_pos(left.to_viper(ast), right.to_viper(ast), pos.to_viper(ast))
                }
            },
            Expr::ContainerOp(op_kind, box ref left, box ref right, _pos) => {
                match op_kind {
                    ContainerOpKind::SeqIndex => {
                        ast.seq_index(left.to_viper(ast), right.to_viper(ast))
                    }
                    ContainerOpKind::SeqConcat => {
                        ast.seq_append(left.to_viper(ast), right.to_viper(ast))
                    }
                    ContainerOpKind::SeqLen => {
                        ast.seq_length(left.to_viper(ast))
                    }
                }
            }
            Expr::Seq(ty, elems, _pos) => {
                let elem_ty = force_matches!(ty, Type::Seq(box elem_ty) => elem_ty);
                let viper_elem_ty = elem_ty.to_viper(ast);
                if elems.is_empty() {
                    ast.empty_seq(viper_elem_ty)
                } else {
                    let viper_elems = elems.iter().map(|e| e.to_viper(ast)).collect::<Vec<_>>();
                    ast.explicit_seq(&viper_elems)
                }
            }
            Expr::Unfolding(
                ref predicate_name,
                ref args,
                ref expr,
                perm,
                ref _variant,
                ref pos,
            ) => ast.unfolding_with_pos(
                ast.predicate_access_predicate(
                    ast.predicate_access(&args.to_viper(ast)[..], &predicate_name),
                    perm.to_viper(ast),
                ),
                expr.to_viper(ast),
                pos.to_viper(ast),
            ),
            Expr::Cond(ref guard, ref left, ref right, ref pos) => ast.cond_exp_with_pos(
                guard.to_viper(ast),
                left.to_viper(ast),
                right.to_viper(ast),
                pos.to_viper(ast),
            ),
            Expr::ForAll(ref vars, ref triggers, ref body, ref pos) => ast.forall_with_pos(
                &vars.to_viper_decl(ast)[..],
                &(triggers, pos).to_viper(ast),
                body.to_viper(ast),
                pos.to_viper(ast),
            ),
            Expr::Exists(ref vars, ref triggers, ref body, ref pos) => ast.exists_with_pos(
                &vars.to_viper_decl(ast)[..],
                &(triggers, pos).to_viper(ast),
                body.to_viper(ast),
                pos.to_viper(ast),
            ),
            Expr::LetExpr(ref var, ref expr, ref body, ref pos) => ast.let_expr_with_pos(
                var.to_viper_decl(ast),
                expr.to_viper(ast),
                body.to_viper(ast),
                pos.to_viper(ast),
            ),
            Expr::FuncApp(
                ref function_name,
                ref args,
                ref formal_args,
                ref return_type,
                ref pos,
            ) => {
                let identifier = compute_identifier(function_name, formal_args, return_type);
                ast.func_app(
                    &identifier,
                    &args.to_viper(ast),
                    return_type.to_viper(ast),
                    pos.to_viper(ast),
                )
            }
            Expr::DomainFuncApp(ref function, ref args, ref _pos) => {
                ast.domain_func_app(
                    function.to_viper(ast),
                    &args.to_viper(ast),
                    &[], // TODO not necessary so far
                )
            }
            /* TODO use once DomainFuncApp has been updated
            Expr::DomainFuncApp(
                ref function_name,
                ref args,
                ref formal_args,
                ref return_type,
                ref domain_name,
                ref pos,
            ) => {
                let identifier = compute_identifier(function_name, formal_args, return_type);
                ast.domain_func_app(
                    &identifier,
                    &args.to_viper(ast),
                    &[], // not necessary so far
                    return_type.to_viper(ast),
                    domain_name,
                    pos.to_viper(ast),
                )
            },
            */
            Expr::InhaleExhale(ref inhale_expr, ref exhale_expr, ref _pos) => {
                ast.inhale_exhale_pred(inhale_expr.to_viper(ast), exhale_expr.to_viper(ast))
            }
            Expr::Downcast(ref base, ..) => {
                base.to_viper(ast)
            }
            Expr::SnapApp(..) => unreachable!("unpatched snapshot operation"),
            // DEBUG: enable this version to see snap$(...) in the Viper output
            // for unpatched snapshot operations; this pushes the error to the
            // verifier, but at least allows inspecting the Viper program
            /*Expr::SnapApp(ref arg, ref pos) => {
                ast.func_app(
                    "snap$",
                    &[arg.to_viper(ast)],
                    self.get_type().to_viper(ast),
                    pos.to_viper(ast),
                )
            }*/
        };
        if config::simplify_encoding() {
            ast.simplified_expression(expr)
        } else {
            expr
        }
    }
}

impl<'v, 'a, 'b> ToViper<'v, viper::Trigger<'v>> for (&'a Trigger, &'b Position) {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Trigger<'v> {
        ast.trigger_with_pos(&self.0.elements().to_viper(ast)[..], self.1.to_viper(ast))
    }
}

impl<'v, 'a, 'b> ToViper<'v, viper::Expr<'v>> for (&'a Const, &'b Position) {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        match self.0 {
            Const::Bool(true) => ast.true_lit_with_pos(self.1.to_viper(ast)),
            Const::Bool(false) => ast.false_lit_with_pos(self.1.to_viper(ast)),
            Const::Int(x) => ast.int_lit_with_pos(*x, self.1.to_viper(ast)),
            Const::BigInt(ref x) => ast.int_lit_from_ref_with_pos(x, self.1.to_viper(ast)),
            Const::FnPtr => ast.null_lit_with_pos(self.1.to_viper(ast)),
        }
    }
}

impl<'v> ToViper<'v, viper::Predicate<'v>> for Predicate {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Predicate<'v> {
        match self {
            Predicate::Struct(p) => p.to_viper(ast),
            Predicate::Enum(p) => p.to_viper(ast),
            Predicate::Bodyless(name, this) => {
                ast.predicate(name, &[this.to_viper_decl(ast)], None)
            }
            Predicate::CreditUnit(p) => p.to_viper(ast),
        }
    }
}

impl<'v> ToViper<'v, viper::Predicate<'v>> for StructPredicate {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Predicate<'v> {
        ast.predicate(
            &self.name,
            &[self.this.to_viper_decl(ast)],
            self.body.as_ref().map(|b| b.to_viper(ast)),
        )
    }
}

impl<'v> ToViper<'v, viper::Predicate<'v>> for EnumPredicate {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Predicate<'v> {
        ast.predicate(
            &self.name,
            &[self.this.to_viper_decl(ast)],
            Some(self.body().to_viper(ast)),
        )
    }
}

impl<'v> ToViper<'v, viper::Predicate<'v>> for CreditUnitPredicate {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Predicate<'v> {
        ast.predicate(
            &self.name,
            &self.args.iter().map(|arg| arg.to_viper_decl(ast)).collect::<Vec<_>>(),
            self.body.as_ref().map(|b| b.to_viper(ast)),
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
            None,
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
            &self.get_identifier(),
            &self.formal_args.to_viper_decl(ast),
            self.return_type.to_viper(ast),
            &self.pres.to_viper(ast),
            &self.posts.to_viper(ast),
            ast.no_position(),
            self.body.as_ref().map(|b| b.to_viper(ast)),
        )
    }
}

impl<'a, 'v> ToViper<'v, viper::Domain<'v>> for &'a Domain {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Domain<'v> {
        ast.domain(
            &self.name,
            &self.functions.to_viper(ast),
            &self.axioms.to_viper(ast),
            &self.type_vars.to_viper(ast),
        )
    }
}

impl<'a, 'v> ToViper<'v, viper::DomainFunc<'v>> for &'a DomainFunc {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::DomainFunc<'v> {
        ast.domain_func(
            &self.get_identifier(),
            &self.formal_args.to_viper_decl(ast),
            self.return_type.to_viper(ast),
            self.unique,
            &self.domain_name,
        )
    }
}

impl<'a, 'v> ToViper<'v, viper::NamedDomainAxiom<'v>> for &'a DomainAxiom {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::NamedDomainAxiom<'v> {
        ast.named_domain_axiom(&self.name, self.expr.to_viper(ast), &self.domain_name)
    }
}

// Vectors

impl<'v> ToViper<'v, Vec<viper::Field<'v>>> for Vec<Field> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Field<'v>> {
        self.iter().map(|x| x.to_viper(ast)).collect()
    }
}

impl<'v, 'a, 'b> ToViper<'v, Vec<viper::Expr<'v>>> for (&'a Vec<LocalVar>, &'b Position) {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Expr<'v>> {
        self.0.iter().map(|x| (x, self.1).to_viper(ast)).collect()
    }
}

impl<'v, 'a, 'b> ToViper<'v, Vec<viper::Trigger<'v>>> for (&'a Vec<Trigger>, &'b Position) {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Trigger<'v>> {
        self.0.iter().map(|x| (x, self.1).to_viper(ast)).collect()
    }
}

impl<'v> ToViperDecl<'v, Vec<viper::LocalVarDecl<'v>>> for Vec<LocalVar> {
    fn to_viper_decl(&self, ast: &AstFactory<'v>) -> Vec<viper::LocalVarDecl<'v>> {
        self.iter().map(|x| x.to_viper_decl(ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::Domain<'v>>> for Vec<Domain> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Domain<'v>> {
        self.iter().map(|x| x.to_viper(ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::DomainFunc<'v>>> for Vec<DomainFunc> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::DomainFunc<'v>> {
        self.iter().map(|x| x.to_viper(ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::NamedDomainAxiom<'v>>> for Vec<DomainAxiom> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::NamedDomainAxiom<'v>> {
        self.iter().map(|x| x.to_viper(ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::Type<'v>>> for Vec<Type> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Type<'v>> {
        self.iter().map(|x| x.to_viper(ast)).collect()
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

impl<'v> ToViper<'v, viper::Method<'v>> for CfgMethod {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Method<'v> {
        (&self).to_viper(ast)
    }
}

impl<'a, 'v> ToViper<'v, viper::Method<'v>> for &'a CfgMethod {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Method<'v> {
        let mut blocks_ast: Vec<viper::Stmt> = vec![];
        let mut declarations: Vec<viper::Declaration> = vec![];

        for local_var in self.local_vars.iter() {
            declarations.push(local_var.to_viper_decl(ast).into());
        }
        for label in self.labels().iter() {
            let decl = ast.label(label, &[]);
            declarations.push(decl.into());
        }

        if config::enable_verify_only_basic_block_path() {
            let path = config::verify_only_basic_block_path();
            cfg_method_convert_basic_block_path(self, path, ast, &mut blocks_ast, &mut declarations);
            // self.convert_basic_block_path(path, ast, &mut blocks_ast, &mut declarations);
        } else {
            // Sort blocks by label, except for the first block
            let mut blocks: Vec<_> = self.basic_blocks.iter().enumerate().skip(1).collect();
            blocks.sort_by_key(|(index, _)| index_to_label(&self.basic_blocks_labels(), *index));
            if !self.basic_blocks.is_empty() {
                blocks.insert(0, (0, &self.basic_blocks[0]));
            }

            for (index, block) in blocks.into_iter() {
                blocks_ast.push(block_to_viper(ast, &self.basic_blocks_labels(), block, index));
                declarations.push(
                    ast.label(&index_to_label(&self.basic_blocks_labels(), index), &[])
                        .into(),
                );
            }
        }
        blocks_ast.push(ast.label(RETURN_LABEL, &[]));
        declarations.push(ast.label(RETURN_LABEL, &[]).into());

        let method_body = if !self.basic_blocks.is_empty() {
            Some(ast.seqn(&blocks_ast, &declarations))
        }
        else {
            None
        };

        let mut formal_returns_decl: Vec<viper::LocalVarDecl> = vec![];
        for local_var in self.get_formal_returns() {
            formal_returns_decl.push(local_var.to_viper_decl(ast));
        }

        let method = ast.method(
            &self.name(),
            &self.viper_formal_args.to_viper_decl(ast),
            &formal_returns_decl,
            &self.viper_preconditions.to_viper(ast),
            &self.viper_postconditions.to_viper(ast),
            method_body,
        );

        method
    }
}

fn cfg_method_convert_basic_block_path<'v>(
    cfg_method: &CfgMethod,
    mut path: Vec<String>,
    ast: &'v AstFactory,
    blocks_ast: &mut Vec<viper::Stmt<'v>>,
    declarations: &mut Vec<viper::Declaration<'v>>,
) {
    path.reverse();
    let mut remaining_blocks: HashMap<_, _> = cfg_method
        .basic_blocks
        .iter()
        .enumerate()
        .map(|(index, block)| {
            (
                index_to_label(&cfg_method.basic_blocks_labels(), index),
                (index, block),
            )
        })
        .collect();
    let mut current_label = index_to_label(&cfg_method.basic_blocks_labels(), 0);
    while let Some((index, block)) = remaining_blocks.remove(&current_label) {
        blocks_ast.push(block_to_viper(ast, &cfg_method.basic_blocks_labels(), block, index));
        declarations.push(
            ast.label(&index_to_label(&cfg_method.basic_blocks_labels(), index), &[])
                .into(),
        );

        let mut successors: Vec<_> = block
            .successor
            .get_following()
            .into_iter()
            .map(|ci| index_to_label(&cfg_method.basic_blocks_labels(), ci.index()))
            .collect();
        assert!(!successors.is_empty());

        if successors.len() == 1 {
            current_label = successors.pop().unwrap();
        } else if let Some(next_label) = path.pop() {
            current_label = next_label;
            assert!(
                successors.contains(&current_label),
                "successors: {:?} next_label: {:?}",
                successors,
                current_label
            );
        } else {
            break;
        }
    }

    for label in config::delete_basic_blocks() {
        let (index, block) = remaining_blocks.remove(&label).unwrap();
        let fake_position = Position::default();
        let stmts: Vec<viper::Stmt> = vec![
            ast.label(&label, &[]),
            ast.inhale(
                ast.false_lit_with_pos(fake_position.to_viper(ast)),
                fake_position.to_viper(ast),
            ),
            successor_to_viper(ast, index, &cfg_method.basic_blocks_labels(), &block.successor),
        ];
        blocks_ast.push(ast.seqn(&stmts, &[]));
        declarations.push(ast.label(&label, &[]).into());
    }

    for (label, (index, block)) in remaining_blocks {
        blocks_ast.push(block_to_viper(ast, &cfg_method.basic_blocks_labels(), block, index));
        declarations.push(ast.label(&label, &[]).into());
    }
}

impl<'v> ToViper<'v, Vec<viper::Method<'v>>> for Vec<CfgMethod> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Method<'v>> {
        self.iter().map(|x| x.to_viper(ast)).collect()
    }
}

fn index_to_label(basic_block_labels: &Vec<String>, index: usize) -> String {
    basic_block_labels[index].clone()
}

fn successor_to_viper<'a>(
    ast: &'a AstFactory,
    index: usize,
    basic_block_labels: &Vec<String>,
    successor: &Successor,
) -> viper::Stmt<'a> {
    match *successor {
        Successor::Undefined => panic!(
            "CFG block '{}' has no successor.",
            basic_block_labels[index].clone()
        ),
        Successor::Return => ast.goto(RETURN_LABEL),
        Successor::Goto(target) => ast.goto(&basic_block_labels[target.index()]),
        Successor::GotoSwitch(ref successors, ref default_target) => {
            let mut stmts: Vec<viper::Stmt<'a>> = vec![];
            for (test, target) in successors {
                let goto = ast.goto(&basic_block_labels[target.index()]);
                let skip = ast.seqn(&[], &[]);
                let conditional_goto = ast.if_stmt(test.to_viper(ast), goto, skip);
                stmts.push(conditional_goto);
            }
            let default_goto = ast.goto(&basic_block_labels[default_target.index()]);
            stmts.push(default_goto);
            ast.seqn(&stmts, &[])
        }
    }
}

fn block_to_viper<'a>(
    ast: &'a AstFactory,
    basic_block_labels: &Vec<String>,
    block: &CfgBlock,
    index: usize,
) -> viper::Stmt<'a> {
    let label = &basic_block_labels[index];
    let mut stmts: Vec<viper::Stmt> = vec![];
    stmts.push(ast.label(label, &[]));
    stmts.extend(block.stmts.to_viper(ast));
    stmts.push(successor_to_viper(
        ast,
        index,
        basic_block_labels,
        &block.successor,
    ));
    ast.seqn(&stmts, &[])
}
