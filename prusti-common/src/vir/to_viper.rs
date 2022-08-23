// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::low_to_viper::{Context, ToViper, ToViperDecl};
use crate::{
    config,
    vir::{
        ast::*,
        borrows::borrow_id,
        cfg::{CfgBlock, CfgMethod, Successor, RETURN_LABEL},
        Program,
    },
};
use log::info;
use prusti_utils::force_matches;
use std::collections::HashMap;
use viper::{self, AstFactory};
use vir::common::identifier::WithIdentifier;

impl<'v> ToViper<'v, viper::Program<'v>> for Program {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Program<'v> {
        let domains = self.domains.to_viper(context, ast);
        let fields = self.fields.to_viper(context, ast);

        let mut viper_methods: Vec<_> = self
            .methods
            .iter()
            .map(|m| m.to_viper(context, ast))
            .collect();
        viper_methods.extend(
            self.builtin_methods
                .iter()
                .map(|m| m.to_viper(context, ast)),
        );
        if config::verify_only_preamble() {
            viper_methods = Vec::new();
        }

        let mut viper_functions: Vec<_> = self
            .functions
            .iter()
            .map(|f| f.to_viper(context, ast))
            .collect();
        let predicates = self.viper_predicates.to_viper(context, ast);

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
                ast.lt_cmp(
                    ast.no_perm(),
                    ast.result_with_pos(ast.perm_type(), ast.no_position()),
                ),
                ast.lt_cmp(
                    ast.result_with_pos(ast.perm_type(), ast.no_position()),
                    ast.full_perm(),
                ),
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
    fn to_viper(&self, _context: Context, ast: &AstFactory<'v>) -> viper::Position<'v> {
        ast.identifier_position(self.line(), self.column(), self.id().to_string())
    }
}

impl<'v> ToViper<'v, viper::Type<'v>> for Type {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Type<'v> {
        match self {
            Type::Int => ast.int_type(),
            Type::Bool => ast.bool_type(),
            //Type::Ref |
            Type::TypedRef(_) => ast.ref_type(),
            Type::Domain(ref name) => ast.domain_type(name, &[], &[]),
            Type::Snapshot(ref name) => ast.domain_type(&format!("Snap${}", name), &[], &[]),
            Type::Seq(ref elem_ty) => ast.seq_type(elem_ty.to_viper(context, ast)),
            Type::Map(ref key_type, ref val_type) => ast.map_type(
                key_type.to_viper(context, ast),
                val_type.to_viper(context, ast),
            ),
            Type::Float(Float::F32) => ast.backend_f32_type(),
            Type::Float(Float::F64) => ast.backend_f64_type(),
            Type::BitVector(bv_size) => match bv_size {
                BitVector::Signed(BitVectorSize::BV8) | BitVector::Unsigned(BitVectorSize::BV8) => {
                    ast.backend_bv8_type()
                }
                BitVector::Signed(BitVectorSize::BV16)
                | BitVector::Unsigned(BitVectorSize::BV16) => ast.backend_bv16_type(),
                BitVector::Signed(BitVectorSize::BV32)
                | BitVector::Unsigned(BitVectorSize::BV32) => ast.backend_bv32_type(),
                BitVector::Signed(BitVectorSize::BV64)
                | BitVector::Unsigned(BitVectorSize::BV64) => ast.backend_bv64_type(),
                BitVector::Signed(BitVectorSize::BV128)
                | BitVector::Unsigned(BitVectorSize::BV128) => ast.backend_bv128_type(),
            },
        }
    }
}

impl<'v, 'a, 'b> ToViper<'v, viper::Expr<'v>> for (&'a LocalVar, &'b Position) {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        if self.0.name == "__result" {
            ast.result_with_pos(
                self.0.typ.to_viper(context, ast),
                self.1.to_viper(context, ast),
            )
        } else {
            ast.local_var_with_pos(
                &self.0.name,
                self.0.typ.to_viper(context, ast),
                self.1.to_viper(context, ast),
            )
        }
    }
}

impl<'v> ToViperDecl<'v, viper::LocalVarDecl<'v>> for LocalVar {
    fn to_viper_decl(&self, context: Context, ast: &AstFactory<'v>) -> viper::LocalVarDecl<'v> {
        ast.local_var_decl(&self.name, self.typ.to_viper(context, ast))
    }
}

impl<'v> ToViper<'v, viper::Field<'v>> for Field {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Field<'v> {
        ast.field(&self.name, self.typ.to_viper(context, ast))
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for Stmt {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        match self {
            Stmt::Comment(ref comment) => ast.comment(comment),
            Stmt::Label(ref label) => ast.label(label, &[]),
            Stmt::Inhale(ref expr) => {
                let fake_position = Position::default();
                ast.inhale(
                    expr.to_viper(context, ast),
                    fake_position.to_viper(context, ast),
                )
            }
            Stmt::Exhale(ref expr, ref pos) => {
                assert!(!pos.is_default(), "stmt with default pos: {}", self);
                ast.exhale(expr.to_viper(context, ast), pos.to_viper(context, ast))
            }
            Stmt::Assert(ref expr, ref pos) => {
                ast.assert(expr.to_viper(context, ast), pos.to_viper(context, ast))
            }
            Stmt::MethodCall(ref method_name, ref args, ref targets) => {
                let fake_position = Position::default();
                ast.method_call(
                    method_name,
                    &args.to_viper(context, ast),
                    &(targets, &fake_position).to_viper(context, ast),
                )
            }
            Stmt::Assign(ref lhs, ref rhs, _) => {
                ast.abstract_assign(lhs.to_viper(context, ast), rhs.to_viper(context, ast))
            }
            Stmt::Fold(ref pred_name, ref args, perm, ref _variant, ref pos) => ast.fold_with_pos(
                ast.predicate_access_predicate_with_pos(
                    ast.predicate_access_with_pos(
                        &args.to_viper(context, ast),
                        pred_name,
                        pos.to_viper(context, ast),
                    ),
                    perm.to_viper(context, ast),
                    pos.to_viper(context, ast),
                ),
                pos.to_viper(context, ast),
            ),
            Stmt::Unfold(ref pred_name, ref args, perm, ref _variant) => {
                ast.unfold(ast.predicate_access_predicate(
                    ast.predicate_access(&args.to_viper(context, ast), pred_name),
                    perm.to_viper(context, ast),
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
                    context: Context,
                    ast: &AstFactory<'v>,
                ) -> viper::Stmt<'v> {
                    let create_footprint_asserts = |expr: &Expr, perm| -> Vec<viper::Stmt> {
                        expr.compute_footprint(perm)
                            .into_iter()
                            .map(|access| {
                                let fake_position = Position::default();
                                let assert = Stmt::Assert(access, fake_position);
                                assert.to_viper(context, ast)
                            })
                            .collect()
                    };
                    match stmt {
                        Stmt::Assign(ref lhs, ref rhs, _) => {
                            let mut stmts = create_footprint_asserts(rhs, PermAmount::Read);
                            stmts.push(ast.abstract_assign(
                                lhs.to_viper(context, ast),
                                rhs.to_viper(context, ast),
                            ));
                            ast.seqn(stmts.as_slice(), &[])
                        }
                        Stmt::Exhale(ref expr, ref pos) => {
                            assert!(!pos.is_default());
                            let mut stmts = create_footprint_asserts(expr, PermAmount::Read);
                            stmts.push(
                                ast.exhale(expr.to_viper(context, ast), pos.to_viper(context, ast)),
                            );
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
                                        &args.to_viper(context, ast),
                                        pred_name,
                                        pos.to_viper(context, ast),
                                    ),
                                    perm.to_viper(context, ast),
                                    pos.to_viper(context, ast),
                                ),
                                pos.to_viper(context, ast),
                            ));
                            ast.seqn(stmts.as_slice(), &[])
                        }
                        Stmt::If(ref guard, ref then_stmts, ref else_stmts) => {
                            let then_stmts: Vec<_> = then_stmts
                                .iter()
                                .map(|stmt| stmt_to_viper_in_packge(stmt, context, ast))
                                .collect();
                            let else_stmts: Vec<_> = else_stmts
                                .iter()
                                .map(|stmt| stmt_to_viper_in_packge(stmt, context, ast))
                                .collect();
                            ast.if_stmt(
                                guard.to_viper(context, ast),
                                ast.seqn(&then_stmts, &[]),
                                ast.seqn(&else_stmts, &[]),
                            )
                        }
                        _ => stmt.to_viper(context, ast),
                    }
                }
                let stmts: Vec<_> = package_stmts
                    .iter()
                    .map(|stmt| stmt_to_viper_in_packge(stmt, context, ast))
                    .collect();
                let var_decls: Vec<_> = vars
                    .iter()
                    .map(|var| var.to_viper_decl(context, ast).into())
                    .collect();
                ast.package(
                    wand.to_viper(context, ast),
                    ast.seqn(&stmts, &var_decls),
                    pos.to_viper(context, ast),
                )
            }
            Stmt::ApplyMagicWand(ref wand, ref pos) => {
                let inhale = force_matches!(wand, Expr::MagicWand(_, _, Some(borrow), _) => {
                    let borrow: usize = borrow_id(*borrow);
                    let borrow: Expr = borrow.into();
                    ast.inhale(
                        ast.predicate_access_predicate(
                            ast.predicate_access(&[borrow.to_viper(context, ast)], "DeadBorrowToken$"),
                            ast.full_perm(),
                        ),
                        pos.to_viper(context, ast),
                    )
                });
                let position =
                    ast.identifier_position(pos.line(), pos.column(), &pos.id().to_string());
                let apply = ast.apply(wand.to_viper(context, ast), position);
                ast.seqn(&[inhale, apply], &[])
            }
            Stmt::ExpireBorrows(_) => {
                // Skip
                ast.comment(&self.to_string())
            }
            Stmt::If(ref guard, ref then_stmts, ref else_stmts) => ast.if_stmt(
                guard.to_viper(context, ast),
                ast.seqn(&then_stmts.to_viper(context, ast), &[]),
                ast.seqn(&else_stmts.to_viper(context, ast), &[]),
            ),
            Stmt::Downcast(..) => {
                // Skip
                ast.comment(&self.to_string())
            }
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for PermAmount {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        match self {
            PermAmount::Write => ast.full_perm(),
            PermAmount::Read => ast.func_app("read$", &[], ast.perm_type(), ast.no_position()),
            PermAmount::Remaining => ast.perm_sub(
                PermAmount::Write.to_viper(context, ast),
                PermAmount::Read.to_viper(context, ast),
            ),
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for Expr {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        let expr = match self {
            Expr::Local(ref local_var, ref pos) => (local_var, pos).to_viper(context, ast),
            Expr::Variant(ref base, ref field, ref pos) => ast.field_access_with_pos(
                base.to_viper(context, ast),
                field.to_viper(context, ast),
                pos.to_viper(context, ast),
            ),
            Expr::Field(ref base, ref field, ref pos) => ast.field_access_with_pos(
                base.to_viper(context, ast),
                field.to_viper(context, ast),
                pos.to_viper(context, ast),
            ),
            Expr::AddrOf(..) => unreachable!(),
            Expr::Const(ref val, ref pos) => (val, pos).to_viper(context, ast),
            Expr::LabelledOld(ref old_label, ref expr, ref pos) => ast.labelled_old_with_pos(
                expr.to_viper(context, ast),
                old_label,
                pos.to_viper(context, ast),
            ),
            Expr::MagicWand(ref lhs, ref rhs, maybe_borrow, ref pos) => {
                let borrow_id = if let Some(borrow) = maybe_borrow {
                    borrow_id(*borrow) as isize
                } else {
                    -1
                };
                let borrow: Expr = borrow_id.into();
                let token = ast.predicate_access_predicate(
                    ast.predicate_access(&[borrow.to_viper(context, ast)], "DeadBorrowToken$"),
                    ast.full_perm(),
                );
                ast.magic_wand_with_pos(
                    ast.and_with_pos(
                        token,
                        lhs.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    rhs.to_viper(context, ast),
                    pos.to_viper(context, ast),
                )
            }
            Expr::PredicateAccessPredicate(ref predicate_name, ref arg, perm, ref pos) => ast
                .predicate_access_predicate_with_pos(
                    ast.predicate_access(&[arg.to_viper(context, ast)], predicate_name),
                    perm.to_viper(context, ast),
                    pos.to_viper(context, ast),
                ),
            Expr::FieldAccessPredicate(ref loc, perm, ref pos) => ast
                .field_access_predicate_with_pos(
                    loc.to_viper(context, ast),
                    perm.to_viper(context, ast),
                    pos.to_viper(context, ast),
                ),
            Expr::UnaryOp(op, ref expr, ref pos) => match expr.get_type() {
                Type::Float(float_ty) => {
                    let size = match float_ty {
                        Float::F32 => viper::FloatSizeViper::F32,
                        Float::F64 => viper::FloatSizeViper::F64,
                    };
                    let op_kind = match op {
                        UnaryOpKind::Minus => viper::UnOpFloat::Neg,
                        UnaryOpKind::IsNaN => viper::UnOpFloat::IsNan,
                        _ => unreachable!("illegal unary operation for floats: {}", op),
                    };
                    ast.float_unop(op_kind, size, expr.to_viper(context, ast))
                }
                Type::BitVector(bitvector_ty) => {
                    let bv_size = lower_bitvector_signed_size(*bitvector_ty);
                    let op_kind = match op {
                        UnaryOpKind::Not => viper::UnOpBv::Not,
                        UnaryOpKind::Minus => viper::UnOpBv::Neg,
                        _ => unreachable!("illegal unary operation for bitvectors: {}", op),
                    };
                    ast.bv_unnop(op_kind, bv_size, expr.to_viper(context, ast))
                }
                typ => match op {
                    UnaryOpKind::Not => {
                        ast.not_with_pos(expr.to_viper(context, ast), pos.to_viper(context, ast))
                    }
                    UnaryOpKind::Minus => {
                        ast.minus_with_pos(expr.to_viper(context, ast), pos.to_viper(context, ast))
                    }
                    _ => unreachable!("illegal unary operation {} for type {}", op, typ),
                },
            },
            Expr::BinOp(op, ref left, ref right, ref pos) => match left.get_maybe_type() {
                Some(Type::Float(float_ty)) => {
                    let size = match float_ty {
                        Float::F32 => viper::FloatSizeViper::F32,
                        Float::F64 => viper::FloatSizeViper::F64,
                    };
                    let float_op_kind = match op {
                        BinaryOpKind::Add => viper::BinOpFloat::Add,
                        BinaryOpKind::Sub => viper::BinOpFloat::Sub,
                        BinaryOpKind::Mul => viper::BinOpFloat::Mul,
                        BinaryOpKind::Div => viper::BinOpFloat::Div,
                        BinaryOpKind::EqCmp => viper::BinOpFloat::Eq,
                        BinaryOpKind::GtCmp => viper::BinOpFloat::Gt,
                        BinaryOpKind::GeCmp => viper::BinOpFloat::Geq,
                        BinaryOpKind::LtCmp => viper::BinOpFloat::Lt,
                        BinaryOpKind::LeCmp => viper::BinOpFloat::Leq,
                        BinaryOpKind::Min => viper::BinOpFloat::Min,
                        BinaryOpKind::Max => viper::BinOpFloat::Max,
                        _ => unreachable!("illegal binary operation for floats: {}", op),
                    };
                    ast.float_binop(
                        float_op_kind,
                        size,
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                    )
                }
                Some(Type::BitVector(bitvector_ty)) => {
                    let viper_size = lower_bitvector_signed_size(*bitvector_ty);
                    let (viper_left, viper_right) = match bitvector_ty {
                        BitVector::Signed(size) => (
                            unsigned_bv_to_signed_int(context, ast, *size, left, *pos),
                            unsigned_bv_to_signed_int(context, ast, *size, right, *pos),
                        ),
                        BitVector::Unsigned(_) => (
                            ast.backend_bv_to_int(viper_size, left.to_viper(context, ast)),
                            ast.backend_bv_to_int(viper_size, right.to_viper(context, ast)),
                        ),
                    };
                    match op {
                        BinaryOpKind::EqCmp => ast.eq_cmp_with_pos(
                            left.to_viper(context, ast),
                            right.to_viper(context, ast),
                            pos.to_viper(context, ast),
                        ),
                        BinaryOpKind::NeCmp => ast.ne_cmp_with_pos(
                            left.to_viper(context, ast),
                            right.to_viper(context, ast),
                            pos.to_viper(context, ast),
                        ),
                        BinaryOpKind::GtCmp => {
                            ast.gt_cmp_with_pos(viper_left, viper_right, pos.to_viper(context, ast))
                        }
                        BinaryOpKind::GeCmp => {
                            ast.ge_cmp_with_pos(viper_left, viper_right, pos.to_viper(context, ast))
                        }
                        BinaryOpKind::LtCmp => {
                            ast.lt_cmp_with_pos(viper_left, viper_right, pos.to_viper(context, ast))
                        }
                        BinaryOpKind::LeCmp => {
                            ast.le_cmp_with_pos(viper_left, viper_right, pos.to_viper(context, ast))
                        }
                        _ => {
                            let op_kind = match op {
                                BinaryOpKind::Add => viper::BinOpBv::BvAdd,
                                BinaryOpKind::Sub => viper::BinOpBv::BvSub,
                                BinaryOpKind::Mul => viper::BinOpBv::BvMul,
                                BinaryOpKind::Div => viper::BinOpBv::BvUDiv,
                                BinaryOpKind::BitAnd => viper::BinOpBv::BitAnd,
                                BinaryOpKind::BitOr => viper::BinOpBv::BitOr,
                                BinaryOpKind::BitXor => viper::BinOpBv::BitXor,
                                BinaryOpKind::Shl => viper::BinOpBv::BvShl,
                                BinaryOpKind::LShr => viper::BinOpBv::BvLShr,
                                BinaryOpKind::AShr => viper::BinOpBv::BvAShr,
                                _ => {
                                    unreachable!("illegal binary operation for bitvectors: {}", op)
                                }
                            };
                            ast.bv_binop(
                                op_kind,
                                viper_size,
                                left.to_viper(context, ast),
                                right.to_viper(context, ast),
                            )
                        }
                    }
                }
                typ => match op {
                    BinaryOpKind::EqCmp => ast.eq_cmp_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    BinaryOpKind::NeCmp => ast.ne_cmp_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    BinaryOpKind::GtCmp => ast.gt_cmp_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    BinaryOpKind::GeCmp => ast.ge_cmp_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    BinaryOpKind::LtCmp => ast.lt_cmp_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    BinaryOpKind::LeCmp => ast.le_cmp_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    BinaryOpKind::Add => ast.add_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    BinaryOpKind::Sub => ast.sub_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    BinaryOpKind::Mul => ast.mul_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    BinaryOpKind::Div => ast.div_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    BinaryOpKind::Mod => ast.module_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    BinaryOpKind::And => ast.and_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    BinaryOpKind::Or => ast.or_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    BinaryOpKind::Implies => ast.implies_with_pos(
                        left.to_viper(context, ast),
                        right.to_viper(context, ast),
                        pos.to_viper(context, ast),
                    ),
                    _ => unreachable!("illegal binary operation {} for type {:?}", op, typ),
                },
            },
            Expr::ContainerOp(op_kind, box ref left, box ref right, _pos) => match op_kind {
                ContainerOpKind::SeqIndex => {
                    ast.seq_index(left.to_viper(context, ast), right.to_viper(context, ast))
                }
                ContainerOpKind::SeqConcat => {
                    ast.seq_append(left.to_viper(context, ast), right.to_viper(context, ast))
                }
                ContainerOpKind::SeqLen => ast.seq_length(left.to_viper(context, ast)),
            },
            Expr::Seq(ty, elems, _pos) => {
                let elem_ty = force_matches!(ty, Type::Seq(box elem_ty) => elem_ty);
                let viper_elem_ty = elem_ty.to_viper(context, ast);
                if elems.is_empty() {
                    ast.empty_seq(viper_elem_ty)
                } else {
                    let viper_elems = elems
                        .iter()
                        .map(|e| e.to_viper(context, ast))
                        .collect::<Vec<_>>();
                    ast.explicit_seq(&viper_elems)
                }
            }
            Expr::Map(ty, elems, _pos) => {
                let (key_ty, val_ty) = force_matches!(ty, Type::Map(box k, box v) => (k, v));
                let viper_key_ty = key_ty.to_viper(context, ast);
                let viper_val_ty = val_ty.to_viper(context, ast);
                if elems.is_empty() {
                    ast.empty_map(viper_key_ty, viper_val_ty)
                } else {
                    let viper_elems = elems
                        .iter()
                        .map(|e| e.to_viper(context, ast))
                        .collect::<Vec<_>>();
                    ast.explicit_map(&viper_elems)
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
                    ast.predicate_access(&args.to_viper(context, ast)[..], predicate_name),
                    perm.to_viper(context, ast),
                ),
                expr.to_viper(context, ast),
                pos.to_viper(context, ast),
            ),
            Expr::Cond(ref guard, ref left, ref right, ref pos) => ast.cond_exp_with_pos(
                guard.to_viper(context, ast),
                left.to_viper(context, ast),
                right.to_viper(context, ast),
                pos.to_viper(context, ast),
            ),
            Expr::ForAll(ref vars, ref triggers, ref body, ref pos) => ast.forall_with_pos(
                &vars.to_viper_decl(context, ast)[..],
                &(triggers, pos).to_viper(context, ast),
                body.to_viper(context, ast),
                pos.to_viper(context, ast),
            ),
            Expr::Exists(ref vars, ref triggers, ref body, ref pos) => ast.exists_with_pos(
                &vars.to_viper_decl(context, ast)[..],
                &(triggers, pos).to_viper(context, ast),
                body.to_viper(context, ast),
                pos.to_viper(context, ast),
            ),
            Expr::LetExpr(ref var, ref expr, ref body, ref pos) => ast.let_expr_with_pos(
                var.to_viper_decl(context, ast),
                expr.to_viper(context, ast),
                body.to_viper(context, ast),
                pos.to_viper(context, ast),
            ),
            Expr::FuncApp(
                ref function_name,
                ref args,
                ref _formal_args,
                ref return_type,
                ref pos,
            ) => ast.func_app(
                function_name,
                &args.to_viper(context, ast),
                return_type.to_viper(context, ast),
                pos.to_viper(context, ast),
            ),
            Expr::DomainFuncApp(ref function, ref args, ref _pos) => {
                ast.domain_func_app(
                    function.to_viper(context, ast),
                    &args.to_viper(context, ast),
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
                    &args.to_viper(context, ast),
                    &[], // not necessary so far
                    return_type.to_viper(context, ast),
                    domain_name,
                    pos.to_viper(context, ast),
                )
            },
            */
            Expr::InhaleExhale(ref inhale_expr, ref exhale_expr, ref _pos) => ast
                .inhale_exhale_pred(
                    inhale_expr.to_viper(context, ast),
                    exhale_expr.to_viper(context, ast),
                ),
            Expr::Downcast(ref base, ..) => base.to_viper(context, ast),
            Expr::SnapApp(..) => unreachable!("unpatched snapshot operation"),
            // DEBUG: enable this version to see snap$(...) in the Viper output
            // for unpatched snapshot operations; this pushes the error to the
            // verifier, but at least allows inspecting the Viper program
            /*Expr::SnapApp(ref arg, ref pos) => {
                ast.func_app(
                    "snap$",
                    &[arg.to_viper(context, ast)],
                    self.get_type().to_viper(context, ast),
                    pos.to_viper(context, ast),
                )
            }*/
            Expr::Cast(kind, base, position) => match kind {
                CastKind::BVIntoInt(signed_size) => match signed_size {
                    BitVector::Signed(size) => {
                        unsigned_bv_to_signed_int(context, ast, *size, base, *position)
                    }
                    BitVector::Unsigned(size) => {
                        let size = lower_bitvector_size(*size);
                        ast.backend_bv_to_int(size, base.to_viper(context, ast))
                    }
                },
                CastKind::IntIntoBV(size) => {
                    let size = lower_bitvector_signed_size(*size);
                    ast.int_to_backend_bv(size, base.to_viper(context, ast))
                }
            },
        };
        if config::simplify_encoding() {
            ast.simplified_expression(expr)
        } else {
            expr
        }
    }
}

impl<'v, 'a, 'b> ToViper<'v, viper::Trigger<'v>> for (&'a Trigger, &'b Position) {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Trigger<'v> {
        ast.trigger_with_pos(
            &self.0.elements().to_viper(context, ast)[..],
            self.1.to_viper(context, ast),
        )
    }
}

impl<'v, 'a, 'b> ToViper<'v, viper::Expr<'v>> for (&'a Const, &'b Position) {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        match self.0 {
            Const::Bool(true) => ast.true_lit_with_pos(self.1.to_viper(context, ast)),
            Const::Bool(false) => ast.false_lit_with_pos(self.1.to_viper(context, ast)),
            Const::Int(x) => ast.int_lit_with_pos(*x, self.1.to_viper(context, ast)),
            Const::BigInt(ref x) => ast.int_lit_from_ref_with_pos(x, self.1.to_viper(context, ast)),
            Const::Float(FloatConst::F32(val)) => ast.backend_f32_lit(*val),
            Const::Float(FloatConst::F64(val)) => ast.backend_f64_lit(*val),
            Const::BitVector(bv_const) => match bv_const.typ {
                BitVector::Signed(BitVectorSize::BV8) | BitVector::Unsigned(BitVectorSize::BV8) => {
                    ast.backend_bv8_lit_str(&bv_const.value)
                }
                BitVector::Signed(BitVectorSize::BV16)
                | BitVector::Unsigned(BitVectorSize::BV16) => {
                    ast.backend_bv16_lit_str(&bv_const.value)
                }
                BitVector::Signed(BitVectorSize::BV32)
                | BitVector::Unsigned(BitVectorSize::BV32) => {
                    ast.backend_bv32_lit_str(&bv_const.value)
                }
                BitVector::Signed(BitVectorSize::BV64)
                | BitVector::Unsigned(BitVectorSize::BV64) => {
                    ast.backend_bv64_lit_str(&bv_const.value)
                }
                BitVector::Signed(BitVectorSize::BV128)
                | BitVector::Unsigned(BitVectorSize::BV128) => {
                    ast.backend_bv128_lit_str(&bv_const.value)
                }
            },
            Const::FnPtr => ast.null_lit_with_pos(self.1.to_viper(context, ast)),
        }
    }
}

impl<'v> ToViper<'v, viper::Predicate<'v>> for Predicate {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Predicate<'v> {
        match self {
            Predicate::Struct(p) => p.to_viper(context, ast),
            Predicate::Enum(p) => p.to_viper(context, ast),
            Predicate::Bodyless(name, this) => {
                ast.predicate(name, &[this.to_viper_decl(context, ast)], None)
            }
        }
    }
}

impl<'v> ToViper<'v, viper::Predicate<'v>> for StructPredicate {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Predicate<'v> {
        ast.predicate(
            &self.name,
            &[self.this.to_viper_decl(context, ast)],
            self.body.as_ref().map(|b| b.to_viper(context, ast)),
        )
    }
}

impl<'v> ToViper<'v, viper::Predicate<'v>> for EnumPredicate {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Predicate<'v> {
        ast.predicate(
            &self.name,
            &[self.this.to_viper_decl(context, ast)],
            Some(self.body().to_viper(context, ast)),
        )
    }
}

impl<'a, 'v> ToViper<'v, viper::Method<'v>> for &'a BodylessMethod {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Method<'v> {
        ast.method(
            &self.name,
            &self.formal_args.to_viper_decl(context, ast),
            &self.formal_returns.to_viper_decl(context, ast),
            &[],
            &[],
            None,
        )
    }
}

impl<'a, 'v> ToViper<'v, viper::Function<'v>> for &'a Function {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Function<'v> {
        ast.function(
            &self.get_identifier(),
            &self.formal_args.to_viper_decl(context, ast),
            self.return_type.to_viper(context, ast),
            &self.pres.to_viper(context, ast),
            &self.posts.to_viper(context, ast),
            ast.no_position(),
            self.body.as_ref().map(|b| b.to_viper(context, ast)),
        )
    }
}

impl<'a, 'v> ToViper<'v, viper::Domain<'v>> for &'a Domain {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Domain<'v> {
        ast.domain(
            &self.name,
            &self.functions.to_viper(context, ast),
            &self.axioms.to_viper(context, ast),
            &self.type_vars.to_viper(context, ast),
        )
    }
}

impl<'a, 'v> ToViper<'v, viper::DomainFunc<'v>> for &'a DomainFunc {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::DomainFunc<'v> {
        ast.domain_func(
            &self.get_identifier(),
            &self.formal_args.to_viper_decl(context, ast),
            self.return_type.to_viper(context, ast),
            self.unique,
            &self.domain_name,
        )
    }
}

impl<'a, 'v> ToViper<'v, viper::NamedDomainAxiom<'v>> for &'a DomainAxiom {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::NamedDomainAxiom<'v> {
        ast.named_domain_axiom(
            &self.name,
            self.expr.to_viper(context, ast),
            &self.domain_name,
        )
    }
}

// Vectors

impl<'v> ToViper<'v, Vec<viper::Field<'v>>> for Vec<Field> {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::Field<'v>> {
        self.iter().map(|x| x.to_viper(context, ast)).collect()
    }
}

impl<'v, 'a, 'b> ToViper<'v, Vec<viper::Expr<'v>>> for (&'a Vec<LocalVar>, &'b Position) {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::Expr<'v>> {
        self.0
            .iter()
            .map(|x| (x, self.1).to_viper(context, ast))
            .collect()
    }
}

impl<'v, 'a, 'b> ToViper<'v, Vec<viper::Trigger<'v>>> for (&'a Vec<Trigger>, &'b Position) {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::Trigger<'v>> {
        self.0
            .iter()
            .map(|x| (x, self.1).to_viper(context, ast))
            .collect()
    }
}

impl<'v> ToViperDecl<'v, Vec<viper::LocalVarDecl<'v>>> for Vec<LocalVar> {
    fn to_viper_decl(
        &self,
        context: Context,
        ast: &AstFactory<'v>,
    ) -> Vec<viper::LocalVarDecl<'v>> {
        self.iter().map(|x| x.to_viper_decl(context, ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::Domain<'v>>> for Vec<Domain> {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::Domain<'v>> {
        self.iter().map(|x| x.to_viper(context, ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::DomainFunc<'v>>> for Vec<DomainFunc> {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::DomainFunc<'v>> {
        self.iter().map(|x| x.to_viper(context, ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::NamedDomainAxiom<'v>>> for Vec<DomainAxiom> {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::NamedDomainAxiom<'v>> {
        self.iter().map(|x| x.to_viper(context, ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::Type<'v>>> for Vec<Type> {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::Type<'v>> {
        self.iter().map(|x| x.to_viper(context, ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::Expr<'v>>> for Vec<Expr> {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::Expr<'v>> {
        self.iter().map(|x| x.to_viper(context, ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::Stmt<'v>>> for Vec<Stmt> {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::Stmt<'v>> {
        self.iter().map(|x| x.to_viper(context, ast)).collect()
    }
}

impl<'v> ToViper<'v, Vec<viper::Predicate<'v>>> for Vec<Predicate> {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::Predicate<'v>> {
        self.iter().map(|x| x.to_viper(context, ast)).collect()
    }
}

impl<'a, 'v> ToViper<'v, viper::Method<'v>> for &'a CfgMethod {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Method<'v> {
        let mut blocks_ast: Vec<viper::Stmt> = vec![];
        let mut declarations: Vec<viper::Declaration> = vec![];

        for local_var in self.local_vars.iter() {
            declarations.push(local_var.to_viper_decl(context, ast).into());
        }
        for label in self.labels().iter() {
            let decl = ast.label(label, &[]);
            declarations.push(decl.into());
        }

        if config::enable_verify_only_basic_block_path() {
            let path = config::verify_only_basic_block_path();
            cfg_method_convert_basic_block_path(
                self,
                path,
                context,
                ast,
                &mut blocks_ast,
                &mut declarations,
            );
            // self.convert_basic_block_path(path, ast, &mut blocks_ast, &mut declarations);
        } else {
            // Sort blocks by label, except for the first block
            let mut blocks: Vec<_> = self.basic_blocks.iter().enumerate().skip(1).collect();
            blocks.sort_by_key(|(index, _)| index_to_label(self.basic_blocks_labels(), *index));
            blocks.insert(0, (0, &self.basic_blocks[0]));

            for (index, block) in blocks.into_iter() {
                blocks_ast.push(block_to_viper(
                    context,
                    ast,
                    self.basic_blocks_labels(),
                    block,
                    index,
                ));
                declarations.push(
                    ast.label(&index_to_label(self.basic_blocks_labels(), index), &[])
                        .into(),
                );
            }
        }
        blocks_ast.push(ast.label(RETURN_LABEL, &[]));
        declarations.push(ast.label(RETURN_LABEL, &[]).into());

        let method_body = Some(ast.seqn(&blocks_ast, &declarations));

        let mut formal_returns_decl: Vec<viper::LocalVarDecl> = vec![];
        for local_var in self.get_formal_returns() {
            formal_returns_decl.push(local_var.to_viper_decl(context, ast));
        }

        ast.method(
            &self.name(),
            &[],
            &formal_returns_decl,
            &[],
            &[],
            method_body,
        )
    }
}

fn cfg_method_convert_basic_block_path<'v>(
    cfg_method: &CfgMethod,
    mut path: Vec<String>,
    context: Context,
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
                index_to_label(cfg_method.basic_blocks_labels(), index),
                (index, block),
            )
        })
        .collect();
    let mut current_label = index_to_label(cfg_method.basic_blocks_labels(), 0);
    while let Some((index, block)) = remaining_blocks.remove(&current_label) {
        blocks_ast.push(block_to_viper(
            context,
            ast,
            cfg_method.basic_blocks_labels(),
            block,
            index,
        ));
        declarations.push(
            ast.label(
                &index_to_label(cfg_method.basic_blocks_labels(), index),
                &[],
            )
            .into(),
        );

        let mut successors: Vec<_> = block
            .successor
            .get_following()
            .into_iter()
            .map(|ci| index_to_label(cfg_method.basic_blocks_labels(), ci.index()))
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
                ast.false_lit_with_pos(fake_position.to_viper(context, ast)),
                fake_position.to_viper(context, ast),
            ),
            successor_to_viper(
                context,
                ast,
                index,
                cfg_method.basic_blocks_labels(),
                &block.successor,
            ),
        ];
        blocks_ast.push(ast.seqn(&stmts, &[]));
        declarations.push(ast.label(&label, &[]).into());
    }

    for (label, (index, block)) in remaining_blocks {
        blocks_ast.push(block_to_viper(
            context,
            ast,
            cfg_method.basic_blocks_labels(),
            block,
            index,
        ));
        declarations.push(ast.label(&label, &[]).into());
    }
}

impl<'v> ToViper<'v, Vec<viper::Method<'v>>> for Vec<CfgMethod> {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::Method<'v>> {
        self.iter().map(|x| x.to_viper(context, ast)).collect()
    }
}

fn index_to_label(basic_block_labels: &[String], index: usize) -> String {
    basic_block_labels[index].clone()
}

fn successor_to_viper<'a>(
    context: Context,
    ast: &'a AstFactory,
    index: usize,
    basic_block_labels: &[String],
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
                let goto = ast.seqn(&[ast.goto(&basic_block_labels[target.index()])], &[]);
                let skip = ast.seqn(&[], &[]);
                let conditional_goto = ast.if_stmt(test.to_viper(context, ast), goto, skip);
                stmts.push(conditional_goto);
            }
            let default_goto = ast.goto(&basic_block_labels[default_target.index()]);
            stmts.push(default_goto);
            ast.seqn(&stmts, &[])
        }
    }
}

fn block_to_viper<'a>(
    context: Context,
    ast: &'a AstFactory,
    basic_block_labels: &[String],
    block: &CfgBlock,
    index: usize,
) -> viper::Stmt<'a> {
    let label = &basic_block_labels[index];
    let mut stmts: Vec<viper::Stmt> = vec![ast.label(label, &[])];
    stmts.extend(block.stmts.to_viper(context, ast));
    stmts.push(successor_to_viper(
        context,
        ast,
        index,
        basic_block_labels,
        &block.successor,
    ));
    ast.seqn(&stmts, &[])
}

fn lower_bitvector_size(size: BitVectorSize) -> viper::BvSize {
    match size {
        BitVectorSize::BV8 => viper::BvSize::BV8,
        BitVectorSize::BV16 => viper::BvSize::BV16,
        BitVectorSize::BV32 => viper::BvSize::BV32,
        BitVectorSize::BV64 => viper::BvSize::BV64,
        BitVectorSize::BV128 => viper::BvSize::BV128,
    }
}

fn lower_bitvector_signed_size(size: BitVector) -> viper::BvSize {
    match size {
        BitVector::Signed(size) | BitVector::Unsigned(size) => lower_bitvector_size(size),
    }
}

fn signed_max_for_size(size: BitVectorSize) -> u128 {
    match size {
        BitVectorSize::BV8 => i8::MAX as u128,
        BitVectorSize::BV16 => i16::MAX as u128,
        BitVectorSize::BV32 => i32::MAX as u128,
        BitVectorSize::BV64 => i64::MAX as u128,
        BitVectorSize::BV128 => i128::MAX as u128,
    }
}

fn unsigned_max_for_size(size: BitVectorSize) -> u128 {
    match size {
        BitVectorSize::BV8 => u8::MAX as u128,
        BitVectorSize::BV16 => u16::MAX as u128,
        BitVectorSize::BV32 => u32::MAX as u128,
        BitVectorSize::BV64 => u64::MAX as u128,
        BitVectorSize::BV128 => u128::MAX as u128,
    }
}

fn unsigned_bv_to_signed_int<'v>(
    context: Context,
    ast: &AstFactory<'v>,
    size: BitVectorSize,
    value: &Expr,
    pos: Position,
) -> viper::Expr<'v> {
    let viper_size = lower_bitvector_size(size);
    let signed_max_int: Expr = signed_max_for_size(size).into();
    let unsigned_max_int: Expr = unsigned_max_for_size(size).into();
    let value = ast.backend_bv_to_int(viper_size, value.to_viper(context, ast));
    let one: Expr = 1u32.into();
    ast.cond_exp_with_pos(
        ast.lt_cmp_with_pos(
            signed_max_int.to_viper(context, ast),
            value,
            pos.to_viper(context, ast),
        ),
        ast.sub_with_pos(
            ast.sub_with_pos(
                value,
                unsigned_max_int.to_viper(context, ast),
                pos.to_viper(context, ast),
            ),
            one.to_viper(context, ast),
            pos.to_viper(context, ast),
        ),
        value,
        pos.to_viper(context, ast),
    )
}
