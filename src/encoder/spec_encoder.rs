// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::borrows::ProcedureContract;
use encoder::builtin_encoder::BuiltinMethodKind;
use encoder::Encoder;
use encoder::error_manager::ErrorCtxt;
use encoder::error_manager::PanicCause;
use encoder::foldunfold;
use encoder::loop_encoder::LoopEncoder;
use encoder::places::{Local, LocalVariableManager, Place};
use encoder::vir::{self, CfgBlockIndex, Successor};
use encoder::vir::utils::ExprIterator;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::BasicBlockIndex;
use prusti_interface::environment::Environment;
use prusti_interface::environment::Procedure;
use prusti_interface::environment::ProcedureImpl;
use report::Log;
use rustc::middle::const_val::ConstVal;
use rustc::mir;
use rustc::hir;
use rustc::mir::TerminatorKind;
use rustc::ty;
use rustc_data_structures::indexed_vec::Idx;
use std::collections::HashMap;
use std::collections::HashSet;
use syntax::codemap::Span;
use syntax::ast;
use prusti_interface::specifications::*;

pub struct SpecEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> SpecEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, mir: &'p mir::Mir<'tcx>) -> Self {
        debug!("SpecEncoder constructor");

        SpecEncoder {
            encoder,
            mir,
        }
    }

    fn encode_hir_arg(&self, arg: &hir::Arg) -> vir::LocalVar {
        trace!("encode_hir_arg: {:?}", arg);
        let var_name = match arg.pat.node {
            hir::PatKind::Lit(ref expr) => {
                hir::print::to_string(hir::print::NO_ANN, |s| s.print_expr(expr))
            }
            ref x => unimplemented!("{:?}", x)
        };
        let arg_ty = self.encoder.env().hir_id_to_type(arg.hir_id);
        let type_name = self.encoder.encode_type_predicate_use(arg_ty);
        vir::LocalVar::new(var_name, vir::Type::TypedRef(type_name))
    }

    fn encode_hir_variable(&self, var_path: &hir::Path) -> vir::LocalVar {
        trace!("encode_hir_path: {:?}", var_path);
        let original_var_name = hir::print::to_string(hir::print::NO_ANN, |s| s.print_path(var_path, false));

        // Special variable names
        let var_name = if original_var_name == "result" {
            "_0".to_string()
        } else if false {
            // TODO: check if the variable is an old expression
            unimplemented!("TODO")
        } else {
            // It must be an argument
            let local = self.mir.local_decls
                .iter_enumerated()
                .find(|(local, local_decl)| match local_decl.name {
                    None => false,
                    Some(name) => &format!("{:?}", name) == &original_var_name
                })
                .map(|(local, _)| local)
                .unwrap();
            format!("{:?}", local)
        };

        let hir_id = match var_path.def {
            hir::def::Def::Local(node_id) => self.encoder.env().tcx().hir.node_to_hir_id(node_id),
            ref x => unimplemented!("{:?}", x)
        };
        let var_ty = self.encoder.env().hir_id_to_type(hir_id);
        let type_name = self.encoder.encode_type_predicate_use(&var_ty);
        vir::LocalVar::new(var_name, vir::Type::TypedRef(type_name))
    }

    fn encode_hir_path(&self, base_expr: &hir::Expr) -> vir::Place {
        trace!("encode_hir_path: {:?}", base_expr);
        let base_ty = self.encoder.env().hir_id_to_type(base_expr.hir_id);
        match base_expr.node {
            hir::Expr_::ExprField(ref expr, field_id) => {
                let place = self.encode_hir_path(expr);
                assert!(place.get_type().is_ref());
                // TODO: get the invariant
                unimplemented!("TODO")
            }

            hir::Expr_::ExprUnary(hir::UnOp::UnDeref, ref expr) => {
                let place = self.encode_hir_path(expr);
                assert!(place.get_type().is_ref());
                let type_name: String = self.encoder.encode_type_predicate_use(base_ty);
                place.access(vir::Field::new("val_ref", vir::Type::TypedRef(type_name))).into()
            }

            hir::Expr_::ExprUnary(..) |
            hir::Expr_::ExprLit(..) |
            hir::Expr_::ExprBinary(..) |
            hir::Expr_::ExprIf(..) |
            hir::Expr_::ExprMatch(..) => unreachable!("A path is expected, but found {:?}", base_expr),

            hir::Expr_::ExprPath(hir::QPath::Resolved(_, ref var_path)) => {
                vir::Place::Base(self.encode_hir_variable(var_path))
            }

            ref x => unimplemented!("{:?}", x),
        }
    }

    fn encode_hir_path_expr(&self, base_expr: &hir::Expr) -> vir::Expr {
        trace!("encode_hir_path_expr: {:?}", base_expr);
        let place = self.encode_hir_path(base_expr);
        let base_ty = self.encoder.env().hir_id_to_type(base_expr.hir_id);
        assert!(place.get_type().is_ref());
        match base_ty.sty {
            ty::TypeVariants::TyBool => place.access(vir::Field::new("val_bool", vir::Type::Bool)).into(),

            ty::TypeVariants::TyInt(_) |
            ty::TypeVariants::TyUint(_) => place.access(vir::Field::new("val_int", vir::Type::Int)).into(),

            ref x => unimplemented!("{:?}", x)
        }
    }

    fn encode_literal_expr(&self, lit: &ast::Lit) -> vir::Expr {
        trace!("encode_literal_expr: {:?}", lit);
        match lit.node {
            ast::LitKind::Int(int_val, ast::LitIntType::Signed(_)) => (int_val as i128).into(),
            ast::LitKind::Int(int_val, ast::LitIntType::Unsigned(_)) |
            ast::LitKind::Int(int_val, ast::LitIntType::Unsuffixed) => int_val.into(),
            ast::LitKind::Bool(bool_val) => bool_val.into(),
            ref x => unimplemented ! ("{:?}", x),
        }
    }

    fn encode_hir_expr(&self, base_expr: &hir::Expr) -> vir::Expr {
        trace!("encode_hir_expr: {:?}", base_expr);
        match base_expr.node {
            hir::Expr_::ExprLit(ref lit) => self.encode_literal_expr(lit),

            hir::Expr_::ExprBinary(op, ref left, ref right) => {
                let left_expr = self.encode_hir_expr(left);
                let right_expr = self.encode_hir_expr(right);
                let is_bool = match left_expr {
                    vir::Expr::Place(ref p) => p.get_type() == &vir::Type::Bool,
                    _ => false
                };
                match op.node {
                    hir::BinOp_::BiAdd => vir::Expr::add(left_expr, right_expr),
                    hir::BinOp_::BiSub => vir::Expr::sub(left_expr, right_expr),
                    hir::BinOp_::BiMul => vir::Expr::mul(left_expr, right_expr),
                    hir::BinOp_::BiDiv => vir::Expr::div(left_expr, right_expr),
                    hir::BinOp_::BiRem => vir::Expr::rem(left_expr, right_expr),
                    hir::BinOp_::BiAnd => vir::Expr::and(left_expr, right_expr),
                    hir::BinOp_::BiOr => vir::Expr::or(left_expr, right_expr),
                    hir::BinOp_::BiBitXor if is_bool => vir::Expr::xor(left_expr, right_expr),
                    hir::BinOp_::BiBitAnd if is_bool => vir::Expr::and(left_expr, right_expr),
                    hir::BinOp_::BiBitOr if is_bool => vir::Expr::or(left_expr, right_expr),
                    hir::BinOp_::BiEq => vir::Expr::eq_cmp(left_expr, right_expr),
                    hir::BinOp_::BiLt => vir::Expr::lt_cmp(left_expr, right_expr),
                    hir::BinOp_::BiLe => vir::Expr::le_cmp(left_expr, right_expr),
                    hir::BinOp_::BiNe => vir::Expr::ne_cmp(left_expr, right_expr),
                    hir::BinOp_::BiGt => vir::Expr::gt_cmp(left_expr, right_expr),
                    hir::BinOp_::BiGe => vir::Expr::ge_cmp(left_expr, right_expr),
                    ref x => unimplemented!("{:?}", x),
                }
            }

            hir::Expr_::ExprUnary(hir::UnOp::UnDeref, ..) |
            hir::Expr_::ExprField(..) |
            hir::Expr_::ExprPath(hir::QPath::Resolved(..)) => {
                let encoded_expr = self.encode_hir_path_expr(base_expr);
                encoded_expr
            }

            hir::Expr_::ExprUnary(hir::UnOp::UnNot, ref expr) => {
                let encoded_expr = self.encode_hir_expr(expr);
                let is_bool = match encoded_expr {
                    vir::Expr::Place(ref p) => p.get_type() == &vir::Type::Bool,
                    _ => false
                };
                assert!(is_bool);
                vir::Expr::not(encoded_expr)
            }

            hir::Expr_::ExprUnary(hir::UnOp::UnNeg, ref expr) => {
                let encoded_expr = self.encode_hir_expr(expr);
                let is_int = match encoded_expr {
                    vir::Expr::Place(ref p) => p.get_type() == &vir::Type::Int,
                    vir::Expr::Const(ref const_val) => const_val.is_num(),
                    _ => false
                };
                assert!(is_int, "{:?} is not int", encoded_expr);
                vir::Expr::minus(encoded_expr)
            }

            hir::Expr_::ExprIf(ref guard_expr, ref then_expr, Some(ref else_expr)) => {
                let encoded_guard = self.encode_hir_expr(guard_expr);
                let encoded_then = self.encode_hir_expr(then_expr);
                let encoded_else = self.encode_hir_expr(else_expr);
                vir::Expr::ite(encoded_guard, encoded_then, encoded_else)
            }

            hir::Expr_::ExprMatch(ref expr, ref arms, _) => {
                assert!(arms.iter().all(|arm| arm.guard.is_none()));
                assert!(arms.iter().all(
                    |arm| arm.pats.iter().all(
                        |pat| match pat.node {
                            hir::PatKind::Wild |
                            hir::PatKind::Lit(_) => true,
                            hir::PatKind::Struct(_, ref args, _) => args.is_empty(),
                            hir::PatKind::TupleStruct(_, ref args, _) => args.is_empty(),
                            hir::PatKind::Tuple(ref args, _) => args.is_empty(),
                            _ => false
                        }
                    )
                ));

                self.encode_match_arms(expr, &arms[..])
            },

            hir::Expr_::ExprBlock(ref block, _) => {
                assert!(block.stmts.is_empty());
                assert!(block.expr.is_some());
                self.encode_hir_expr(block.expr.as_ref().unwrap())
            }

            ref x => unimplemented!("{:?}", x),
        }
    }

    fn encode_match_arms(&self, expr: &hir::Expr, arms: &[hir::Arm]) -> vir::Expr {
        assert!(!arms.is_empty());
        let first_arm = &arms[0];
        let encoded_body = self.encode_hir_expr(&first_arm.body);

        if arms.len() == 1 {
            encoded_body
        } else {
            let mut encoded_pats: Vec<vir::Expr> = vec![];
            for pat in &first_arm.pats {
                let encoded_pat: vir::Expr = match pat.node {
                    hir::PatKind::Wild => true.into(),

                    hir::PatKind::Lit(ref expr) => self.encode_hir_expr(expr),

                    hir::PatKind::Struct(ref qpath, _, _) => unimplemented!("TODO"),
                    hir::PatKind::TupleStruct(ref qpath, _, _) => unimplemented!("TODO"),
                    hir::PatKind::Tuple(_, _) => unimplemented!("TODO"),

                    ref x => unimplemented!("{:?}", x),
                };
                encoded_pats.push(encoded_pat);
            }

            vir::Expr::ite(
                encoded_pats.into_iter().disjoin(),
                encoded_body,
                self.encode_match_arms(expr, &arms[1..])
            )
        }
    }

    fn encode_trigger(&self, trigger: &TypedTrigger) -> vir::Trigger {
        warn!("TODO: incomplete encoding of trigger: {:?}", trigger);
        vir::Trigger::new(vec![])
    }

    /// Encode a specification item as a single expression.
    pub fn encode_assertion(&self, assertion: &TypedAssertion) -> vir::Expr {
        warn!("TODO: incomplete encoding of functional specification: {:?}", assertion);
        match assertion.kind {
            box AssertionKind::Expr(ref hir_expr) => {
                self.encode_hir_expr(&hir_expr.expr)
            }
            box AssertionKind::And(ref assertions) => {
                assertions.iter()
                    .map(|x| self.encode_assertion(x))
                    .collect::<Vec<vir::Expr>>()
                    .into_iter()
                    .conjoin()
            }
            box AssertionKind::Implies(ref lhs, ref rhs) => {
                vir::Expr::implies(
                    self.encode_hir_expr(&lhs.expr),
                    self.encode_assertion(rhs)
                )
            }
            box AssertionKind::ForAll(ref vars, ref trigger_set, ref filter, ref body) => {
                vir::Expr::forall(
                    vars.vars.iter().map(|x| self.encode_hir_arg(x)).collect(),
                    trigger_set.triggers().iter().map(|x| self.encode_trigger(x)).collect(),
                    vir::Expr::implies(
                        self.encode_hir_expr(&filter.expr),
                        self.encode_hir_expr(&body.expr)
                    )
                )
            }
        }
    }
}
