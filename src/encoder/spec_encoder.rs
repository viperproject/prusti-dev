// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::borrows::ProcedureContract;
use encoder::builtin_encoder::BuiltinMethodKind;
use encoder::mir_encoder::PRECONDITION_LABEL;
use encoder::Encoder;
use encoder::error_manager::ErrorCtxt;
use encoder::error_manager::PanicCause;
use encoder::foldunfold;
use encoder::loop_encoder::LoopEncoder;
use encoder::vir::{self, CfgBlockIndex, Successor};
use encoder::vir::ExprIterator;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::BasicBlockIndex;
use prusti_interface::environment::Environment;
use prusti_interface::environment::Procedure;
use prusti_interface::environment::ProcedureImpl;
use prusti_interface::report::Log;
use rustc::middle::const_val::ConstVal;
use rustc::mir;
use rustc::hir;
use rustc::mir::TerminatorKind;
use rustc::ty;
use rustc_data_structures::indexed_vec::Idx;
use std::collections::HashMap;
use std::collections::HashSet;
use syntax::codemap::Span;
use syntax_pos::symbol::Ident;
use syntax::ast;
use prusti_interface::specifications::*;
use encoder::mir_encoder::MirEncoder;

pub struct SpecEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> SpecEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, mir: &'p mir::Mir<'tcx>) -> Self {
        trace!("SpecEncoder constructor");

        SpecEncoder {
            encoder,
            mir,
        }
    }

    fn encode_hir_field(&self, field_expr: &hir::Expr) -> vir::Field {
        trace!("encode_hir_field: {:?}", field_expr);
        assert!(match field_expr.node { hir::Expr_::ExprField(..) => true, _ => false });

        let (base_expr, field_id) = if let hir::Expr_::ExprField(ref base_expr, field_id) = field_expr.node {
            (base_expr, field_id)
        } else {
            unreachable!()
        };

        let tcx = self.encoder.env().tcx();
        let owner_def_id = field_expr.hir_id.owner_def_id();
        let typeck_tables = tcx.typeck_tables_of(owner_def_id);
        let field_index = tcx.field_index(field_expr.id, typeck_tables);
        let base_expr_ty = typeck_tables.expr_ty(base_expr);

        let field_name = match base_expr_ty.ty_adt_def() {
            Some(adt) => {
                match tcx.hir.describe_def(base_expr.id) {
                    Some(def) => {
                        let variant_def = tcx.expect_variant_def(def);
                        let def_id = tcx.adt_def_id_of_variant(variant_def);
                        let variant_index = adt.variant_index_with_id(def_id);
                        // TODO: do we want the variant_index or the discriminant?
                        format!("enum_{}_{:?}", variant_index, field_id.name)
                    }
                    None => {
                        format!("enum_0_{:?}", field_id.name)
                    }
                }
            }
            None => {
                format!("tuple_{}", field_index)
            }
        };

        let field_ty = typeck_tables.expr_ty(field_expr);
        let encoded_type = self.encoder.encode_type(field_ty);
        vir::Field::new(field_name, encoded_type)
    }

    fn encode_hir_arg(&self, arg: &hir::Arg) -> vir::LocalVar {
        trace!("encode_hir_arg: {:?}", arg);
        let var_name = match arg.pat.node {
            hir::PatKind::Lit(ref expr) => {
                hir::print::to_string(hir::print::NO_ANN, |s| s.print_expr(expr))
            }
            hir::PatKind::Binding(_, _, ident, ..) => {
                ident.node.to_string()
            }
            ref x => unimplemented!("{:?}", x)
        };
        debug!("encode_hir_arg var_name: {:?}", var_name);
        let arg_ty = self.encoder.env().hir_id_to_type(arg.hir_id);

        assert!(match arg_ty.sty {
            ty::TypeVariants::TyInt(..) |
            ty::TypeVariants::TyUint(..) => true,
            _ => false
        }, "Quantification is only supported over integer values");

        vir::LocalVar::new(var_name, vir::Type::Int)
    }

    fn path_to_string(&self, var_path: &hir::Path) -> String {
        hir::print::to_string(hir::print::NO_ANN, |s| s.print_path(var_path, false))
    }

    fn encode_hir_variable(&self, var_path: &hir::Path) -> vir::LocalVar {
        trace!("encode_hir_variable: {:?}", var_path);
        let original_var_name = self.path_to_string(var_path);
        let mut is_quantified_var;

        // Special variable names
        let var_name = if original_var_name == "result" {
            is_quantified_var = false;
            "_0".to_string()
        } else {
            // Is it an argument?
            let opt_local = self.mir.local_decls
                .iter_enumerated()
                .find(|(local, local_decl)| match local_decl.name {
                    None => false,
                    Some(name) => &format!("{:?}", name) == &original_var_name
                })
                .map(|(local, _)| local);

            // TODO: give precedence to the variables declared in quantifiers
            match opt_local {
                // If it's an argument, use the MIR name (_1, _2, ...)
                Some(local) => {
                    is_quantified_var = false;
                    format!("{:?}", local)
                }

                // If it is not an argument, keep the original name
                None => {
                    is_quantified_var = true;
                    original_var_name
                }
            }
        };

        let hir_id = match var_path.def {
            hir::def::Def::Local(node_id) |
            hir::def::Def::Upvar(node_id, _, _) => self.encoder.env().tcx().hir.node_to_hir_id(node_id),
            ref x => unimplemented!("{:?}", x)
        };
        let var_ty = self.encoder.env().hir_id_to_type(hir_id);

        let encoded_type = if is_quantified_var {
            assert!(match var_ty.sty {
                ty::TypeVariants::TyInt(..) |
                ty::TypeVariants::TyUint(..) => true,
                _ => false
            }, "Quantification is only supported over integer values");
            vir::Type::Int
        } else {
            let type_name = self.encoder.encode_type_predicate_use(&var_ty);
            vir::Type::TypedRef(type_name)
        };

        vir::LocalVar::new(var_name, encoded_type)
    }

    fn encode_hir_path(&self, base_expr: &hir::Expr) -> vir::Place {
        trace!("encode_hir_path: {:?}", base_expr.node);
        let base_ty = self.encoder.env().hir_id_to_type(base_expr.hir_id);
        match base_expr.node {
            hir::Expr_::ExprField(ref expr, field_id) => {
                let place = self.encode_hir_path(expr);
                assert!(place.get_type().is_ref());
                let field = self.encode_hir_field(base_expr);
                place.access(field)
            }

            hir::Expr_::ExprUnary(hir::UnOp::UnDeref, ref expr) => {
                let place = self.encode_hir_path(expr);
                assert!(place.get_type().is_ref());
                match place {
                    vir::Place::AddrOf(box base, typ) => base,
                    _ => {
                        let type_name: String = self.encoder.encode_type_predicate_use(base_ty);
                        place.access(vir::Field::new("val_ref", vir::Type::TypedRef(type_name))).into()
                    }
                }
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
        trace!("encode_hir_path_expr: {:?}", base_expr.node);
        let place = self.encode_hir_path(base_expr);
        let base_ty = self.encoder.env().hir_id_to_type(base_expr.hir_id);

        if place.get_type().is_ref() {
            match base_ty.sty {
                ty::TypeVariants::TyBool => place.access(vir::Field::new("val_bool", vir::Type::Bool)).into(),

                ty::TypeVariants::TyInt(..) |
                ty::TypeVariants::TyUint(..) => place.access(vir::Field::new("val_int", vir::Type::Int)).into(),

                ty::TypeVariants::TyTuple(..) |
                ty::TypeVariants::TyAdt(..) => place.into(),

                ref x => unimplemented!("{:?}", x)
            }
        } else {
            place.into()
        }
    }

    fn encode_literal_expr(&self, lit: &ast::Lit) -> vir::Expr {
        trace!("encode_literal_expr: {:?}", lit.node);
        match lit.node {
            ast::LitKind::Int(int_val, ast::LitIntType::Signed(_)) => (int_val as i128).into(),
            ast::LitKind::Int(int_val, ast::LitIntType::Unsigned(_)) |
            ast::LitKind::Int(int_val, ast::LitIntType::Unsuffixed) => int_val.into(),
            ast::LitKind::Bool(bool_val) => bool_val.into(),
            ref x => unimplemented ! ("{:?}", x),
        }
    }

    fn encode_hir_expr(&self, base_expr: &hir::Expr) -> vir::Expr {
        trace!("encode_hir_expr: {:?}", base_expr.node);
        match base_expr.node {
            hir::Expr_::ExprLit(ref lit) => self.encode_literal_expr(lit),

            hir::Expr_::ExprUnary(hir::UnOp::UnDeref, ..) |
            hir::Expr_::ExprField(..) => {
                let encoded_expr = self.encode_hir_path_expr(base_expr);
                encoded_expr
            }

            hir::Expr_::ExprPath(hir::QPath::Resolved(..)) => {
                let encoded_expr = self.encode_hir_path_expr(base_expr);
                encoded_expr
            }

            hir::Expr_::ExprCall(ref callee, ref arguments) => {
                match callee.node {
                    hir::Expr_::ExprPath(hir::QPath::Resolved(_, ref fn_path)) => {
                        let fn_name = self.path_to_string(fn_path);
                        if fn_name == "old" {
                            assert!(arguments.len() == 1);
                            vir::Expr::labelled_old(
                                PRECONDITION_LABEL,
                                self.encode_hir_expr(&arguments[0]),
                            )
                        } else {
                            unimplemented!("TODO: call function {:?} from specification", fn_name)
                        }
                    }

                    ref x => unimplemented!("{:?}", x),
                }
            }

            ref x => unimplemented!("{:?}", x),
        }
    }

    fn encode_trigger(&self, trigger: &TypedTrigger) -> vir::Trigger {
        trace!("encode_trigger {:?}", trigger);
        // TODO: `encode_hir_expr` generated also the final `.val_int` field access, that we may not want...
        vir::Trigger::new(
            trigger.terms().iter().map(|expr| self.encode_hir_expr(&expr.expr)).collect()
        )
    }

    /// Encode a specification item as a single expression.
    pub fn encode_assertion(&self, assertion: &TypedAssertion) -> vir::Expr {
        trace!("encode_assertion {:?}", assertion);
        match assertion.kind {
            box AssertionKind::Expr(ref assertion_expr) => {
                self.encode_expression(assertion_expr)
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
                    self.encode_expression(lhs),
                    self.encode_assertion(rhs)
                )
            }
            box AssertionKind::ForAll(ref vars, ref trigger_set, ref body) => {
                vir::Expr::forall(
                    vars.vars.iter().map(|x| self.encode_hir_arg(x)).collect(),
                    trigger_set.triggers().iter().map(|x| self.encode_trigger(x)).collect(),
                    self.encode_assertion(body)
                )
            }
        }
    }

    fn encode_expression(&self, assertion_expr: &TypedExpression) -> vir::Expr {
        debug!("encode_expression {:?}", assertion_expr);
        let tcx = self.encoder.env().tcx();

        // Find the MIR of the assertion
        let mut curr_node_id = assertion_expr.expr.id;
        for i in 0..1 {
            curr_node_id = tcx.hir.get_parent_node(curr_node_id);
        }
        let closure_node_id = curr_node_id;
        let mir_def_id = tcx.hir.local_def_id(closure_node_id);
        let mut mir_expr = self.encoder.encode_pure_function_body(mir_def_id);

        // Fix the return variable
        let spec_method_node_id = tcx.hir.get_parent(closure_node_id);
        let spec_method_def_id = tcx.hir.local_def_id(spec_method_node_id);
        let spec_method_mir = tcx.mir_validated(spec_method_def_id).borrow();
        let spec_method_mir_encoder = MirEncoder::new(self.encoder, &spec_method_mir);
        let fake_return_var = spec_method_mir_encoder.encode_local(
            spec_method_mir.args_iter().last().unwrap()
        );
        let proper_return_var = vir::LocalVar::new(
            "_0".to_string(),
            fake_return_var.typ.clone()
        );
        mir_expr = vir::utils::ExprSubPlaceSubstitutor::substitute(
            mir_expr,
            &fake_return_var.into(),
            proper_return_var.into()
        );

        // TODO: replace with quantified variables...

        debug!("MIR expr {:?} --> {}", assertion_expr.id, mir_expr);
        mir_expr
    }
}
