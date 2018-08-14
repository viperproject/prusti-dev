// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::Encoder;
use encoder::mir_interpreter::{BackwardMirInterpreter, run_backward_interpretation};
use encoder::mir_encoder::MirEncoder;
use encoder::builtin_encoder::BuiltinFunctionKind;
use encoder::procedure_encoder::PRECONDITION_LABEL;
use encoder::vir;
use rustc::mir;
use rustc::ty;
use rustc::hir::def_id::DefId;
use std::collections::HashMap;
use prusti_interface::environment::Environment;
use syntax::ast;

pub struct PureFunctionEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    proc_def_id: DefId,
    mir: &'p mir::Mir<'tcx>,
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> PureFunctionEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, proc_def_id: DefId, mir: &'p mir::Mir<'tcx>) -> Self {
        trace!("PureFunctionEncoder constructor: {:?}", proc_def_id);
        PureFunctionEncoder {
            encoder,
            proc_def_id,
            mir
        }
    }

    pub fn encode_body(&self) -> vir::Expr {
        let procedure_name = self.encoder.env().get_item_name(self.proc_def_id);
        debug!("Encode body of pure function {}", procedure_name);

        let interpreter = PureFunctionInterpreter::new(self.encoder, self.mir);
        let state = run_backward_interpretation(self.mir, &interpreter)
            .expect(&format!("Procedure {:?} contains a loop", self.proc_def_id));
        let body_expr = state.into_expression();
        debug!("Pure function {} has been encoded with expr: {}", procedure_name, body_expr);
        body_expr
    }

    pub fn encode_function(&self) -> vir::Function {
        let procedure_name = self.encoder.env().get_item_name(self.proc_def_id);
        debug!("Encode pure function {}", procedure_name);

        let interpreter = PureFunctionInterpreter::new(self.encoder, self.mir);
        let state = run_backward_interpretation(self.mir, &interpreter)
            .expect(&format!("Procedure {:?} contains a loop", self.proc_def_id));
        let body_expr = state.into_expression();
        debug!("Pure function {} has been encoded with expr: {}", procedure_name, body_expr);

        let formal_args: Vec<_> = self.mir.args_iter().map(
            |local| interpreter.mir_encoder().encode_local(local)
        ).collect();
        let return_type = self.encoder.encode_value_type(self.mir.return_ty());

        vir::Function {
            name: procedure_name,
            formal_args,
            return_type,
            body: Some(body_expr)
        }
    }
}

#[derive(Clone, Debug)]
struct PureFunctionState {
    expr: vir::Expr
}

impl PureFunctionState {
    fn new(expr: vir::Expr) -> Self {
        PureFunctionState {
            expr
        }
    }

    fn expr(&self) -> &vir::Expr {
        &self.expr
    }

    fn into_expression(self) -> vir::Expr {
        self.expr
    }

    pub fn substitute_place(&mut self, sub_target: &vir::Place, replacement: vir::Place) {
        debug!("substitute_place {:?} --> {:?}", sub_target, replacement);
        self.expr = vir::utils::ExprSubPlaceSubstitutor::substitute(self.expr.clone(), sub_target, replacement);
    }

    pub fn substitute_value(&mut self, exact_target: &vir::Place, replacement: vir::Expr) {
        debug!("substitute_value {:?} --> {:?}", exact_target, replacement);
        self.expr = vir::utils::ExprExactPlaceSubstitutor::substitute(self.expr.clone(), exact_target, replacement);
    }

    pub fn uses_place(&self, sub_target: &vir::Place) -> bool {
        debug!("uses_place {:?}", sub_target);
        vir::utils::ExprPlaceFinder::find(&self.expr, sub_target)
    }
}


struct PureFunctionInterpreter<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>,
    mir_encoder: MirEncoder<'p, 'v, 'r, 'a, 'tcx>
}

/// XXX: This encoding works backward, but there is the risk of generating expressions whose length
/// is exponential in the number of branches. If this becomes a problem, consider doing a forward
/// encoding (keeping path conditions expressions).
impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> PureFunctionInterpreter<'p, 'v, 'r, 'a, 'tcx> {
    fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, mir: &'p mir::Mir<'tcx>) -> Self {
        PureFunctionInterpreter {
            encoder,
            mir,
            mir_encoder: MirEncoder::new(encoder, mir, "_pure".to_string())
        }
    }

    fn mir_encoder(&self) -> &MirEncoder<'p, 'v, 'r, 'a, 'tcx> {
        &self.mir_encoder
    }
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> BackwardMirInterpreter<'tcx> for PureFunctionInterpreter<'p, 'v, 'r, 'a, 'tcx> {
    type State = PureFunctionState;

    fn apply_terminator(&self, term: &mir::Terminator<'tcx>, states: HashMap<mir::BasicBlock, &Self::State>) -> Self::State {
        debug!("apply_terminator {:?}, states: {:?}", term, states);
        use rustc::mir::TerminatorKind;

        let undef_expr = {
            // Generate a function call that leaves the expression undefined.
            let return_type = self.encoder.encode_value_type(self.mir.return_ty());
            let function_name = self.encoder.encode_builtin_function_use(
                BuiltinFunctionKind::Undefined(return_type.clone())
            );
            vir::Expr::FuncApp(function_name, vec![], vec![], return_type)
        };

        match term.kind {
            TerminatorKind::Unreachable |
            TerminatorKind::Abort |
            TerminatorKind::Drop{..} |
            TerminatorKind::Resume{..} => {
                assert!(states.is_empty());
                PureFunctionState::new(undef_expr)
            }

            TerminatorKind::Goto { ref target } => {
                assert_eq!(states.len(), 1);
                states[target].clone()
            }

            TerminatorKind::FalseEdges { ref real_target, .. } => {
                assert_eq!(states.len(), 2);
                states[real_target].clone()
            }

            TerminatorKind::FalseUnwind { ref real_target, .. } => {
                assert_eq!(states.len(), 1);
                states[real_target].clone()
            }

            TerminatorKind::Return => {
                assert!(states.is_empty());
                debug!("Return type: {:?}", self.mir.return_ty());
                let return_type = self.encoder.encode_type(self.mir.return_ty());
                let return_var = vir::LocalVar::new("_pure_0", return_type);
                let field = self.encoder.encode_value_field(self.mir.return_ty());
                PureFunctionState::new(vir::Place::Base(return_var.into()).access(field).into())
            }

            TerminatorKind::SwitchInt { ref targets, ref discr, ref values, switch_ty } => {
                trace!("SwitchInt ty '{:?}', discr '{:?}', values '{:?}'", switch_ty, discr, values);
                let mut cfg_targets: Vec<(vir::Expr, mir::BasicBlock)> = vec![];
                let discr_val = self.mir_encoder.encode_operand_expr(discr);
                for (i, &value) in values.iter().enumerate() {
                    let target = targets[i as usize];
                    // Convert int to bool, if required
                    let viper_guard = match switch_ty.sty {
                        ty::TypeVariants::TyBool => {
                            if value == 0 {
                                // If discr is 0 (false)
                                vir::Expr::not(discr_val.clone().into())
                            } else {
                                // If discr is not 0 (true)
                                discr_val.clone().into()
                            }
                        }

                        ty::TypeVariants::TyInt(_) |
                        ty::TypeVariants::TyUint(_) => {
                            vir::Expr::eq_cmp(
                                discr_val.clone().into(),
                                self.encoder.encode_int_cast(value, switch_ty)
                            )
                        }

                        ref x => unreachable!("{:?}", x)
                    };
                    cfg_targets.push((viper_guard, target))
                }
                let default_target = targets[values.len()];

                PureFunctionState::new(
                    cfg_targets.into_iter().fold(
                        states[&default_target].expr().clone(),
                        |else_expr, (guard, then_target)|
                            vir::Expr::ite(guard, states[&then_target].expr().clone(), else_expr)
                    )
                )
            }

            TerminatorKind::DropAndReplace { ref target, ref location, ref value, .. } => {
                unimplemented!();
            }

            TerminatorKind::Call {
                ref args,
                ref destination,
                func: mir::Operand::Constant(
                    box mir::Constant {
                        literal: mir::Literal::Value {
                            value: ty::Const {
                                ty: &ty::TyS {
                                    sty: ty::TyFnDef(def_id, ..),
                                    ..
                                },
                                ..
                            }
                        },
                        ..
                    }
                ),
                ..
            } => {
                let func_proc_name: &str = &self.encoder.env().get_item_name(def_id);
                match func_proc_name {
                    "prusti_contracts::internal::old" => {
                        debug!("Encoding old expression {:?}", args[0]);
                        assert!(args.len() == 1);
                        assert!(destination.is_some());
                        let (ref lhs_place, target_block) = destination.as_ref().unwrap();
                        let (encoded_lhs, ty, _) = self.mir_encoder.encode_place(lhs_place);
                        let lhs_value = encoded_lhs.clone().access(self.encoder.encode_value_field(ty));
                        let arg_expr = self.mir_encoder.encode_operand_expr(&args[0]);
                        let encoded_rhs = vir::Expr::labelled_old(PRECONDITION_LABEL, arg_expr);

                        let mut state = states[&target_block].clone();
                        state.substitute_value(&lhs_value, encoded_rhs);
                        state
                    }

                    // generic function call
                    _ => {
                        debug!("Encoding function call '{}'", func_proc_name);
                        unimplemented!();
                    }
                }
            }

            TerminatorKind::Call { .. } => {
                // Other kind of calls?
                unimplemented!();
            }

            TerminatorKind::Assert { ref cond, expected, ref target, ref msg, .. } => {
                let cond_val = self.mir_encoder.encode_operand_expr(cond);
                let viper_guard = if expected {
                    cond_val
                } else {
                    vir::Expr::not(cond_val)
                };

                PureFunctionState::new(
                    vir::Expr::ite(
                        viper_guard,
                        states[target].expr().clone(),
                        undef_expr
                    )
                )
            }

            TerminatorKind::Resume |
            TerminatorKind::Yield { .. } |
            TerminatorKind::GeneratorDrop => unimplemented!("{:?}", term.kind),
        }
    }

    fn apply_statement(&self, stmt: &mir::Statement<'tcx>, state: &mut Self::State) {
        debug!("apply_statement {:?}, state: {:?}", stmt, state);

        match stmt.kind {
            mir::StatementKind::StorageLive(..) |
            mir::StatementKind::StorageDead(..) |
            mir::StatementKind::ReadForMatch(..) => {
                // Nothing to do
            }

            mir::StatementKind::Assign(ref lhs, ref rhs) => {
                let (encoded_lhs, ty, _) = self.mir_encoder.encode_place(lhs);

                if !state.uses_place(&encoded_lhs) {
                    // If the lhs is not mentioned in our state, do nothing
                    debug!("The state does not mention {:?}", encoded_lhs);
                    return
                }

                let opt_lhs_value_place = match ty.sty {
                    ty::TypeVariants::TyBool |
                    ty::TypeVariants::TyInt(..) |
                    ty::TypeVariants::TyUint(..) |
                    ty::TypeVariants::TyRawPtr(..) |
                    ty::TypeVariants::TyRef(..) => {
                        Some(encoded_lhs.clone().access(self.encoder.encode_value_field(ty)))
                    }
                    _ => None
                };

                let type_name = self.encoder.encode_type_predicate_use(ty);
                match rhs {
                    &mir::Rvalue::Use(ref operand) => {
                        let opt_encoded_rhs = self.mir_encoder.encode_operand_place(operand);

                        match opt_encoded_rhs {
                            Some(encode_rhs) => {
                                // Substitute a place
                                state.substitute_place(&encoded_lhs, encode_rhs);
                            },
                            None => {
                                // Substitute a place of a value with an expression
                                let rhs_expr = self.mir_encoder.encode_operand_expr(operand);
                                state.substitute_value(&opt_lhs_value_place.unwrap(), rhs_expr);
                            },
                        }
                    }

                    &mir::Rvalue::Aggregate(..) => {
                        unimplemented!()
                    }

                    &mir::Rvalue::BinaryOp(op, ref left, ref right) => {
                        let encoded_left = self.mir_encoder.encode_operand_expr(left);
                        let encoded_right = self.mir_encoder.encode_operand_expr(right);

                        let field = self.encoder.encode_value_field(ty);
                        let encoded_value = self.mir_encoder.encode_bin_op_expr(op, encoded_left, encoded_right, ty);

                        // Substitute a place of a value with an expression
                        state.substitute_value(&opt_lhs_value_place.unwrap(), encoded_value);
                    }

                    &mir::Rvalue::CheckedBinaryOp(op, ref left, ref right) => {
                        let encoded_left = self.mir_encoder.encode_operand_expr(left);
                        let encoded_right = self.mir_encoder.encode_operand_expr(right);

                        let encoded_value = self.mir_encoder.encode_bin_op_expr(op, encoded_left.clone(), encoded_right.clone(), ty);
                        let encoded_check = self.mir_encoder.encode_bin_op_check(op, encoded_left, encoded_right);

                        let field_types = if let ty::TypeVariants::TyTuple(ref x) = ty.sty { x } else { unreachable!() };
                        let value_field = self.encoder.encode_ref_field("tuple_0", field_types[0]);
                        let value_field_value = self.encoder.encode_value_field(field_types[0]);
                        let check_field = self.encoder.encode_ref_field("tuple_1", field_types[1]);
                        let check_field_value = self.encoder.encode_value_field(field_types[1]);

                        let lhs_value = encoded_lhs.clone()
                            .access(value_field)
                            .access(value_field_value);
                        let lhs_check = encoded_lhs.clone()
                            .access(check_field)
                            .access(check_field_value);

                        // Substitute a place of a value with an expression
                        state.substitute_value(&lhs_value, encoded_value);
                        state.substitute_value(&lhs_check, encoded_check);
                    }

                    &mir::Rvalue::UnaryOp(op, ref operand) => {
                        let encoded_val = self.mir_encoder.encode_operand_expr(operand);

                        let field = self.encoder.encode_value_field(ty);
                        let encoded_value = self.mir_encoder.encode_unary_op_expr(op, encoded_val);

                        unimplemented!()
                    }

                    &mir::Rvalue::NullaryOp(op, ref op_ty) => {
                        unimplemented!()
                    }

                    &mir::Rvalue::Discriminant(ref src) => {
                        let (encoded_src, src_ty, _) = self.mir_encoder.encode_place(src);
                        match src_ty.sty {
                            ty::TypeVariants::TyAdt(ref adt_def, _) if !adt_def.is_box() => {
                                let num_variants = adt_def.variants.len();

                                let discr_value: vir::Expr = if num_variants <= 1 {
                                    0.into()
                                } else {
                                    let discr_field = self.encoder.encode_discriminant_field();
                                    encoded_src.access(discr_field).into()
                                };

                                // Substitute a place of a value with an expression
                                state.substitute_value(&opt_lhs_value_place.unwrap(), discr_value);
                            }
                            ref x => {
                                panic!("The discriminant of type {:?} is not defined", x);
                            }
                        }
                    }

                    &mir::Rvalue::Ref(ref _region, mir::BorrowKind::Shared, ref place) => {
                        unimplemented!()
                    }

                    &mir::Rvalue::Ref(ref _region, mir::BorrowKind::Unique, ref place) |
                    &mir::Rvalue::Ref(ref _region, mir::BorrowKind::Mut{ .. }, ref place)=> {
                        let ref_field = self.encoder.encode_value_field(ty);
                        let (encoded_value, _, _) = self.mir_encoder.encode_place(place);

                        unimplemented!()
                    }

                    ref rhs => {
                        unimplemented!("encoding of '{:?}'", rhs);
                    }
                }
            }

            ref stmt => unimplemented!("encoding of '{:?}'", stmt)
        }
    }
}
