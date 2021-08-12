// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::vir;
use rustc_middle::{mir, ty, span_bug};
use rustc_span::Span;
use std::collections::HashMap;
use std::fmt::{self, Debug, Display};
use std::iter::FromIterator;
use std::marker::Sized;
use log::{trace, debug};
use crate::encoder::pure_function_encoder::{PureFunctionEncoder, PureFunctionBackwardInterpreter};
use crate::encoder::errors::{SpannedEncodingResult, EncodingError, ErrorCtxt, WithSpan};
use crate::encoder::builtin_encoder::BuiltinFunctionKind;
use prusti_interface::data::ProcedureDefId;

/// Backward interpreter for a loop-less MIR
pub trait BackwardMirInterpreter<'tcx> {
    type Error: Sized;
    type State: Sized;
    fn apply_terminator(
        &self,
        bb: mir::BasicBlock,
        terminator: &mir::Terminator<'tcx>,
        states: HashMap<mir::BasicBlock, &Self::State>,
    ) -> Result<Self::State, Self::Error>;
    fn apply_statement(
        &self,
        bb: mir::BasicBlock,
        stmt_index: usize,
        stmt: &mir::Statement<'tcx>,
        state: &mut Self::State,
    ) -> Result<(), Self::Error>;
}

/// Interpret a loop-less MIR starting from the end and return the **initial** state.
/// The result is None if the CFG contains a loop.
pub fn run_backward_interpretation<'tcx, S, E, I>(
    mir: &mir::Body<'tcx>,
    interpreter: &I,
) -> Result<Option<S>, E> where
    S: Debug,
    E: Debug,
    I: BackwardMirInterpreter<'tcx, State = S, Error = E>
{
    let basic_blocks = mir.basic_blocks();
    let mut heads: HashMap<mir::BasicBlock, S> = HashMap::new();

    // Find the final basic blocks
    let mut pending_blocks: Vec<mir::BasicBlock> = basic_blocks
        .iter_enumerated()
        .filter(|(_, bb_data)| match bb_data.terminator {
            Some(ref term) => term.successors().next().is_none(),
            _ => false,
        })
        .map(|(bb, _)| bb)
        .collect();

    // Interpret all the blocks in `pending_blocks`
    while !pending_blocks.is_empty() {
        let curr_bb = pending_blocks.pop().unwrap();
        let bb_data = &basic_blocks[curr_bb];

        // Apply the terminator
        let terminator = bb_data.terminator();
        let states = HashMap::from_iter(terminator.successors().map(|bb| (*bb, &heads[bb])));
        trace!("States before: {:?}", states);
        trace!("Apply terminator {:?}", terminator);
        let mut curr_state = interpreter.apply_terminator(curr_bb, terminator, states)?;
        trace!("State after: {:?}", curr_state);

        // Apply each statement, from the last
        for (stmt_index, stmt) in bb_data.statements.iter().enumerate().rev() {
            trace!("State before: {:?}", curr_state);
            trace!("Apply statement {:?}", stmt);
            interpreter.apply_statement(curr_bb, stmt_index, stmt, &mut curr_state)?;
            trace!("State after: {:?}", curr_state);
        }

        // Store the state at the beginning of block `curr_bb`
        heads.insert(curr_bb, curr_state);

        // Put the preceding basic blocks
        for &pred_bb in mir.predecessors()[curr_bb].iter() {
            if let Some(ref term) = basic_blocks[pred_bb].terminator {
                if term.successors().all(|succ_bb| heads.contains_key(succ_bb)) {
                    pending_blocks.push(pred_bb);
                }
            }
        }
    }

    let result = heads.remove(&basic_blocks.indices().next().unwrap());

    if result.is_none() {
        trace!("heads: {:?}", heads);
    }

    Ok(result)
}

/// Interpret a loop-less MIR starting from the end and return the **initial** state.
/// The result is None if the CFG contains a loop.
pub fn run_backward_interpretation_point_to_point<
    'tcx,
    S: Debug + Clone,
    E,
    I: BackwardMirInterpreter<'tcx, State = S, Error = E>,
>(
    mir: &mir::Body<'tcx>,
    interpreter: &I,
    initial_bbi: mir::BasicBlock,
    final_bbi: mir::BasicBlock,
    final_stmt_index: usize,
    final_state: S,
    empty_state: S,
) -> Result<Option<S>, E> {
    let basic_blocks = mir.basic_blocks();
    let mut heads: HashMap<mir::BasicBlock, S> = HashMap::new();
    trace!(
        "[start] run_backward_interpretation_point_to_point:\n - from final block {:?}, statement {}\n - and state {:?}\n - to initial block {:?}\n - using empty state {:?}",
        final_bbi,
        final_stmt_index,
        final_state,
        initial_bbi,
        empty_state
    );

    // Find the final basic blocks
    let mut pending_blocks: Vec<mir::BasicBlock> = vec![final_bbi];

    // Interpret all the blocks in `pending_blocks`
    while !pending_blocks.is_empty() {
        let curr_bb = pending_blocks.pop().unwrap();
        let bb_data = &basic_blocks[curr_bb];
        trace!("curr_bb: {:?}", curr_bb);

        // Apply the terminator
        let terminator = bb_data.terminator();
        let terminator_index = bb_data.statements.len();
        let states = {
            // HACK: define the state even if only one successor is defined
            let default_state = terminator
                .successors()
                .flat_map(|bb| heads.get(bb))
                .next()
                .unwrap_or(&empty_state);
            HashMap::from_iter(
                terminator
                    .successors()
                    .map(|bb| (*bb, heads.get(bb).unwrap_or(&default_state))),
            )
        };
        trace!("States before: {:?}", states);
        trace!("Apply terminator {:?}", terminator);
        let mut curr_state = interpreter.apply_terminator(
            curr_bb,
            terminator,
            states
        )?;
        trace!("State after: {:?}", curr_state);
        if curr_bb == final_bbi && final_stmt_index == terminator_index {
            trace!("Final location reached in terminator");
            curr_state = final_state.clone();
            trace!("State after: {:?}", curr_state);
        }

        // Apply each statement, from the last
        for (stmt_index, stmt) in bb_data.statements.iter().enumerate().rev() {
            trace!("State before: {:?}", curr_state);
            trace!("Apply statement {:?}", stmt);
            interpreter.apply_statement(curr_bb, stmt_index, stmt, &mut curr_state)?;
            trace!("State after: {:?}", curr_state);
            if curr_bb == final_bbi && final_stmt_index == stmt_index {
                trace!("Final location reached in statement");
                curr_state = final_state.clone();
                trace!("State after: {:?}", curr_state);
            }
        }

        // Store the state at the beginning of block `curr_bb`
        heads.insert(curr_bb, curr_state);

        if curr_bb != initial_bbi {
            // Put the preceding basic blocks
            for &pred_bb in mir.predecessors()[curr_bb].iter() {
                // Note: here we don't check that all the successors of `pred_bb` has been visited.
                // It's a known limitation, because this is the point-to-point interpretation.
                // Use `run_backward_interpretation` if the check is important.
                pending_blocks.push(pred_bb);
            }
        }
    }

    let result = heads.remove(&initial_bbi);

    if result.is_none() {
        trace!("heads: {:?}", heads);
    }

    trace!(
        "[end] run_backward_interpretation_point_to_point:\n - from final final block {:?}, statement {}\n - and state {:?}\n - to initial block {:?}\n - using empty state {:?}\n - resulted in state {:?}",
        final_bbi,
        final_stmt_index,
        final_state,
        initial_bbi,
        empty_state,
        result
    );

    Ok(result)
}

/// Forward interpreter for a loop-less MIR
pub trait ForwardMirInterpreter<'tcx> {
    type State: Sized;
    fn initial_state(&self) -> Self::State;
    fn apply_statement(&self, stmt: &mir::Statement<'tcx>, state: &mut Self::State);
    fn apply_terminator(
        &self,
        terminator: &mir::Terminator<'tcx>,
        state: &Self::State,
    ) -> (HashMap<mir::BasicBlock, Self::State>, Option<Self::State>);
    fn join(&self, states: &[&Self::State]) -> Self::State;
}

pub(super) trait PureBackwardSubstitutionState {
    fn apply_assignment<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        pure_fn_interpreter: &PureFunctionBackwardInterpreter<'p, 'v, 'tcx>,
        lhs: &mir::Place<'tcx>,
        rhs: &mir::Rvalue<'tcx>,
        span: Span,
        parent_def_id: ProcedureDefId
    ) -> SpannedEncodingResult<()>
    {
        let (encoded_lhs, ty, _) = pure_fn_interpreter.encode_place(lhs).unwrap();

        if !self.use_place(&encoded_lhs) {
            // If the lhs is not mentioned in our state, do nothing
            trace!("The state does not mention {:?}", encoded_lhs);
            return Ok(());
        }

        let opt_lhs_value_place = match ty.kind() {
            ty::TyKind::Bool
            | ty::TyKind::Int(..)
            | ty::TyKind::Uint(..)
            | ty::TyKind::RawPtr(..)
            | ty::TyKind::Ref(..) => Some(
                pure_fn_interpreter.encoder.encode_value_expr(
                    encoded_lhs.clone(),
                    ty
                ).with_span(span)?
                // encoded_lhs
                //     .clone()
                //     .field(pure_fn_interpreter.encoder.encode_value_field(ty)),
            ),
            _ => None,
        };

        match rhs {
            &mir::Rvalue::Use(ref operand) => {
                let opt_encoded_rhs = pure_fn_interpreter.encode_operand_place(operand)
                    .with_span(span)?;

                match opt_encoded_rhs {
                    Some(encoded_rhs) => {
                        // Substitute a place
                        self.substitute_place(&encoded_lhs, encoded_rhs);
                    }
                    None => {
                        // Substitute a place of a value with an expression
                        if let Some(lhs_value_place) = &opt_lhs_value_place {
                            // opt_lhs_value_place can be none in trigger generation code.
                            let rhs_expr = pure_fn_interpreter.mir_encoder
                                .encode_operand_expr(operand)
                                .with_span(span)?;
                            self.substitute_value(lhs_value_place, rhs_expr);
                        }
                    }
                }
            }

            &mir::Rvalue::Aggregate(ref aggregate, ref operands) => {
                debug!("Encode aggregate {:?}, {:?}", aggregate, operands);
                match aggregate.as_ref() {
                    &mir::AggregateKind::Tuple => {
                        let field_types = if let ty::TyKind::Tuple(ref x) = ty.kind() {
                            x
                        } else {
                            unreachable!()
                        };
                        let mut field_exprs = vec![];
                        for (field_num, operand) in operands.iter().enumerate() {
                            let field_name = format!("tuple_{}", field_num);
                            let field_ty = field_types[field_num];
                            let encoded_field = pure_fn_interpreter.encoder
                                .encode_raw_ref_field(field_name, field_ty.expect_ty())
                                .with_span(span)?;
                            let field_place = encoded_lhs.clone().field(encoded_field);

                            let encoded_operand = pure_fn_interpreter.encode_operand_place(operand)
                                .with_span(span)?;
                            match encoded_operand {
                                Some(encoded_rhs) => {
                                    // Substitute a place
                                    field_exprs.push(encoded_rhs.clone());
                                    self.substitute_place(&field_place, encoded_rhs);
                                }
                                None => {
                                    // Substitute a place of a value with an expression
                                    let rhs_expr =
                                        pure_fn_interpreter.mir_encoder.encode_operand_expr(operand)
                                            .with_span(span)?;
                                    field_exprs.push(rhs_expr.clone());
                                    self.substitute_value(
                                        &pure_fn_interpreter.encoder.encode_value_expr(field_place, field_ty.expect_ty()).with_span(span)?,
                                        rhs_expr,
                                    );
                                }
                            }
                        }
                        let snapshot = pure_fn_interpreter.encoder.encode_snapshot_constructor(
                            ty,
                            field_exprs,
                        ).with_span(span)?;
                        self.substitute_place(&encoded_lhs, snapshot);
                    }

                    &mir::AggregateKind::Adt(adt_def, variant_index, subst, _, _) => {
                        let num_variants = adt_def.variants.len();
                        let variant_def = &adt_def.variants[variant_index];
                        let mut encoded_lhs_variant = encoded_lhs.clone();
                        if num_variants != 1 {
                            let discr_field = pure_fn_interpreter.encoder.encode_discriminant_field();
                            self.substitute_value(
                                &encoded_lhs.clone().field(discr_field),
                                variant_index.index().into(),
                            );
                            encoded_lhs_variant =
                                encoded_lhs_variant.variant(&variant_def.ident.as_str());
                        }
                        for (field_index, field) in variant_def.fields.iter().enumerate() {
                            let operand = &operands[field_index];
                            let field_name = &field.ident.as_str();
                            let tcx = pure_fn_interpreter.encoder.env().tcx();
                            let field_ty = field.ty(tcx, subst);
                            let encoded_field = pure_fn_interpreter.encoder
                                .encode_struct_field(field_name, field_ty)
                                .with_span(span)?;

                            let field_place =
                                encoded_lhs_variant.clone().field(encoded_field);

                            let encoded_operand = pure_fn_interpreter.encode_operand_place(operand)
                                .with_span(span)?;
                            match encoded_operand {
                                Some(encoded_rhs) => {
                                    // Substitute a place
                                    self.substitute_place(&field_place, encoded_rhs);
                                }
                                None => {
                                    // Substitute a place of a value with an expression
                                    let rhs_expr =
                                        pure_fn_interpreter.mir_encoder.encode_operand_expr(operand)
                                            .with_span(span)?;
                                    self.substitute_value(
                                        &pure_fn_interpreter.encoder.encode_value_expr(field_place, field_ty).with_span(span)?,
                                        rhs_expr,
                                    );
                                }
                            }
                        }
                    }

                    &mir::AggregateKind::Array(elem_ty) => {
                        let mut encoded_operands = Vec::with_capacity(operands.len());
                        for oper in operands {
                            let encoded_oper = pure_fn_interpreter.encode_operand_place(oper)
                                .with_span(span)?;
                            let encoded_oper = match encoded_oper {
                                Some(encoded_rhs) => encoded_rhs,
                                None => {
                                    pure_fn_interpreter.mir_encoder.encode_operand_expr(oper)
                                        .with_span(span)?
                                }
                            };
                            encoded_operands.push(encoded_oper);
                        }

                        let encoded_elem_ty = pure_fn_interpreter.encoder.encode_snapshot_type(elem_ty)
                            .with_span(span)?;
                        let elems = vir::Expr::Seq(
                            vir::Type::Seq(box encoded_elem_ty),
                            encoded_operands,
                            vir::Position::default(),
                        );

                        let snapshot = pure_fn_interpreter.encoder.encode_snapshot_constructor(
                            ty,
                            vec![elems],
                        ).with_span(span)?;

                        self.substitute_place(&encoded_lhs, snapshot);
                    }

                    ref x => unimplemented!("{:?}", x),
                }
            }

            &mir::Rvalue::BinaryOp(op, box(ref left, ref right)) => {
                let encoded_left = pure_fn_interpreter.mir_encoder.encode_operand_expr(left)
                    .with_span(span)?;
                let encoded_right = pure_fn_interpreter.mir_encoder.encode_operand_expr(right)
                    .with_span(span)?;
                let encoded_value = pure_fn_interpreter.mir_encoder.encode_bin_op_expr(
                    op,
                    vir::Expr::snap_app(encoded_left),
                    vir::Expr::snap_app(encoded_right),
                    ty,
                ).with_span(span)?;

                // Substitute a place of a value with an expression
                self.substitute_value(&opt_lhs_value_place.unwrap(), encoded_value);
            }

            &mir::Rvalue::CheckedBinaryOp(op, box (ref left, ref right)) => {
                let operand_ty = if let ty::TyKind::Tuple(ref types) = ty.kind() {
                    types[0].clone()
                } else {
                    unreachable!()
                };

                let encoded_left = pure_fn_interpreter.mir_encoder.encode_operand_expr(left)
                    .with_span(span)?;
                let encoded_right = pure_fn_interpreter.mir_encoder.encode_operand_expr(right)
                    .with_span(span)?;

                let encoded_value = pure_fn_interpreter.mir_encoder.encode_bin_op_expr(
                    op,
                    vir::Expr::snap_app(encoded_left.clone()),
                    vir::Expr::snap_app(encoded_right.clone()),
                    operand_ty.expect_ty(),
                ).with_span(span)?;
                let encoded_check = pure_fn_interpreter.mir_encoder.encode_bin_op_check(
                    op,
                    vir::Expr::snap_app(encoded_left),
                    vir::Expr::snap_app(encoded_right),
                    operand_ty.expect_ty(),
                ).with_span(span)?;

                let field_types = if let ty::TyKind::Tuple(ref x) = ty.kind() {
                    x
                } else {
                    unreachable!()
                };
                let value_field = pure_fn_interpreter.encoder
                    .encode_raw_ref_field("tuple_0".to_string(), field_types[0].expect_ty())
                    .with_span(span)?;
                let value_field_value = pure_fn_interpreter.encoder
                    .encode_value_field(field_types[0].expect_ty()).with_span(span)?;
                let check_field = pure_fn_interpreter.encoder
                    .encode_raw_ref_field("tuple_1".to_string(), field_types[1].expect_ty())
                    .with_span(span)?;
                let check_field_value = pure_fn_interpreter.encoder
                    .encode_value_field(field_types[1].expect_ty()).with_span(span)?;

                let lhs_value = encoded_lhs
                    .clone()
                    .field(value_field)
                    .field(value_field_value);
                let lhs_check = encoded_lhs
                    .clone()
                    .field(check_field)
                    .field(check_field_value);

                // Substitute a place of a value with an expression
                self.substitute_value(&lhs_value, encoded_value);
                self.substitute_value(&lhs_check, encoded_check);
            }

            &mir::Rvalue::UnaryOp(op, ref operand) => {
                let encoded_val = pure_fn_interpreter.mir_encoder.encode_operand_expr(operand)
                    .with_span(span)?;
                let encoded_value = pure_fn_interpreter.mir_encoder.encode_unary_op_expr(op, encoded_val);

                // Substitute a place of a value with an expression
                self.substitute_value(&opt_lhs_value_place.unwrap(), encoded_value);
            }

            &mir::Rvalue::NullaryOp(_op, ref _op_ty) => unimplemented!(),

            &mir::Rvalue::Discriminant(ref src) => {
                let (encoded_src, src_ty, _) = pure_fn_interpreter.encode_place(src).unwrap();
                match src_ty.kind() {
                    ty::TyKind::Adt(ref adt_def, _) if !adt_def.is_box() => {
                        let num_variants = adt_def.variants.len();

                        let discr_value: vir::Expr = if num_variants == 0 {
                            let pos = pure_fn_interpreter
                                .encoder
                                .error_manager()
                                .register(span, ErrorCtxt::Unexpected, parent_def_id);
                            let function_name = pure_fn_interpreter.encoder.encode_builtin_function_use(
                                BuiltinFunctionKind::Unreachable(vir::Type::Int),
                            );
                            vir::Expr::func_app(
                                function_name,
                                vec![],
                                vec![],
                                vir::Type::Int,
                                pos,
                            )
                        } else {
                            if num_variants == 1 {
                                0.into()
                            } else {
                                let discr_field = pure_fn_interpreter.encoder.encode_discriminant_field();
                                encoded_src.field(discr_field).into()
                            }
                        };

                        // Substitute a place of a value with an expression
                        self.substitute_value(&opt_lhs_value_place.unwrap(), discr_value);
                    }
                    ref x => {
                        panic!("The discriminant of type {:?} is not defined", x);
                    }
                }
            }

            &mir::Rvalue::Ref(_, mir::BorrowKind::Unique, ref place)
            | &mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, ref place)
            | &mir::Rvalue::Ref(_, mir::BorrowKind::Shared, ref place) => {
                // will panic if attempting to encode unsupported type
                let encoded_place = pure_fn_interpreter.encode_place(place).unwrap().0;
                let encoded_ref = match encoded_place {
                    vir::Expr::Field(
                        box ref base,
                        vir::Field { ref name, .. },
                        ref _pos,
                    ) if name == "val_ref" => {
                        // Simplify "address of reference"
                        base.clone()
                    }
                    other_place => other_place.addr_of(),
                };

                // Substitute the place
                self.substitute_place(&encoded_lhs, encoded_ref);
            }

            &mir::Rvalue::Cast(mir::CastKind::Misc, ref operand, dst_ty) => {
                let encoded_val = pure_fn_interpreter.mir_encoder
                    .encode_cast_expr(operand, dst_ty, span)?;

                // Substitute a place of a value with an expression
                self.substitute_value(&opt_lhs_value_place.unwrap(), encoded_val);
            }

            &mir::Rvalue::Len(ref place) => {
                let place_ty = pure_fn_interpreter.encode_place(place).with_span(span)?.1;
                match place_ty.kind() {
                    ty::TyKind::Array(..) => {
                        let array_types = pure_fn_interpreter.encoder.encode_array_types(place_ty).with_span(span)?;
                        self.substitute_value(&opt_lhs_value_place.unwrap(), array_types.array_len.into());
                    }
                    ty::TyKind::Slice(..) => {
                        let snap_len = pure_fn_interpreter.encoder.encode_snapshot_slice_len(
                            place_ty,
                            pure_fn_interpreter.encode_place(place).with_span(span)?.0,
                        ).with_span(span)?;

                        self.substitute_value(&opt_lhs_value_place.unwrap(), snap_len);
                    }
                    _ => span_bug!(span, "length should only be requested on arrays or slices"),
                }
            }

            &mir::Rvalue::Cast(mir::CastKind::Pointer(ty::adjustment::PointerCast::Unsize), ref operand, ty) => {
                if !ty.is_slice() {
                    return Err(EncodingError::unsupported(
                        "unsizing a pointer or reference value is not supported"
                    )).with_span(span);
                }

                let rhs_array_ref_ty = pure_fn_interpreter.mir_encoder.get_operand_ty(operand);
                let encoded_rhs = if let Some(encoded_place) = pure_fn_interpreter.encode_operand_place(operand).with_span(span)? {
                    encoded_place
                } else {
                    pure_fn_interpreter.mir_encoder.encode_operand_expr(operand)
                        .with_span(span)?
                };
                // encoded_rhs is something like ref$Array$.. or ref$Slice$.. but we want .val_ref: Array$..
                let encoded_rhs = pure_fn_interpreter.encoder.encode_value_expr(encoded_rhs, rhs_array_ref_ty).with_span(span)?;
                let rhs_array_ty = if let ty::TyKind::Ref(_, array_ty, _) = rhs_array_ref_ty.kind() {
                    array_ty
                } else {
                    unreachable!("rhs array not a ref?")
                };
                trace!("rhs_array_ty: {:?}", rhs_array_ty);
                let array_types = pure_fn_interpreter.encoder.encode_array_types(rhs_array_ty).with_span(span)?;

                let encoded_array_elems = (0..array_types.array_len)
                    .map(|idx| {
                        pure_fn_interpreter.encoder.encode_snapshot_array_idx(rhs_array_ty, encoded_rhs.clone(), idx.into())
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .with_span(span)?;

                let elem_snap_ty = pure_fn_interpreter.encoder.encode_snapshot_type(array_types.elem_ty_rs).with_span(span)?;
                let elems_seq = vir::Expr::Seq(
                    vir::Type::Seq(box elem_snap_ty),
                    encoded_array_elems,
                    vir::Position::default(),
                );

                let slice_snap = pure_fn_interpreter.encoder.encode_snapshot_constructor(ty, vec![elems_seq]).with_span(span)?;

                self.substitute_value(&opt_lhs_value_place.unwrap(), slice_snap);

            }

            ref rhs => {
                unimplemented!("encoding of '{:?}'", rhs);
            }
        }

        Ok(())
    }

    fn substitute_place(&mut self, sub_target: &vir::Expr, replacement: vir::Expr);

    fn substitute_value(&mut self, exact_target: &vir::Expr, replacement: vir::Expr);

    fn use_place(&self, sub_target: &vir::Expr) -> bool;
}

#[derive(Clone, Debug)]
pub struct MultiExprBackwardInterpreterState {
    exprs: Vec<vir::Expr>,
}

impl Display for MultiExprBackwardInterpreterState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "exprs={}",
            self.exprs
                .iter()
                .map(|e| format!("{},", e))
                .collect::<String>()
        )
    }
}

impl MultiExprBackwardInterpreterState {
    pub fn new(exprs: Vec<vir::Expr>) -> Self {
        MultiExprBackwardInterpreterState { exprs }
    }

    pub fn new_single(expr: vir::Expr) -> Self {
        MultiExprBackwardInterpreterState { exprs: vec![expr] }
    }

    pub fn exprs(&self) -> &Vec<vir::Expr> {
        &self.exprs
    }

    pub fn exprs_mut(&mut self) -> &mut Vec<vir::Expr> {
        &mut self.exprs
    }

    pub fn into_expressions(self) -> Vec<vir::Expr> {
        self.exprs
    }
}

impl PureBackwardSubstitutionState for MultiExprBackwardInterpreterState {
    fn substitute_place(&mut self, sub_target: &vir::Expr, replacement: vir::Expr) {
        trace!("substitute_place {:?} --> {:?}", sub_target, replacement);

        // If `replacement` is a reference, simplify also its dereferentiations
        if let vir::Expr::AddrOf(box ref base_replacement, ref _dereferenced_type, ref pos) =
        replacement
        {
            trace!("Substitution of a reference. Simplify its dereferentiations.");
            let deref_field = vir::Field::new("val_ref", base_replacement.get_type().clone());
            let deref_target = sub_target
                .clone()
                .field(deref_field.clone())
                .set_pos(*pos);
            self.substitute_place(&deref_target, base_replacement.clone());
        }

        for expr in &mut self.exprs {
            *expr = expr.clone().replace_place(&sub_target, &replacement);
        }
    }

    fn substitute_value(&mut self, exact_target: &vir::Expr, replacement: vir::Expr) {
        trace!("substitute_value {:?} --> {:?}", exact_target, replacement);
        for expr in &mut self.exprs {
            *expr = expr.clone().replace_place(exact_target, &replacement);
        }
    }

    fn use_place(&self, sub_target: &vir::Expr) -> bool {
        trace!("use_place {:?}", sub_target);
        self.exprs.iter().any(|expr| expr.find(sub_target))
    }
}
