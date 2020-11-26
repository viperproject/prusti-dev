// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::errors::{
    ErrorCtxt, EncodingError, PositionlessEncodingError, WithSpan
};
use crate::encoder::mir_encoder::{MirEncoder, PlaceEncoder};
use crate::encoder::mir_encoder::PRECONDITION_LABEL;
use crate::encoder::mir_interpreter::{
    run_backward_interpretation_point_to_point, BackwardMirInterpreter,
    MultiExprBackwardInterpreterState,
};
use crate::encoder::pure_function_encoder::PureFunctionBackwardInterpreter;
use crate::encoder::Encoder;
use prusti_common::config;
use prusti_common::vir;
use prusti_common::vir::ExprIterator;
use prusti_interface::specs::typed;
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty;
use std::collections::HashMap;
use rustc_ast::ast;
use log::{debug, trace};
use prusti_interface::utils::read_prusti_attr;

/// Encode an assertion coming from a specification to a `vir::Expr`.
///
/// In this documentation, we distinguish the encoding of a _value_ of a Rust expression from
/// the encoding of its _memory location_. For example:
/// * given an argument `x: u32` the Viper encoding will use `x: Ref` to encode the memory
///   location and `x.val_int: Int` to encode the value;
/// * given an argument `y: &u32` the Viper encoding will use `y: Ref` to encode the memory
///   location and `y.val_ref: Ref` to encode the value.
///
/// Arguments:
/// * `encoder`: a reference to the `Encoder`.
/// * `assertion`: the assertion to be encoded.
/// * `pre_label`: the label to be used to encode `old(..)` expressions. This should be `None` iff
///   the assertion cannot have old expressions (e.g. a precondition).
/// * `target_args`: the expression to be used to encode arguments.
/// * `target_return`: the expression to be used to encode `return` expressions. This should be
///   `None` iff the assertion cannot mention `return` (e.g. a loop invariant).
/// * `targets_are_values`: if `true`, the elements of `target_args` and `target_return` encode
///   _values_ and not _memory locations_. This is typically used to encode pure functions.
/// * `assertion_location`: the basic block at which the assertion should be encoded. This should
///   be `None` iff the assertion is a loop invariant.
pub fn encode_spec_assertion<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    assertion: &typed::Assertion<'tcx>,
    pre_label: Option<&str>,
    target_args: &[vir::Expr],
    target_return: Option<&vir::Expr>,
    targets_are_values: bool,
    assertion_location: Option<mir::BasicBlock>,
) -> Result<vir::Expr, EncodingError> {
    let spec_encoder = SpecEncoder::new(
        encoder,
        pre_label.unwrap_or(""),
        target_args,
        target_return,
        targets_are_values,
        assertion_location,
    );
    spec_encoder.encode_assertion(assertion)
}

struct SpecEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    /// The label to encode `old(..)` expressions
    pre_label: &'p str,
    /// The expression that encodes the arguments.
    target_args: &'p [vir::Expr],
    /// The expression that encodes `return` in a postcondition.
    target_return: Option<&'p vir::Expr>,
    /// Used to encode pure functions.
    targets_are_values: bool,
    /// Location at which to encode loop invariants.
    assertion_location: Option<mir::BasicBlock>,
}

impl<'p, 'v: 'p, 'tcx: 'v> SpecEncoder<'p, 'v, 'tcx> {
    fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        pre_label: &'p str,
        target_args: &'p [vir::Expr],
        target_return: Option<&'p vir::Expr>,
        targets_are_values: bool,
        assertion_location: Option<mir::BasicBlock>,
    ) -> Self {
        trace!("SpecEncoder constructor");

        SpecEncoder {
            encoder,
            pre_label,
            target_args,
            target_return,
            targets_are_values,
            assertion_location,
        }
    }

    /// Encode a quantified variable `arg`, given its type `arg_ty` and a unique identifier
    /// `forall_id` of the quantification.
    fn encode_forall_arg(
        &self,
        arg: mir::Local,
        arg_ty: ty::Ty<'tcx>,
        forall_id: &str
    ) -> vir::LocalVar {
        trace!("encode_forall_arg: {:?} {:?} {:?}", arg, arg_ty, forall_id);
        assert!(
            match arg_ty.kind() {
                ty::TyKind::Int(..) | ty::TyKind::Uint(..) => true,
                _ => false,
            },
            "Quantification is only supported over integer values"
        );
        let var_name = format!("{:?}_forall_{}", arg, forall_id);
        vir::LocalVar::new(var_name, vir::Type::Int)
    }

    fn encode_trigger(&self, trigger: &typed::Trigger) -> vir::Trigger {
        trace!("encode_trigger {:?}", trigger);
        // TODO: `encode_hir_expr` generated also the final `.val_int` field access, that we may not want...
        // vir::Trigger::new(
        //     trigger
        //         .terms()
        //         .iter()
        //         .map(|expr| self.encode_hir_expr(&expr.expr))
        //         .collect(),
        // )
        unimplemented!();
    }

    /// Encode a specification item as a single expression.
    pub fn encode_assertion(&self, assertion: &typed::Assertion<'tcx>)
        -> Result<vir::Expr, EncodingError>
    {
        trace!("encode_assertion {:?}", assertion);
        Ok(match assertion.kind {
            box typed::AssertionKind::Expr(ref assertion_expr) =>
                self.encode_expression(assertion_expr)?,
            box typed::AssertionKind::And(ref assertions) => assertions
                .iter()
                .map(|x| self.encode_assertion(x))
                .collect::<Result<Vec<vir::Expr>, _>>()?
                .into_iter()
                .conjoin(),
            box typed::AssertionKind::Implies(ref lhs, ref rhs) => {
                vir::Expr::implies(
                    self.encode_assertion(lhs)?,
                    self.encode_assertion(rhs)?
                )
            }
            box typed::AssertionKind::TypeCond(ref vars, ref assertion) => {
                let enc = |ty: ty::Ty<'tcx>| -> vir::Expr {
                    // FIXME: this is a hack to support generics. See issue #187.
                    let ty = self.encoder.resolve_typaram(ty);
                    self.encoder.encode_tag_func_app(ty)
                };
                let typecond =
                    vir::Expr::eq_cmp(enc(vars.vars[0].1), enc(vars.vars[1].1));
                vir::Expr::implies(
                    typecond,
                    self.encode_assertion(assertion)?
                )
            }
            box typed::AssertionKind::ForAll(ref vars, ref trigger_set, ref body) => {
                let mut encoded_args = Vec::new();
                let mut bounds = Vec::new();
                for (arg, ty) in &vars.vars {
                    let encoded_arg = self.encode_forall_arg(*arg, ty, &format!("{}_{}", vars.spec_id, vars.id));
                    if config::check_overflows() {
                        bounds.extend(self.encoder.encode_type_bounds(&encoded_arg.clone().into(), ty));
                    } else if config::encode_unsigned_num_constraint() {
                        if let ty::TyKind::Uint(_) = ty.kind() {
                            let expr = vir::Expr::le_cmp(0.into(), encoded_arg.clone().into());
                            bounds.push(expr);
                        }
                    }
                    encoded_args.push(encoded_arg);
                }
                let encoded_triggers = trigger_set
                    .triggers()
                    .iter()
                    .map(|x| self.encode_trigger(x))
                    .collect();
                let encoded_body = self.encode_assertion(body)?;
                let final_body = if bounds.is_empty() {
                    encoded_body
                } else {
                    vir::Expr::implies(bounds.into_iter().conjoin(), encoded_body)
                };
                vir::Expr::forall(
                    encoded_args,
                    encoded_triggers,
                    final_body,
                )
            },
        })
    }

    /// Translate an expression `expr` from a closure identified by `def_id` to its definition site.
    ///
    /// During the translation:
    /// * Usages of the closure's captured state will be translated to the captured place.
    /// * Closure arguments will be treated as quantified variables and will be translated using
    ///   the `self.encode_forall_arg(..)` method.
    ///
    /// The result is a tuple with:
    /// * the translated expression,
    /// * the def_id of the item in which the closure was defined,
    /// * the location at which the closure was defined.
    fn translate_expr_to_closure_def_site(
        &self,
        expr: vir::Expr,
        inner_def_id: DefId,
    ) -> Result<(vir::Expr, DefId, mir::Location), EncodingError> {
        debug!("translate_expr_to_closure_def_site {} {:?}", expr, inner_def_id);
        let inner_mir = self.encoder.env().mir(inner_def_id.expect_local());
        let inner_mir_encoder = MirEncoder::new(self.encoder, &inner_mir, inner_def_id);
        let inner_attrs = self.encoder.env().tcx().get_attrs(inner_def_id);

        let opt_instantiation = self.encoder.get_single_closure_instantiation(
            inner_def_id
        );
        let (
            outer_def_id,
            outer_location,
            captured_operands,
            captured_operand_tys,
        ) = opt_instantiation.expect(
            &format!("cannot find definition site for closure {:?}", inner_def_id)
        );
        let outer_mir = self.encoder.env().mir(outer_def_id.expect_local());
        let outer_mir_encoder = MirEncoder::new(self.encoder, &outer_mir, outer_def_id);
        let outer_span = outer_mir_encoder.get_span_of_location(outer_location);
        trace!("Replacing variables of {:?} captured from {:?}", inner_def_id, outer_def_id);

        // Take the first argument, which is the closure's captured state.
        // The closure is a record containing all the captured variables.
        let closure_local = inner_mir.args_iter().next().unwrap();
        let closure_var = inner_mir_encoder.encode_local(closure_local)?;
        let closure_ty = &inner_mir.local_decls[closure_local].ty;
        let should_closure_be_dereferenced = inner_mir_encoder.can_be_dereferenced(closure_ty);
        let (deref_closure_var, _deref_closure_ty) = if should_closure_be_dereferenced {
            let res = inner_mir_encoder
                .encode_deref(closure_var.clone().into(), closure_ty)
                .with_span(outer_span)?;
            (res.0, res.1)
        } else {
            (closure_var.clone().into(), *closure_ty)
        };
        trace!("closure_ty: {:?}", closure_ty);
        trace!("deref_closure_var: {:?}", deref_closure_var);

        let captured_tys = captured_operand_tys;
        trace!("captured_tys: {:?}", captured_tys);
        assert_eq!(captured_tys.len(), captured_operands.len());

        // Replacements to translate from the closure to the definition site
        let mut replacements: Vec<(vir::Expr, vir::Expr)> = vec![];

        // Replacement 1: translate a local variable from the closure to a place in the outer MIR
        let inner_captured_places: Vec<_> = captured_tys
            .iter()
            .enumerate()
            .map(|(index, &captured_ty)| {
                let field_name = format!("closure_{}", index);
                self.encoder.encode_raw_ref_field(field_name, captured_ty)
                    .with_span(outer_span)
                    .map(|encoded_field|
                        deref_closure_var.clone().field(encoded_field)
                    )
            })
            .collect::<Result<_, _>>()?;
        let outer_captured_places: Vec<_> = captured_operands
            .iter()
            .map(|operand| outer_mir_encoder.encode_operand_place(operand))
            .collect::<Result<Vec<_>, _>>()
            .with_span(outer_span)?
            .into_iter()
            .map(|x| x.unwrap())
            .collect();
        for (index, (inner_place, outer_place)) in inner_captured_places
            .iter()
            .zip(outer_captured_places.iter())
            .enumerate()
        {
            debug!(
                "Field {} of closure, encoded as {}: {}, corresponds to {}: {} \
                in the middle of the enclosing procedure",
                index,
                inner_place,
                inner_place.get_type(),
                outer_place,
                outer_place.get_type()
            );
            assert_eq!(inner_place.get_type(), outer_place.get_type());
        }
        replacements.extend(
            inner_captured_places
                .into_iter()
                .zip(outer_captured_places.into_iter())
        );

        // Replacement 2: rename the variables introduced by a quantification
        let opt_forall_id = read_prusti_attr("expr_id", inner_attrs);
        if let Some(forall_id) = opt_forall_id {
            // Skip the first argument, which is the captured state
            for local_arg_index in inner_mir.args_iter().skip(1) {
                let local_arg = &inner_mir.local_decls[local_arg_index];
                assert!(!local_arg.internal);
                let quantified_var = self.encode_forall_arg(
                    local_arg_index,
                    local_arg.ty,
                    &forall_id
                );
                let encoded_arg = inner_mir_encoder.encode_local(local_arg_index).unwrap();
                let value_field = self.encoder.encode_value_field(local_arg.ty);
                let encoded_arg_value = vir::Expr::local(encoded_arg).field(value_field);
                trace!(
                    "Place {}: {} will be renamed to {} because a quantifier introduced it",
                    encoded_arg_value,
                    encoded_arg_value.get_type(),
                    quantified_var
                );
                replacements.push((encoded_arg_value, quantified_var.into()));
            }
        }

        // Do the replacements
        let outer_expr = expr.replace_multiple_places(&replacements);
        debug!(
            "Expr at the definition site ({:?} {:?}): {}",
            outer_def_id,
            outer_location,
            outer_expr
        );
        Ok((outer_expr, outer_def_id, outer_location))
    }

    /// Given an expression and a program point, return the equivalent expression at a
    /// precedent program point.
    fn translate_expr_to_state(
        &self,
        expr: vir::Expr,
        def_id: DefId,
        expr_location: mir::Location,
        target_location: mir::BasicBlock,
    ) -> Result<vir::Expr, EncodingError> {
        debug!("translate_expr_to_state {} {:?} {:?}", expr, def_id, expr_location);
        let mir = self.encoder.env().mir(def_id.expect_local());

        // Translate an intermediate state to the state at the beginning of the method
        let state = MultiExprBackwardInterpreterState::new_single(
            expr.clone()
        );
        let interpreter = StraightLineBackwardInterpreter::new(
            self.encoder,
            &mir,
            def_id,
        );
        let initial_state = run_backward_interpretation_point_to_point(
            &mir,
            &interpreter,
            target_location,
            expr_location.block,
            expr_location.statement_index,
            state,
            MultiExprBackwardInterpreterState::new(vec![]),
        )?.expect(
            &format!("cannot encode {:?} because its CFG contains a loop", def_id)
        );
        let pre_state_expr = initial_state.into_expressions().remove(0);

        trace!("Expr at the beginning: {}", pre_state_expr);
        Ok(pre_state_expr)
    }

    /// Encode the assertion of a contract or loop invariant.
    fn encode_expression(&self, assertion_expr: &typed::Expression)
        -> Result<vir::Expr, EncodingError>
    {
        debug!("encode_expression {:?}", assertion_expr);

        let mut curr_def_id = assertion_expr.expr.to_def_id();
        let mut curr_expr = self.encoder.encode_pure_function_body(curr_def_id)?;

        loop {
            let done = self.encoder.get_single_closure_instantiation(curr_def_id).is_none();
            if done {
                debug!("end of encode_expression loop: {:?} has no instantiation", curr_def_id);
                break;
            }
            let (
                outer_expr,
                outer_def_id,
                outer_location,
            ) = self.translate_expr_to_closure_def_site(curr_expr, curr_def_id)?;
            let done = self.encoder.get_single_closure_instantiation(outer_def_id).is_none();
            curr_expr = self.translate_expr_to_state(
                outer_expr,
                outer_def_id,
                outer_location,
                if done {
                    self.assertion_location.unwrap_or(mir::START_BLOCK)
                } else {
                    mir::START_BLOCK
                },
            )?;
            curr_def_id = outer_def_id;
        }

        // At this point `curr_def_id` should be either a SPEC item (when encoding a contract) or
        // the method being verified (when encoding a loop invariant).
        let mir = self.encoder.env().mir(curr_def_id.expect_local());
        let mir_encoder = MirEncoder::new(self.encoder, &mir, curr_def_id);

        // Replacements to use the provided `target_args` and `target_return`
        let mut replacements: Vec<(vir::Expr, vir::Expr)> = vec![];

        // Replacement 1: replace the arguments with the `target_args`.
        replacements.extend(
            mir.args_iter()
                .zip(self.target_args)
                .map(|(local, target_arg)| {
                    let local_ty = mir.local_decls[local].ty;
                    // will panic if attempting to encode unsupported type
                    let spec_local = mir_encoder.encode_local(local).unwrap();
                    let spec_local_place: vir::Expr = if self.targets_are_values {
                        self.encoder.encode_value_expr(
                            vir::Expr::local(spec_local),
                            local_ty
                        )
                    } else {
                        spec_local.into()
                    };
                    (spec_local_place, target_arg.clone())
                })
        );

        // Replacement 2: replace the fake return variable (last argument) of SPEC items with
        // `target_return`
        if let Some(target_return) = self.target_return {
            let fake_return_local = mir.args_iter().last().unwrap();
            let fake_return_ty = mir.local_decls[fake_return_local].ty;
            // will panic if attempting to encode unsupported type
            let spec_fake_return = mir_encoder.encode_local(fake_return_local).unwrap();
            let spec_fake_return_place: vir::Expr = if self.targets_are_values {
                self.encoder.encode_value_expr(
                    vir::Expr::local(spec_fake_return),
                    fake_return_ty
                )
            } else {
                spec_fake_return.clone().into()
            };
            replacements.push((spec_fake_return_place, target_return.clone()));
        }

        // Do the replacements
        curr_expr = curr_expr.replace_multiple_places(&replacements);

        // use the provided `self.pre_label` to encode old expressions
        curr_expr = curr_expr.map_old_expr_label(|label| {
            if label == PRECONDITION_LABEL {
                self.pre_label.to_string()
            } else {
                label.clone()
            }
        });

        debug!("MIR expr {:?} --> {}", assertion_expr.id, curr_expr);
        Ok(curr_expr.set_default_pos(
            self.encoder
                .error_manager()
                .register(
                    self.encoder.env().tcx().def_span(assertion_expr.expr),
                    ErrorCtxt::GenericExpression),
        ))
    }
}

struct StraightLineBackwardInterpreter<'p, 'v: 'p, 'tcx: 'v> {
    interpreter: PureFunctionBackwardInterpreter<'p, 'v, 'tcx>,
}

/// XXX: This encoding works backward, but there is the risk of generating expressions whose length
/// is exponential in the number of branches. If this becomes a problem, consider doing a forward
/// encoding (keeping path conditions expressions).
impl<'p, 'v: 'p, 'tcx: 'v> StraightLineBackwardInterpreter<'p, 'v, 'tcx> {
    fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        mir: &'p mir::Body<'tcx>,
        def_id: DefId,
    ) -> Self {
        StraightLineBackwardInterpreter {
            interpreter: PureFunctionBackwardInterpreter::new(
                encoder, mir, def_id, false,
            ),
        }
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> BackwardMirInterpreter<'tcx>
    for StraightLineBackwardInterpreter<'p, 'v, 'tcx>
{
    type State = MultiExprBackwardInterpreterState;
    type Error = EncodingError;

    fn apply_terminator(
        &self,
        bb: mir::BasicBlock,
        term: &mir::Terminator<'tcx>,
        states: HashMap<mir::BasicBlock, &Self::State>,
    ) -> Result<Self::State, Self::Error> {
        trace!("apply_terminator {:?}, states: {:?}", term, states);
        if !states.is_empty() && states.values().all(|state| !state.exprs().is_empty()) {
            // All states are initialized
            self.interpreter.apply_terminator(bb, term, states)
        } else {
            // One of the states is not yet initialized
            trace!("Skip terminator {:?}", term);
            Ok(MultiExprBackwardInterpreterState::new(vec![]))
        }
    }
    fn apply_statement(
        &self,
        bb: mir::BasicBlock,
        stmt_index: usize,
        stmt: &mir::Statement<'tcx>,
        state: &mut Self::State,
    ) -> Result<(), Self::Error> {
        trace!("apply_statement {:?}, state: {:?}", stmt, state);
        if !state.exprs().is_empty() {
            // The state is initialized
            self.interpreter
                .apply_statement(bb, stmt_index, stmt, state);
        } else {
            // The state is not yet initialized
            trace!("Skip statement {:?}", stmt);
        }
        Ok(())
    }
}
