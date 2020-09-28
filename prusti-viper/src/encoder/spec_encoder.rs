// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::errors::ErrorCtxt;
use crate::encoder::mir_encoder::{MirEncoder, PlaceEncoder};
use crate::encoder::mir_encoder::PRECONDITION_LABEL;
use crate::encoder::mir_interpreter::{
    run_backward_interpretation_point_to_point, BackwardMirInterpreter,
    MultiExprBackwardInterpreterState,
};
use crate::encoder::pure_function_encoder::PureFunctionBackwardInterpreter;
use crate::encoder::Encoder;
use prusti_common::vir;
use prusti_common::vir::ExprIterator;
use prusti_interface::specs::typed;
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty;
use std::collections::HashMap;
use rustc_ast::ast;
use log::{debug, trace, error};

pub fn encode_spec_assertion<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    mir: &'p mir::Body<'tcx>,
    target_label: &'p str,
    target_args: &'p [vir::Expr],
    target_return: Option<&'p vir::Expr>,
    targets_are_values: bool,
    stop_at_bbi: Option<mir::BasicBlock>,
    assertion: &typed::Assertion<'tcx>,
) -> vir::Expr {
    let spec_encoder = SpecEncoder::new(
        encoder,
        mir,
        target_label,
        target_args,
        target_return,
        targets_are_values,
        stop_at_bbi,
    );
    spec_encoder.encode_assertion(assertion)
}

struct SpecEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    // FIXME: this should be the MIR of the `__spec` function
    mir: Option<&'p mir::Body<'tcx>>,
    /// The context in which the specification should be encoded
    target_label: &'p str,
    /// The expression that encodes the arguments.
    target_args: &'p [vir::Expr],
    /// The expression that encodes `return` in a postcondition.
    target_return: Option<&'p vir::Expr>,
    /// Used to encode pure functions
    targets_are_values: bool,
    /// Used to encode loop invariants
    stop_at_bbi: Option<mir::BasicBlock>,
}

impl<'p, 'v: 'p, 'tcx: 'v> SpecEncoder<'p, 'v, 'tcx> {
    fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        mir: &'p mir::Body<'tcx>,
        target_label: &'p str,
        target_args: &'p [vir::Expr],
        target_return: Option<&'p vir::Expr>,
        targets_are_values: bool,
        stop_at_bbi: Option<mir::BasicBlock>,
    ) -> Self {
        trace!("SpecEncoder constructor");

        SpecEncoder {
            encoder,
            mir: Some(mir),
            target_label,
            target_args,
            target_return,
            targets_are_values,
            stop_at_bbi,
        }
    }

    fn new_simple(
        encoder: &'p Encoder<'v, 'tcx>,
        target_args: &'p [vir::Expr],
    ) -> Self {
        trace!("SpecEncoder simple constructor");

        SpecEncoder {
            encoder,
            mir: None,
            target_label: &"",
            target_args,
            target_return: None,
            targets_are_values: false,
            stop_at_bbi: None,
        }
    }

    fn encode_forall_arg(&self, arg: mir::Local, arg_ty: ty::Ty<'tcx>) -> vir::LocalVar {
        trace!("encode_forall_arg: {:?} {:?}", arg, arg_ty);
        assert!(
            match arg_ty.kind() {
                ty::TyKind::Int(..) | ty::TyKind::Uint(..) => true,
                _ => false,
            },
            "Quantification is only supported over integer values"
        );
        // FIXME: The name encoding is most likely wrong. (It most likely does
        // not match the names generated in other places.)
        let var_name = format!("{:?}_forall", arg);
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
    pub fn encode_assertion(&self, assertion: &typed::Assertion<'tcx>) -> vir::Expr {
        trace!("encode_assertion {:?}", assertion);
        match assertion.kind {
            box typed::AssertionKind::Expr(ref assertion_expr) => self.encode_expression(assertion_expr),
            box typed::AssertionKind::And(ref assertions) => assertions
                .iter()
                .map(|x| self.encode_assertion(x))
                .collect::<Vec<vir::Expr>>()
                .into_iter()
                .conjoin(),
            box typed::AssertionKind::Implies(ref lhs, ref rhs) => {
                vir::Expr::implies(self.encode_assertion(lhs), self.encode_assertion(rhs))
            }
            box typed::AssertionKind::TypeCond(ref vars, ref assertion) => {
                let enc = |ty: ty::Ty<'tcx>| -> vir::Expr {
                    // FIXME oh dear...
                    let ty = self.encoder.resolve_typaram(ty);
                    self.encoder.encode_tag_func_app(ty)
                };
                let typecond =
                    vir::Expr::eq_cmp(enc(vars.vars[0].1), enc(vars.vars[1].1));
                vir::Expr::implies(typecond, self.encode_assertion(assertion))
            }
            box typed::AssertionKind::ForAll(ref vars, ref trigger_set, ref body) => vir::Expr::forall(
                vars.vars.iter().map(|(arg, ty)| self.encode_forall_arg(*arg, ty)).collect(),
                trigger_set
                    .triggers()
                    .iter()
                    .map(|x| self.encode_trigger(x))
                    .collect(),
                // TODO: Replace the variables introduced in the quantifications
                self.encode_assertion(body),
            ),
        }
    }

    fn encode_expression(&self, assertion_expr: &typed::Expression) -> vir::Expr {
        debug!("encode_expression {:?}", assertion_expr);
        let tcx = self.encoder.env().tcx();

//         // Find the MIR of the first closure that encodes the assertions
//         let mut curr_node_id = assertion_expr.expr.id;
//         for _ in 0..1 {
//             curr_node_id = tcx.hir.get_parent_node(curr_node_id);
//         }
        // let mut curr_def_id = tcx.hir.local_def_id(curr_node_id);
        let mut curr_def_id = assertion_expr.expr.to_def_id();
        let mut curr_namespace = "".to_string();

        let mut encoded_expr = self.encoder.encode_pure_function_body(curr_def_id);

        // For each of the enclosing closures, replace with the variables captured in the closure.
        // We support at most 1000 nested closures (arbitrarily chosen).
        for closure_counter in 0..1000 {
            let (outer_def_id, outer_location, captured_operands, captured_operand_tys) = {
                let mut instantiations = self.encoder.get_closure_instantiations(curr_def_id);
                if instantiations.is_empty() {
                    // `curr_def_id` is not a closure and there are no captured variables
                    break;
                }
                assert_eq!(instantiations.len(), 1);
                instantiations.remove(0)
            };

            let is_last_iteration = self
                .encoder
                .get_closure_instantiations(outer_def_id)
                .is_empty();

            // XXX: This definition has been moved in the loop to avoid NLL issues
            let curr_procedure = self.encoder.env().get_procedure(curr_def_id);
            let curr_mir = curr_procedure.get_mir();
            let curr_mir_encoder = MirEncoder::new_with_namespace(
                self.encoder,
                curr_mir,
                curr_def_id,
                curr_namespace.clone(),
            );

            trace!(
                "Procedure {:?} is contained in {:?}",
                curr_def_id,
                outer_def_id
            );
            let stop_at_bbi = if format!("{:?}", outer_def_id).contains("{{closure}}") {
                // FIXME: A hack to identify if we are more than on closure inside the loop.
                // If this is a case, when stop_at_bbi makes no sense because it refers to
                // non-existant basic block.
                None
            } else {
                self.stop_at_bbi.clone()
            };
            let is_spec_function = self
                .encoder
                .get_closure_instantiations(outer_def_id)
                .is_empty();
            let outer_procedure = self.encoder.env().get_procedure(outer_def_id);
            let outer_mir = outer_procedure.get_mir();
            // HACK: don't use a namespace for the last iteration if we are encoding a loop invariant
            let outer_namespace = if self.stop_at_bbi.is_some() && is_last_iteration {
                "".to_string()
            } else {
                format!("_closure{}", closure_counter)
            };
            let outer_mir_encoder = MirEncoder::new_with_namespace(
                self.encoder,
                outer_mir,
                outer_def_id,
                outer_namespace.clone(),
            );
            trace!("Replacing variables captured from {:?}", outer_def_id);

            // Take the first local variable, that is the closure.
            // The closure is a record containing all the captured variables.
            let closure_local = curr_mir.local_decls.indices().skip(1).next().unwrap();
            // will panic if attempting to encode unsupported type
            let closure_var = curr_mir_encoder.encode_local(closure_local).unwrap();
            let closure_ty = &curr_mir.local_decls[closure_local].ty;
            let should_closure_be_dereferenced = curr_mir_encoder.can_be_dereferenced(closure_ty);
            let (deref_closure_var, deref_closure_ty) = if should_closure_be_dereferenced {
                let res = curr_mir_encoder.encode_deref(closure_var.clone().into(), closure_ty);
                (res.0, res.1)
            } else {
                (closure_var.clone().into(), *closure_ty)
            };
            trace!("closure_ty: {:?}", closure_ty);
            trace!("deref_closure_var: {:?}", deref_closure_var);
            trace!("deref_closure_ty: {:?}", deref_closure_ty);
            let closure_subst =
                if let ty::TyKind::Closure(_, ref substs) = deref_closure_ty.kind() {
                    substs.clone()
                } else {
                    unreachable!()
                };
            // let captured_tys: Vec<ty::Ty> = closure_subst.upvar_tys(curr_def_id, tcx).collect();
            // let captured_tys: Vec<ty::Ty> = closure_subst.iter().map(|arg| arg.expect_ty()).collect();
            let captured_tys = captured_operand_tys;
            trace!("captured_tys: {:?}", captured_tys);
            assert_eq!(captured_tys.len(), captured_operands.len());

            // Translate a local variable from the closure to a place in the outer MIR
            let inner_captured_places: Vec<_> = captured_tys
                .iter()
                .enumerate()
                .map(|(index, &captured_ty)| {
                    let field_name = format!("closure_{}", index);
                    let encoded_field = self.encoder.encode_raw_ref_field(field_name, captured_ty);
                    deref_closure_var.clone().field(encoded_field)
                })
                .collect();
            let outer_captured_places: Vec<_> = captured_operands
                .iter()
                .map(|operand| outer_mir_encoder.encode_operand_place(operand).unwrap())
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
            encoded_expr = encoded_expr.replace_multiple_places(
                &inner_captured_places
                    .into_iter()
                    .zip(outer_captured_places.into_iter())
                    .collect::<Vec<_>>()
            );

            // Translate an intermediate state to the state at the beginning of the method
            let state = MultiExprBackwardInterpreterState::new_single(encoded_expr.clone());
            let interpreter = StraightLineBackwardInterpreter::new(
                self.encoder,
                outer_mir,
                outer_def_id,
                outer_namespace.clone(),
            );
            let initial_state = run_backward_interpretation_point_to_point(
                outer_mir,
                &interpreter,
                stop_at_bbi.unwrap_or(mir::START_BLOCK),
                outer_location.block,
                outer_location.statement_index,
                state,
                MultiExprBackwardInterpreterState::new(vec![]),
            )
            .unwrap();
            encoded_expr = initial_state.into_expressions().remove(0);

            // Replace the variables introduced in the quantifications
            if !is_spec_function {
                // let mut var_names = HashMap::new();
                // for info in &outer_mir.var_debug_info {
                //     if let Some(local) = info.place.as_local() {
                //         var_names.insert(local, info.name);
                //     } else {
                //         unimplemented!();
                //     }
                // }
                for local_arg_index in outer_mir.args_iter().skip(1) {
                    // if let Some(var_name) = var_names.get(&local_arg_index) {
                    let local_arg = &outer_mir.local_decls[local_arg_index];
                    if !local_arg.internal {
                        let var_name = format!("{:?}_forall", local_arg_index);
                        let encoded_arg = outer_mir_encoder.encode_local(local_arg_index).unwrap();
                        let value_field = self.encoder.encode_value_field(local_arg.ty);
                        let value_type = self.encoder.encode_value_type(local_arg.ty);
                        let proper_var = vir::LocalVar::new(var_name, value_type);
                        let encoded_arg_value = vir::Expr::local(encoded_arg).field(value_field);
                        trace!(
                            "Place {}: {} is renamed to {} because a quantifier introduced it",
                            encoded_arg_value,
                            encoded_arg_value.get_type(),
                            proper_var
                        );
                        encoded_expr =
                            encoded_expr.replace_place(&encoded_arg_value, &proper_var.into());
                    }
                }
            }

            trace!(
                "Expr at the beginning of closure with namespace '{}': {}",
                outer_namespace,
                encoded_expr
            );

            // Outer is the new curr
            curr_namespace = outer_namespace;
            curr_def_id = outer_def_id;
        }

        // XXX: This definition has been copied after the loop to avoid NLL issues
        let curr_procedure = self.encoder.env().get_procedure(curr_def_id);
        let curr_mir = curr_procedure.get_mir();
        let curr_mir_encoder = MirEncoder::new_with_namespace(
            self.encoder,
            curr_mir,
            curr_def_id,
            curr_namespace.clone(),
        );

        if self.stop_at_bbi.is_none() {
            // At this point, `curr_def_id` corresponds to the SPEC method. Here is a simple check.
            let item_name = self
                .encoder
                .encode_item_name(curr_def_id);
            if !tcx.is_closure(curr_def_id) {
                assert!(item_name.contains("prusti_pre_item_") ||
                        item_name.contains("prusti_post_item_"), "item_name: {}", item_name);
            } else {
                trace!("curr_def_id refers to closure: {:?}", curr_def_id);
                // TODO (?): check that tcx.get_attrs(curr_def_id) includes
                //           prusti::spec_only and prusti::spec_id
            }
        }

        // Translate arguments and return from the SPEC to the TARGET context
        if self.stop_at_bbi.is_none() {
            // FIXME
            //assert_eq!(curr_mir.args_iter().count(), self.target_args.len() + 1);
        } else {
            assert_eq!(curr_mir.args_iter().count(), self.target_args.len());
        }
        trace!("curr_mir args: {:?} {:?}, target_args: {:?}",
               curr_mir.args_iter().collect::<Vec<_>>(),
               curr_mir.args_iter().map(|arg| &curr_mir.local_decls[arg]).collect::<Vec<_>>(),
               self.target_args);
        for (local, target_arg) in curr_mir.args_iter().zip(self.target_args) {
            let local_ty = curr_mir.local_decls[local].ty;
            // will panic if attempting to encode unsupported type
            let spec_local = curr_mir_encoder.encode_local(local).unwrap();
            let spec_local_place: vir::Expr = if self.targets_are_values {
                self.encoder.encode_value_expr(vir::Expr::local(spec_local), local_ty)
            } else {
                spec_local.into()
            };

            encoded_expr = encoded_expr.replace_place(&spec_local_place, target_arg);
        }
        if let Some(target_return) = self.target_return {
            let fake_return_local = curr_mir.args_iter().last().unwrap();
            let fake_return_ty = curr_mir.local_decls[fake_return_local].ty;
            // will panic if attempting to encode unsupported type
            let spec_fake_return = curr_mir_encoder.encode_local(fake_return_local).unwrap();

            /*match self.target_return_value {
                Some(target_return_value) => {
                    match curr_mir.return_ty().sty {
                        ty::TyKind::Bool |
                        ty::TyKind::Int(..) |
                        ty::TyKind::Uint(..) |
                        ty::TyKind::RawPtr(..) |
                        ty::TyKind::Ref(..) => {
                            let value_field = self.encoder.encode_value_field(curr_mir.return_ty());
                            let spec_fake_return_value = vir::Expr::Local(spec_fake_return.clone()).field(value_field);
                            encoded_expr = encoded_expr.replace_place(&spec_fake_return_value, target_return_value);
                        }
                        _ => {}
                    }
                }
                None => {}
            }*/

            let spec_fake_return_place: vir::Expr = if self.targets_are_values {
                self.encoder.encode_value_expr(
                    vir::Expr::local(spec_fake_return),
                    fake_return_ty
                )
            } else {
                spec_fake_return.clone().into()
            };

            debug!("spec_fake_return_place: {}", spec_fake_return_place);
            debug!("target_return: {}", target_return);
            encoded_expr = encoded_expr.replace_place(&spec_fake_return_place, target_return);
        }

        // Translate label of `old[pre]` expressions to the TARGET label
        encoded_expr = encoded_expr.map_old_expr_label(|label| {
            if label == PRECONDITION_LABEL {
                self.target_label.to_string()
            } else {
                label.clone()
            }
        });

        debug!("MIR expr {:?} --> {}", assertion_expr.id, encoded_expr);
        encoded_expr.set_default_pos(
            self.encoder
                .error_manager()
                .register(
                    self.encoder.env().tcx().def_span(assertion_expr.expr),
                    ErrorCtxt::GenericExpression),
        )
    }

    /// Translate an expression from a closure identified by `def_id` to its definition site.
    /// The `expr` parameter is the expression encoded using the closure's arguments and captured
    /// state.
    ///
    /// The result is a tuple with:
    /// * the translated expression,
    /// * the def_id of the item in which the closure was defined,
    /// * the location at which the closure was defined.
    fn translate_expr_to_closure_def_site(
        &self,
        expr: vir::Expr,
        def_id: DefId,
    ) -> (vir::Expr, DefId, mir::Location) {
        debug!("translate_expr_to_closure_def_site {} {:?}", expr, def_id);
        let inner_mir = self.encoder.env().mir(def_id.expect_local());
        let inner_mir_encoder = MirEncoder::new(self.encoder, &inner_mir, def_id);

        let opt_instantiation = self.encoder.get_single_closure_instantiation(def_id);
        let (
            outer_def_id,
            outer_location,
            captured_operands,
            captured_operand_tys,
        ) = opt_instantiation.expect(
            &format!("cannot find definition site for closure {:?}", def_id)
        );
        let outer_mir = self.encoder.env().mir(outer_def_id.expect_local());
        let outer_mir_encoder = MirEncoder::new(self.encoder, &outer_mir, outer_def_id);
        trace!("Replacing variables of {:?} captured from {:?}", def_id, outer_def_id);

        // Take the first local variable, that is the closure.
        // The closure is a record containing all the captured variables.
        let closure_local = inner_mir.local_decls.indices().skip(1).next().unwrap();
        // will panic if attempting to encode unsupported type
        let closure_var = inner_mir_encoder.encode_local(closure_local).unwrap();
        let closure_ty = &inner_mir.local_decls[closure_local].ty;
        let should_closure_be_dereferenced = inner_mir_encoder.can_be_dereferenced(closure_ty);
        let (deref_closure_var, deref_closure_ty) = if should_closure_be_dereferenced {
            let res = inner_mir_encoder.encode_deref(closure_var.clone().into(), closure_ty);
            (res.0, res.1)
        } else {
            (closure_var.clone().into(), *closure_ty)
        };
        trace!("closure_ty: {:?}", closure_ty);
        trace!("deref_closure_var: {:?}", deref_closure_var);
        trace!("deref_closure_ty: {:?}", deref_closure_ty);
        let closure_subst =
            if let ty::TyKind::Closure(_, ref substs) = deref_closure_ty.kind() {
                substs.clone()
            } else {
                unreachable!()
            };

        let captured_tys = captured_operand_tys;
        trace!("captured_tys: {:?}", captured_tys);
        assert_eq!(captured_tys.len(), captured_operands.len());

        // Translate a local variable from the closure to a place in the outer MIR
        let inner_captured_places: Vec<_> = captured_tys
            .iter()
            .enumerate()
            .map(|(index, &captured_ty)| {
                let field_name = format!("closure_{}", index);
                let encoded_field = self.encoder.encode_raw_ref_field(field_name, captured_ty);
                deref_closure_var.clone().field(encoded_field)
            })
            .collect();
        let outer_captured_places: Vec<_> = captured_operands
            .iter()
            .map(|operand| outer_mir_encoder.encode_operand_place(operand).unwrap())
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
        let outer_expr = expr.replace_multiple_places(
            &inner_captured_places
                .into_iter()
                .zip(outer_captured_places.into_iter())
                .collect::<Vec<_>>()
        );

        debug!(
            "Expr at the definition site ({:?} {:?}): {}",
            outer_def_id,
            outer_location,
            outer_expr
        );
        (outer_expr, outer_def_id, outer_location)
    }

    /// Given an expression and a program point, return the equivalent expression at a
    /// precedent program point.
    fn translate_expr_to_state(
        &self,
        expr: vir::Expr,
        def_id: DefId,
        expr_location: mir::Location,
        target_location: mir::BasicBlock,
    ) -> vir::Expr {
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
            "".to_string(),
        );
        let initial_state = run_backward_interpretation_point_to_point(
            &mir,
            &interpreter,
            target_location,
            expr_location.block,
            expr_location.statement_index,
            state,
            MultiExprBackwardInterpreterState::new(vec![]),
        ).expect(
            &format!("cannot encode {:?} because its CFG contains a loop", def_id)
        );
        let pre_state_expr = initial_state.into_expressions().remove(0);

        trace!("Expr at the beginning: {}", pre_state_expr);
        pre_state_expr
    }

    /// Encode the assertion of a contract or of a loop invariant to a VIR expression.
    fn new_encode_expression(&self, assertion_expr: &typed::Expression) -> vir::Expr {
        debug!("encode_expression {:?}", assertion_expr);

        let mut curr_def_id = assertion_expr.expr.to_def_id();
        let mut curr_expr = self.encoder.encode_pure_function_body(curr_def_id);

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
            ) = self.translate_expr_to_closure_def_site(curr_expr, curr_def_id);
            let done = self.encoder.get_single_closure_instantiation(outer_def_id).is_none();
            curr_expr = self.translate_expr_to_state(
                outer_expr,
                outer_def_id,
                outer_location,
                if done {
                    self.stop_at_bbi.unwrap_or(mir::START_BLOCK)
                } else {
                    mir::START_BLOCK
                },
            );
            curr_def_id = outer_def_id;
        }

        // At this point `curr_def_id` should be either a SPEC item (when encoding a contract) or
        // the method being verified (when encoding a loop invariant).
        let mir = self.encoder.env().mir(curr_def_id.expect_local());
        let mir_encoder = MirEncoder::new(self.encoder, &mir, curr_def_id);

        // `curr_expr` is an expression that can be evaluated in `curr_def_id`, but it contains
        // arguments encoded with e.g. a `.val_int` final field, which is not what we want if we
        // are encoding a pure function. So, if needed we replace them.
        if !self.targets_are_values {
            let replacements: Vec<_> = mir.args_iter().map(|local| {
                let local_ty = mir.local_decls[local].ty;
                // will panic if attempting to encode unsupported type
                let spec_local = mir_encoder.encode_local(local).unwrap();
                let spec_local_place: vir::Expr = self.encoder.encode_value_expr(
                    vir::Expr::local(spec_local.clone()),
                    local_ty
                );
                (spec_local_place, spec_local.into())
            }).collect();
            curr_expr = curr_expr.replace_multiple_places(&replacements);
        }

        // Replace the fake return variable (last argument) of SPEC items with a given expression
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
            curr_expr = curr_expr.replace_place(&spec_fake_return_place, target_return);
        }

        debug!("MIR expr {:?} --> {}", assertion_expr.id, curr_expr);
        curr_expr.set_default_pos(
            self.encoder
                .error_manager()
                .register(
                    self.encoder.env().tcx().def_span(assertion_expr.expr),
                    ErrorCtxt::GenericExpression),
        )
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
        namespace: String,
    ) -> Self {
        StraightLineBackwardInterpreter {
            interpreter: PureFunctionBackwardInterpreter::new(
                encoder, mir, def_id, namespace, false,
            ),
        }
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> BackwardMirInterpreter<'tcx>
    for StraightLineBackwardInterpreter<'p, 'v, 'tcx>
{
    type State = MultiExprBackwardInterpreterState;
    fn apply_terminator(
        &self,
        bb: mir::BasicBlock,
        term: &mir::Terminator<'tcx>,
        states: HashMap<mir::BasicBlock, &Self::State>,
    ) -> Self::State {
        trace!("apply_terminator {:?}, states: {:?}", term, states);
        if !states.is_empty() && states.values().all(|state| !state.exprs().is_empty()) {
            // All states are initialized
            self.interpreter.apply_terminator(bb, term, states)
        } else {
            // One of the states is not yet initialized
            trace!("Skip terminator {:?}", term);
            MultiExprBackwardInterpreterState::new(vec![])
        }
    }
    fn apply_statement(
        &self,
        bb: mir::BasicBlock,
        stmt_index: usize,
        stmt: &mir::Statement<'tcx>,
        state: &mut Self::State,
    ) {
        trace!("apply_statement {:?}, state: {:?}", stmt, state);
        if !state.exprs().is_empty() {
            // The state is initialized
            self.interpreter
                .apply_statement(bb, stmt_index, stmt, state);
        } else {
            // The state is not yet initialized
            trace!("Skip statement {:?}", stmt);
        }
    }
}
