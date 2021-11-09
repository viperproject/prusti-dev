use crate::encoder::{
    encoder::SubstMap,
    errors::{
        EncodingError, EncodingResult, ErrorCtxt, SpannedEncodingError, SpannedEncodingResult,
        WithSpan,
    },
    high::{pure_functions::HighPureFunctionEncoderInterface, types::HighTypeEncoderInterface},
    mir::{
        generics::GenericsEncoderInterface,
        places::PlacesEncoderInterface,
        pure::{
            interpreter::{state::ExprBackwardInterpreterState, ExpressionBackwardInterpreter},
            PureFunctionEncoderInterface,
        },
        types::MirTypeEncoderInterface,
    },
    mir_encoder::{MirEncoder, PlaceEncoder, PlaceEncoding, PRECONDITION_LABEL},
    mir_interpreter::{run_backward_interpretation_point_to_point, BackwardMirInterpreter},
    Encoder, SpecFunctionKind,
};
use log::{debug, trace};
use prusti_common::config;
use prusti_interface::{specs::typed, utils::read_prusti_attr};
use rustc_ast::ast;
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty};
use std::collections::HashMap;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, ExpressionIterator, QuantifierHelpers},
    high::{self as vir_high, operations::ty::Typed, Generic},
    polymorphic::ExprIterator,
};

pub(super) struct SpecificationEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    /// The label to encode `old(..)` expressions
    pre_label: &'p str,
    /// The expression that encodes the arguments.
    target_args: &'p [vir_high::Expression],
    /// The expression that encodes `return` in a postcondition.
    target_return: Option<&'p vir_high::Expression>,
    /// Location at which to encode loop invariants.
    assertion_location: Option<mir::BasicBlock>,
    /// When registering errors, this gives us their
    /// associated function
    parent_def_id: DefId,
    tymap: &'p SubstMap<'tcx>,
}

impl<'p, 'v: 'p, 'tcx: 'v> SpecificationEncoder<'p, 'v, 'tcx> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        pre_label: &'p str,
        target_args: &'p [vir_high::Expression],
        target_return: Option<&'p vir_high::Expression>,
        assertion_location: Option<mir::BasicBlock>,
        parent_def_id: DefId,
        tymap: &'p SubstMap<'tcx>,
    ) -> Self {
        trace!("SpecEncoder constructor");

        Self {
            encoder,
            pre_label,
            target_args,
            target_return,
            assertion_location,
            parent_def_id,
            tymap,
        }
    }

    /// Encode a quantified variable `arg`, given its type `arg_ty` and a unique identifier
    /// `quant_id` of the quantification.
    fn encode_quantifier_arg(
        &self,
        arg: mir::Local,
        arg_ty: ty::Ty<'tcx>,
        quant_id: &str,
    ) -> EncodingResult<vir_high::VariableDecl> {
        trace!(
            "encode_quantifier_arg: {:?} {:?} {:?}",
            arg,
            arg_ty,
            quant_id
        );
        let ty = self.encoder.encode_type_high(arg_ty)?;
        // FIXME: find a reasonable position when using this function below,
        // change return to EncodingResult<...>, then unwrap with ?
        let var_name = format!("{:?}_quant_{}", arg, quant_id);
        Ok(vir_high::VariableDecl::new(var_name, ty))
    }

    fn encode_trigger(
        &self,
        trigger: &typed::Trigger,
        bounded_vars: &[vir_high::VariableDecl],
    ) -> SpannedEncodingResult<vir_high::Trigger> {
        trace!("encode_trigger {:?}", trigger);
        struct TriggerChecker {
            span: rustc_span::MultiSpan,
            error: Option<SpannedEncodingError>,
        }
        impl vir_high::visitors::ExpressionWalker for TriggerChecker {
            fn walk_expression(&mut self, expression: &vir_high::Expression) {
                match expression {
                    vir_high::Expression::Local(..)
                    | vir_high::Expression::Constant(..)
                    | vir_high::Expression::FuncApp(..) => {
                        // Legal triggers.
                    }
                    _ => {
                        // Everything else is illegal in triggers.
                        let msg = "Only function calls are allowed in triggers.";
                        // TODO: We should use a more precise span.
                        self.error = Some(SpannedEncodingError::incorrect(msg, self.span.clone()));
                    }
                }
                if self.error.is_none() {
                    vir_high::visitors::default_walk_expression(self, expression);
                }
            }
        }
        let bounded_vars: Vec<_> = bounded_vars.iter().map(|var| var.clone().into()).collect();
        let mut found_bounded_vars = std::collections::HashSet::new();
        let mut encoded_expressions = Vec::new();
        for term in trigger.terms() {
            let encoded_expr = self.encode_expression(term)?;
            let mut checker = TriggerChecker {
                error: None,
                span: self.encoder.env().tcx().def_span(term.expr).into(),
            };
            vir_high::visitors::ExpressionWalker::walk_expression(&mut checker, &encoded_expr);
            if let Some(error) = checker.error {
                return Err(error);
            }
            for var in &bounded_vars {
                if encoded_expr.find(var) {
                    found_bounded_vars.insert(var);
                }
            }
            encoded_expressions.push(encoded_expr);
        }
        for var in &bounded_vars {
            if !found_bounded_vars.contains(var) {
                debug!("bounded_vars: {:?}", bounded_vars);
                debug!("encoded_expressions: {:?}", encoded_expressions);
                debug!("found_bounded_vars: {:?}", found_bounded_vars);
                debug!("var: {:?}", var);
                // FIXME: We should mention the missing variable in the error message.
                let msg = "a trigger must mention all bounded variables.";
                let span = rustc_span::MultiSpan::from_spans(
                    trigger
                        .terms()
                        .iter()
                        .map(|term| self.encoder.env().tcx().def_span(term.expr))
                        .collect(),
                );
                return Err(SpannedEncodingError::incorrect(msg, span));
            }
        }
        Ok(vir_high::Trigger::new(encoded_expressions))
    }

    /// Encode a specification item as a single expression.
    pub(super) fn encode_assertion(
        &self,
        assertion: &typed::Assertion<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        trace!("encode_assertion {:?}", assertion);
        Ok(match assertion.kind {
            box typed::AssertionKind::Expr(ref assertion_expr) => {
                self.encode_expression(assertion_expr)?
            }
            box typed::AssertionKind::And(ref assertions) => assertions
                .iter()
                .map(|x| self.encode_assertion(x))
                .collect::<Result<Vec<vir_high::Expression>, _>>()?
                .into_iter()
                .conjoin(),
            box typed::AssertionKind::Implies(ref lhs, ref rhs) => vir_high::Expression::implies(
                self.encode_assertion(lhs)?,
                self.encode_assertion(rhs)?,
            ),
            box typed::AssertionKind::TypeCond(ref _vars, ref _assertion) => {
                unimplemented!();
                // let enc = |ty: ty::Ty<'tcx>| -> vir_high::Expression {
                //     // FIXME: this is a hack to support generics. See issue #187.
                //     // TODO polymorphic: might remove this step
                //     let ty = self.encoder.resolve_typaram(ty, self.tymap);
                //     self.encoder.encode_tag_func_app(ty)
                // };
                // let typecond =
                //     vir_high::Expression::eq_cmp(enc(vars.vars[0].1), enc(vars.vars[1].1));
                // vir_high::Expression::implies(
                //     typecond,
                //     self.encode_assertion(assertion)?
                // )
            }
            box typed::AssertionKind::ForAll(ref vars, ref trigger_set, ref body) => {
                self.encode_quantifier(vars, trigger_set, body, false)?
            }
            box typed::AssertionKind::Exists(ref vars, ref trigger_set, ref body) => {
                self.encode_quantifier(vars, trigger_set, body, true)?
            }
            box typed::AssertionKind::SpecEntailment {
                ref closure,
                arg_binders: ref vars,
                ref pres,
                ref posts,
            } => {
                // TODO: refactor, simplify, or extract into a function
                let tcx = self.encoder.env().tcx();
                let mir = self.encoder.env().local_mir(closure.expr);
                let result = &mir.local_decls[0_u32.into()];
                let ty = result.ty;
                if let Some(ty_repl) = self.tymap.get(ty) {
                    debug!("spec ent repl: {:?} -> {:?}", ty, ty_repl);

                    match ty_repl.kind() {
                        ty::TyKind::Closure(def_id, _substs)
                        | ty::TyKind::FnDef(def_id, _substs) => {
                            let encoded_pres = pres
                                .iter()
                                .map(|x| self.encode_assertion(x))
                                .collect::<Result<Vec<vir_high::Expression>, _>>()?
                                .into_iter()
                                .conjoin();

                            // encode_quantifier_arg() above only works for integers.
                            // Therefore, for the time being, check that we're working with integers:
                            vars.args.iter().for_each(|(_arg, arg_ty)| {
                                match arg_ty.kind() {
                                    ty::TyKind::Int(..) | ty::TyKind::Uint(..) => {}
                                    _ => { unimplemented!("Only integers are currently supported as closure arguments."); }
                                }
                            });
                            match vars.result.1.kind() {
                                ty::TyKind::Int(..) | ty::TyKind::Uint(..) => {}
                                _ => {
                                    unimplemented!("Only integers are currently supported as closure return types.");
                                }
                            }

                            let sf_pre_name = self
                                .encoder
                                .encode_spec_func_name(*def_id, SpecFunctionKind::Pre);
                            let qvars_pre = {
                                let mut qvars_pre = Vec::new();
                                for (arg, arg_ty) in &vars.args {
                                    let span = self.encoder.get_local_span(&*mir, *arg)?;
                                    qvars_pre.push(
                                        self.encode_quantifier_arg(
                                            *arg,
                                            arg_ty,
                                            &format!("{}_{}", vars.spec_id, vars.pre_id),
                                        )
                                        .with_span(span)?,
                                    );
                                }
                                qvars_pre
                            };
                            let pre_conjunct = vir_high::Expression::forall(
                                qvars_pre.clone(),
                                vec![], // TODO: encode triggers
                                vir_high::Expression::implies(
                                    encoded_pres.clone(),
                                    vir_high::Expression::function_call(
                                        sf_pre_name,
                                        qvars_pre
                                            .iter()
                                            .map(|x| vir_high::Expression::local_no_pos(x.clone()))
                                            .collect(),
                                        vir_high::Type::Bool,
                                    ),
                                ),
                            );

                            let sf_post_name = self
                                .encoder
                                .encode_spec_func_name(*def_id, SpecFunctionKind::Post);

                            // The result is modeled as the final argument to the post() spec function
                            let result_var = mir::Local::from_usize(vars.args.len() + 2);

                            // The set of quantified variables
                            let mut qvars_post = Vec::new();
                            for (arg, arg_ty) in &vars.args {
                                let span = self.encoder.get_local_span(&*mir, *arg)?;
                                qvars_post.push(
                                    self.encode_quantifier_arg(
                                        *arg,
                                        arg_ty,
                                        &format!("{}_{}", vars.spec_id, vars.post_id),
                                    )
                                    .with_span(span)?,
                                );
                            }
                            let result_span = self.encoder.get_local_span(&*mir, result_var)?;
                            qvars_post.push(
                                self.encode_quantifier_arg(
                                    result_var,
                                    tcx.mk_ty(ty::TyKind::Int(ty::IntTy::I32)),
                                    &format!("{}_{}", vars.spec_id, vars.post_id),
                                )
                                .with_span(result_span)?,
                            );
                            let arguments = qvars_post
                                .iter()
                                .map(|x| vir_high::Expression::local_no_pos(x.clone()))
                                .collect();

                            // The quantified variables in the precondition have been encoded using
                            // different IDs (vars.pre_id vs. vars.post_id), so we need to fix them
                            let impl_lhs = (0..qvars_pre.len()).fold(encoded_pres, |e, i| {
                                e.replace_place(
                                    &vir_high::Expression::local_no_pos(qvars_pre[i].clone()),
                                    &vir_high::Expression::local_no_pos(qvars_post[i].clone()),
                                )
                            });

                            let post_conjunct = vir_high::Expression::forall(
                                qvars_post,
                                vec![], // TODO: encode triggers
                                vir_high::Expression::implies(
                                    impl_lhs,
                                    vir_high::Expression::implies(
                                        vir_high::Expression::function_call(
                                            sf_post_name,
                                            arguments,
                                            vir_high::Type::Bool,
                                        ),
                                        posts
                                            .iter()
                                            .map(|x| self.encode_assertion(x))
                                            .collect::<Result<Vec<vir_high::Expression>, _>>()?
                                            .into_iter()
                                            .conjoin(),
                                    ),
                                ),
                            );

                            vec![pre_conjunct, post_conjunct].into_iter().conjoin()
                        }
                        _ => unreachable!(),
                    }
                } else {
                    // TODO
                    true.into()
                }
            }
        })
    }

    /// Encode a universal or existential quantifer. Encodes type bounds of
    /// quantified variables as:
    /// * premises in a universal quantifier, or
    /// * conjuncts in an existential quantifier.
    fn encode_quantifier(
        &self,
        vars: &typed::QuantifierVars<'tcx>,
        trigger_set: &typed::TriggerSet,
        body: &typed::Assertion<'tcx>,
        exists: bool,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let mut encoded_args = vec![];
        // FIXME: the type bounds should be part of the type invariant.
        let mut bounds = vec![];
        for (arg, ty) in &vars.vars {
            // TODO: how to get a span for the variable here?
            //if !self.encoder.is_quantifiable(ty).unwrap() {
            //    return Err(EncodingError::incorrect(
            //        "This type cannot be used in quantifiers.",
            //    ).with_span(?));
            //}

            // FIXME: figure out from where to get the span and replace “unwrap” with ?
            let encoded_arg = self
                .encode_quantifier_arg(*arg, ty, &format!("{}_{}", vars.spec_id, vars.id))
                .unwrap();
            if config::check_overflows() {
                debug_assert!(self.encoder.env().type_is_copy(ty));
                // FIXME: the type bounds should be part of the type invariant.
                if let Some((lower_bound, upper_bound)) = self.encoder.get_integer_type_bounds(ty) {
                    bounds.push(vir_high::Expression::less_equals(
                        lower_bound,
                        encoded_arg.clone().into(),
                    ));
                    bounds.push(vir_high::Expression::less_equals(
                        encoded_arg.clone().into(),
                        upper_bound,
                    ));
                }
            } else if config::encode_unsigned_num_constraint() {
                if let ty::TyKind::Uint(_) = ty.kind() {
                    let expr =
                        vir_high::Expression::less_equals(0u8.into(), encoded_arg.clone().into());
                    bounds.push(expr);
                }
            }
            encoded_args.push(encoded_arg);
        }
        let mut encoded_triggers = Vec::new();
        for trigger in trigger_set.triggers() {
            let encoded_trigger = self.encode_trigger(trigger, &encoded_args)?;
            encoded_triggers.push(encoded_trigger);
        }
        let encoded_body = self.encode_assertion(body)?;
        let final_body = if bounds.is_empty() {
            encoded_body
        } else if exists {
            vir_high::Expression::and(bounds.into_iter().conjoin(), encoded_body)
        } else {
            vir_high::Expression::implies(bounds.into_iter().conjoin(), encoded_body)
        };
        if exists {
            Ok(vir_high::Expression::exists(
                encoded_args,
                encoded_triggers,
                final_body,
            ))
        } else {
            Ok(vir_high::Expression::forall(
                encoded_args,
                encoded_triggers,
                final_body,
            ))
        }
    }

    /// Translate an expression `expr` from a closure identified by `def_id` to its definition site.
    ///
    /// During the translation:
    /// * Usages of the closure's captured state will be translated to the captured place.
    /// * Closure arguments will be treated as quantified variables and will be translated using
    ///   the `self.encode_quantifier_arg(..)` method.
    ///
    /// The result is a tuple with:
    /// * the translated expression,
    /// * the def_id of the item in which the closure was defined,
    /// * the location at which the closure was defined.
    fn translate_expr_to_closure_def_site(
        &self,
        expr: vir_high::Expression,
        inner_def_id: DefId,
    ) -> SpannedEncodingResult<(vir_high::Expression, DefId, mir::Location)> {
        debug!(
            "translate_expr_to_closure_def_site {} {:?}",
            expr, inner_def_id
        );
        let inner_mir = self.encoder.env().local_mir(inner_def_id.expect_local());
        let inner_attrs = self.encoder.env().tcx().get_attrs(inner_def_id);

        let opt_instantiation = self.encoder.get_single_closure_instantiation(inner_def_id);
        let (outer_def_id, outer_location, captured_operands, captured_operand_tys) =
            opt_instantiation.unwrap_or_else(|| {
                panic!("cannot find definition site for closure {:?}", inner_def_id)
            });
        let outer_mir = self.encoder.env().local_mir(outer_def_id.expect_local());
        let outer_mir_encoder = MirEncoder::new(self.encoder, &outer_mir, outer_def_id);
        let outer_span = outer_mir_encoder.get_span_of_location(outer_location);
        trace!(
            "Replacing variables of {:?} captured from {:?}",
            inner_def_id,
            outer_def_id
        );

        // Take the first argument, which is the closure's captured state.
        // The closure is a record containing all the captured variables.
        let closure_local = inner_mir.args_iter().next().unwrap();
        let closure_var = self.encoder.encode_local_high(&inner_mir, closure_local)?;
        let closure_ty = &inner_mir.local_decls[closure_local].ty;
        let deref_closure_var: vir_high::Expression = closure_var.into();
        trace!("closure_ty: {:?}", closure_ty);
        trace!("deref_closure_var: {:?}", deref_closure_var);

        let captured_tys = captured_operand_tys;
        trace!("captured_tys: {:?}", captured_tys);
        assert_eq!(captured_tys.len(), captured_operands.len());

        // Replacements to translate from the closure to the definition site
        let mut replacements: Vec<(vir_high::Expression, vir_high::Expression)> = vec![];

        // Replacement 1: translate a local variable from the closure to a place in the outer MIR
        let substs = &self
            .encoder
            .encode_substitution_map_high(self.tymap)
            .with_span(outer_span)?;
        let inner_captured_places: Vec<vir_high::Expression> = captured_tys
            .iter()
            .enumerate()
            .map(|(index, &captured_ty)| {
                let field_name = format!("closure_{}", index);
                self.encoder
                    .encode_type_high(captured_ty)
                    .with_span(outer_span)
                    .map(|ty| {
                        let field_decl = vir_high::FieldDecl::new(field_name, ty);
                        let place = vir_high::Expression::field_no_pos(
                            deref_closure_var.clone(),
                            field_decl,
                        );
                        place.substitute_types(substs)
                    })
            })
            .collect::<Result<_, _>>()?;
        let outer_captured_places: Vec<_> = captured_operands
            .iter()
            .map(
                |operand| self.encoder.encode_operand_place_high(&*outer_mir, operand), // outer_mir_encoder.encode_operand_place(operand)
            )
            .collect::<Result<Vec<_>, _>>()
            .with_span(outer_span)?
            .into_iter()
            .map(|x| x.unwrap().substitute_types(substs))
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
                .zip(outer_captured_places.into_iter()),
        );

        // Replacement 2: rename the variables introduced by a quantification
        let opt_forall_id = read_prusti_attr("expr_id", inner_attrs);
        if let Some(forall_id) = opt_forall_id {
            // Skip the first argument, which is the captured state
            for local_arg_index in inner_mir.args_iter().skip(1) {
                let local_arg = &inner_mir.local_decls[local_arg_index];
                assert!(!local_arg.internal);
                let quantified_var = self
                    .encode_quantifier_arg(local_arg_index, local_arg.ty, &forall_id)
                    .with_span(outer_span)?;
                let encoded_arg = self
                    .encoder
                    .encode_local_high(&*inner_mir, local_arg_index)?;
                let encoded_arg_value = match local_arg.ty.kind() {
                    ty::TyKind::Uint(_)
                    | ty::TyKind::Int(_)
                    | ty::TyKind::Bool
                    | ty::TyKind::Char => {
                        let span = self.encoder.get_local_span(&*inner_mir, local_arg_index)?;
                        let value_field = self
                            .encoder
                            .encode_value_field_high(local_arg.ty)
                            .with_span(span)?;
                        vir_high::Expression::field_no_pos(
                            vir_high::Expression::local_no_pos(encoded_arg),
                            value_field,
                        )
                    }
                    _ => encoded_arg.into(),
                };
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
            outer_def_id, outer_location, outer_expr
        );
        Ok((outer_expr, outer_def_id, outer_location))
    }

    /// Given an expression and a program point, return the equivalent expression at a
    /// precedent program point.
    fn translate_expr_to_state(
        &self,
        expr: vir_high::Expression,
        def_id: DefId,
        expr_location: mir::Location,
        target_location: mir::BasicBlock,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        debug!(
            "translate_expr_to_state {} {:?} {:?}",
            expr, def_id, expr_location
        );
        let mir = self.encoder.env().local_mir(def_id.expect_local());
        let span = self.encoder.env().get_def_span(def_id);

        // Translate an intermediate state to the state at the beginning of the method
        let substs = self
            .encoder
            .encode_substitution_map_high(self.tymap)
            .with_span(span)?;
        let state = ExprBackwardInterpreterState::new_defined_with_substs(expr, substs);
        let interpreter = StraightLineBackwardInterpreter::new(
            self.encoder,
            &mir,
            def_id,
            self.parent_def_id,
            self.tymap,
        );
        let initial_state = run_backward_interpretation_point_to_point(
            &mir,
            &interpreter,
            target_location,
            expr_location.block,
            expr_location.statement_index,
            state,
            ExprBackwardInterpreterState::new_undefined(),
        )?
        .ok_or_else(|| {
            SpannedEncodingError::internal(
                format!("cannot encode {:?} because its CFG contains a loop", def_id),
                span,
            )
        })?;
        let pre_state_expr = initial_state.into_expr().ok_or_else(|| {
            SpannedEncodingError::internal("interpretation produced no expression", span)
        })?;

        trace!("Expr at the beginning: {}", pre_state_expr);
        Ok(pre_state_expr)
    }

    /// Encode the assertion of a contract or loop invariant.
    fn encode_expression(
        &self,
        assertion_expr: &typed::Expression,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        debug!("encode_expression {:?}", assertion_expr);

        let mut curr_def_id = assertion_expr.expr.to_def_id();
        let mut curr_expr = self.encoder.encode_pure_expression_high(
            curr_def_id,
            self.parent_def_id,
            self.tymap,
        )?;

        loop {
            let done = self
                .encoder
                .get_single_closure_instantiation(curr_def_id)
                .is_none();
            if done {
                debug!(
                    "end of encode_expression loop: {:?} has no instantiation",
                    curr_def_id
                );
                break;
            }
            let (outer_expr, outer_def_id, outer_location) =
                self.translate_expr_to_closure_def_site(curr_expr, curr_def_id)?;
            let done = self
                .encoder
                .get_single_closure_instantiation(outer_def_id)
                .is_none();
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

        // FIXME: "self" is skipped for closures, see TypeEncoder
        let skip_first = self
            .encoder
            .encode_item_name(curr_def_id)
            .contains("_closure_");

        // At this point `curr_def_id` should be either a SPEC item (when encoding a contract) or
        // the method being verified (when encoding a loop invariant).
        let mir = self.encoder.env().local_mir(curr_def_id.expect_local());

        // Replacements to use the provided `target_args` and `target_return`
        let mut replacements: Vec<(vir_high::Expression, vir_high::Expression)> = vec![];
        let span = self
            .encoder
            .env()
            .get_def_span(assertion_expr.expr.to_def_id());
        let substs = &self
            .encoder
            .encode_substitution_map_high(self.tymap)
            .with_span(span)?;

        // Replacement 1: replace the arguments with the `target_args`.
        replacements.extend(
            mir.args_iter()
                .zip(self.target_args.iter().skip(if skip_first { 1 } else { 0 }))
                .take(if self.target_return.is_some() {
                    mir.arg_count - 1
                } else {
                    mir.arg_count
                })
                .map(|(local, target_arg)| {
                    let spec_local = self.encoder.encode_local_high(&*mir, local)?;
                    let spec_local_place: vir_high::Expression = spec_local.into();
                    Ok((
                        spec_local_place.substitute_types(substs),
                        target_arg.clone(),
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_iter(),
        );

        // Replacement 2: replace the fake return variable (last argument) of SPEC items with
        // `target_return`
        if let Some(target_return) = self.target_return {
            let fake_return_local = mir.args_iter().last().unwrap();
            let spec_fake_return = self.encoder.encode_local_high(&*mir, fake_return_local)?;
            let spec_fake_return_place: vir_high::Expression = spec_fake_return.into();
            replacements.push((
                spec_fake_return_place.substitute_types(substs),
                target_return.clone(),
            ));
        }

        // Do the replacements
        curr_expr = curr_expr.replace_multiple_places(&replacements);

        // use the provided `self.pre_label` to encode old expressions
        curr_expr = curr_expr.map_old_expression_label(|label| {
            if label == PRECONDITION_LABEL {
                self.pre_label.to_string()
            } else {
                label
            }
        });
        debug!("MIR expr {:?} --> {}", assertion_expr.id, curr_expr);
        Ok(curr_expr.set_default_pos(
            self.encoder
                .error_manager()
                .register(
                    self.encoder.env().tcx().def_span(assertion_expr.expr),
                    ErrorCtxt::GenericExpression,
                    self.parent_def_id,
                )
                .into(),
        ))
    }
}

struct StraightLineBackwardInterpreter<'p, 'v: 'p, 'tcx: 'v> {
    interpreter: ExpressionBackwardInterpreter<'p, 'v, 'tcx>,
}

/// This encoding works backward, so there is the risk of generating expressions whose length
/// is exponential in the number of branches. If this becomes a problem, consider doing a forward
/// encoding (keeping path conditions expressions).
impl<'p, 'v: 'p, 'tcx: 'v> StraightLineBackwardInterpreter<'p, 'v, 'tcx> {
    fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        mir: &'p mir::Body<'tcx>,
        def_id: DefId,
        parent_def_id: DefId,
        tymap: &'p SubstMap<'tcx>,
    ) -> Self {
        StraightLineBackwardInterpreter {
            interpreter: ExpressionBackwardInterpreter::new(
                encoder,
                mir,
                def_id,
                false,
                parent_def_id,
                tymap.clone(),
            ),
        }
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> BackwardMirInterpreter<'tcx>
    for StraightLineBackwardInterpreter<'p, 'v, 'tcx>
{
    type State = ExprBackwardInterpreterState;
    type Error = SpannedEncodingError;

    fn apply_terminator(
        &self,
        bb: mir::BasicBlock,
        term: &mir::Terminator<'tcx>,
        states: HashMap<mir::BasicBlock, &Self::State>,
    ) -> Result<Self::State, Self::Error> {
        trace!("apply_terminator {:?}, states: {:?}", term, states);
        self.interpreter.apply_terminator(bb, term, states)
    }

    fn apply_statement(
        &self,
        bb: mir::BasicBlock,
        stmt_index: usize,
        stmt: &mir::Statement<'tcx>,
        state: &mut Self::State,
    ) -> Result<(), Self::Error> {
        trace!("apply_statement {:?}, state: {:?}", stmt, state);
        self.interpreter
            .apply_statement(bb, stmt_index, stmt, state)
    }
}
