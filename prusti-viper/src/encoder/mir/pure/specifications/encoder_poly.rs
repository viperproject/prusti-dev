// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    encoder::{
        errors::{EncodingError, EncodingResult, SpannedEncodingResult, WithSpan},
        high::types::HighTypeEncoderInterface,
        mir::{
            pure::{specifications::utils::extract_closure_from_ty, PureFunctionEncoderInterface},
            types::MirTypeEncoderInterface,
        },
        mir_encoder::{MirEncoder, PlaceEncoder},
        snapshot::interface::SnapshotEncoderInterface,
        Encoder,
    },
    error_incorrect,
};
use prusti_common::config;
use prusti_rustc_interface::{
    errors::MultiSpan,
    hir::def_id::DefId,
    middle::{ty, ty::GenericArgsRef},
    span::Span,
};
use rustc_hash::FxHashSet;
use vir_crate::polymorphic::ExprIterator;

// TODO: this variant (poly) should not need to exist, eventually should be
//       replaced by the high variant + lowering

pub(super) fn inline_closure<'tcx>(
    encoder: &Encoder<'_, 'tcx>,
    def_id: DefId,
    cl_expr: vir_crate::polymorphic::Expr,
    args: Vec<vir_crate::polymorphic::LocalVar>,
    parent_def_id: DefId,
    substs: GenericArgsRef<'tcx>,
) -> SpannedEncodingResult<vir_crate::polymorphic::Expr> {
    let mir = encoder
        .env()
        .body
        .get_closure_body(def_id, substs, parent_def_id);
    assert_eq!(mir.arg_count, args.len() + 1);
    let mir_encoder = MirEncoder::new(encoder, &mir, def_id);
    let mut body_replacements = vec![];
    for (arg_idx, arg_local) in mir.args_iter().enumerate() {
        let local_span = mir_encoder.get_local_span(arg_local);
        let local = mir_encoder.encode_local(arg_local).unwrap();
        let local_ty = mir.local_decls[arg_local].ty;
        body_replacements.push(if arg_idx == 0 {
            (
                encoder
                    .encode_value_expr(vir_crate::polymorphic::Expr::local(local), local_ty)
                    .with_span(local_span)?,
                cl_expr.clone(),
            )
        } else {
            (
                vir_crate::polymorphic::Expr::local(local),
                vir_crate::polymorphic::Expr::local(args[arg_idx - 1].clone()),
            )
        });
    }
    Ok(encoder
        .encode_pure_expression(def_id, parent_def_id, substs)?
        .replace_multiple_places(&body_replacements))
}

#[allow(clippy::unnecessary_unwrap)]
#[allow(clippy::too_many_arguments)]
pub(super) fn inline_spec_item<'tcx>(
    encoder: &Encoder<'_, 'tcx>,
    def_id: DefId,
    target_args: &[vir_crate::polymorphic::Expr],
    target_return: Option<&vir_crate::polymorphic::Expr>,
    targets_are_values: bool,
    parent_def_id: DefId,
    substs: GenericArgsRef<'tcx>,
) -> SpannedEncodingResult<vir_crate::polymorphic::Expr> {
    // each non-lifetime parameter should be matched with a subst
    assert_eq!(
        substs
            .non_erasable_generics(encoder.env().tcx(), def_id)
            .count(),
        encoder
            .env()
            .query
            .identity_substs(def_id)
            .non_erasable_generics(encoder.env().tcx(), def_id)
            .count()
    );

    let mir = encoder
        .env()
        .body
        .get_expression_body(def_id, substs, parent_def_id);
    assert_eq!(
        mir.arg_count,
        target_args.len() + usize::from(target_return.is_some())
    );
    let mir_encoder = MirEncoder::new(encoder, &mir, def_id);
    let mut body_replacements = vec![];
    for (arg_idx, arg_local) in mir.args_iter().enumerate() {
        let local_span = mir_encoder.get_local_span(arg_local);
        let local = mir_encoder.encode_local(arg_local).unwrap();
        let local_ty = mir.local_decls[arg_local].ty;
        let is_return_arg = target_return.is_some() && arg_idx == mir.arg_count - 1;
        body_replacements.push((
            if targets_are_values && !is_return_arg {
                encoder
                    .encode_value_expr(vir_crate::polymorphic::Expr::local(local.clone()), local_ty)
                    .with_span(local_span)?
            } else {
                vir_crate::polymorphic::Expr::local(local.clone())
            },
            if is_return_arg {
                target_return.unwrap().clone()
            } else {
                target_args[arg_idx].clone()
            },
        ));

        if !is_return_arg {
            body_replacements.push((
                vir_crate::polymorphic::Expr::local(local),
                target_args[arg_idx].clone(),
            ));
        }
    }
    Ok(encoder
        .encode_pure_expression(def_id, parent_def_id, substs)?
        .replace_multiple_places(&body_replacements))
}

pub(super) fn encode_quantifier<'tcx>(
    encoder: &Encoder<'_, 'tcx>,
    _span: Span,
    encoded_args: Vec<vir_crate::polymorphic::Expr>,
    is_exists: bool,
    parent_def_id: DefId,
    substs: ty::GenericArgsRef<'tcx>,
) -> SpannedEncodingResult<vir_crate::polymorphic::Expr> {
    // Quantifiers are encoded as:
    //   forall(
    //     (
    //       ( // trigger set 1
    //         |qvars...| { <trigger expr 1> },
    //         |qvars...| { <trigger expr 2> },
    //       ),
    //       ...,
    //     ),
    //     |qvars...| -> bool { <body expr> },
    //   )

    let cl_type_body = substs.type_at(1);
    let (body_def_id, body_substs, body_span, args, _) =
        extract_closure_from_ty(encoder.env().query, cl_type_body);

    let mut encoded_qvars = vec![];
    let mut bounds = vec![];
    for (arg_idx, arg_ty) in args.into_iter().enumerate() {
        let qvar_ty = encoder.encode_snapshot_type(arg_ty).with_span(body_span)?;
        let qvar_name = format!(
            "_{}_quant_{}",
            arg_idx,
            encoder.encode_item_name(body_def_id),
        );
        let encoded_qvar = vir_crate::polymorphic::LocalVar::new(qvar_name, qvar_ty);
        if config::check_overflows() {
            bounds.extend(encoder.encode_type_bounds(&encoded_qvar.clone().into(), arg_ty));
        } else if config::encode_unsigned_num_constraint() {
            if let ty::TyKind::Uint(_) = arg_ty.kind() {
                let expr =
                    vir_crate::polymorphic::Expr::le_cmp(0u32.into(), encoded_qvar.clone().into());
                bounds.push(expr);
            }
        }
        encoded_qvars.push(encoded_qvar);
    }

    let mut encoded_trigger_sets = vec![];
    for (trigger_set_idx, ty_trigger_set) in
        substs.type_at(0).tuple_fields().into_iter().enumerate()
    {
        let mut encoded_triggers = vec![];
        let mut set_spans = vec![];
        for (trigger_idx, ty_trigger) in ty_trigger_set.tuple_fields().into_iter().enumerate() {
            let (trigger_def_id, trigger_substs, trigger_span, _, _) =
                extract_closure_from_ty(encoder.env().query, ty_trigger);
            let set_field = encoder
                .encode_raw_ref_field(format!("tuple_{trigger_set_idx}"), ty_trigger_set)
                .with_span(trigger_span)?;
            let trigger_field = encoder
                .encode_raw_ref_field(format!("tuple_{trigger_idx}"), ty_trigger)
                .with_span(trigger_span)?;
            // note: `is_encoding_trigger` must be set back to `false` before returning early in case of errors
            encoder.is_encoding_trigger.set(true);
            let encoded_trigger_result = inline_closure(
                encoder,
                trigger_def_id,
                encoded_args[0]
                    .clone()
                    .field(set_field)
                    .field(trigger_field),
                encoded_qvars.clone(),
                parent_def_id,
                trigger_substs,
            );
            encoder.is_encoding_trigger.set(false);
            let mut encoded_trigger = encoded_trigger_result?;

            // slice accesses and other pure calls can get encoded as
            // `foo(...).val_X` but for triggers we need to strip the field
            // access away
            // TODO(tymap): this also strip out user-written field accesses...
            while let vir_crate::polymorphic::Expr::Field(vir_crate::polymorphic::FieldExpr {
                base,
                ..
            }) = encoded_trigger
            {
                encoded_trigger = *base;
            }

            check_trigger(&encoded_trigger).with_span(trigger_span)?;
            encoded_triggers.push(encoded_trigger);
            set_spans.push(trigger_span);
        }
        let encoded_trigger_set = vir_crate::polymorphic::Trigger::new(encoded_triggers);
        check_trigger_set(&encoded_qvars, &encoded_trigger_set)
            .with_span(MultiSpan::from_spans(set_spans))?;
        encoded_trigger_sets.push(encoded_trigger_set);
    }

    let encoded_body = inline_closure(
        encoder,
        body_def_id,
        encoded_args[1].clone(),
        encoded_qvars.clone(),
        parent_def_id,
        body_substs,
    )?;

    // replace qvars with a nicer name based on quantifier depth to ensure that
    // quantifiers remain stable for caching
    let quantifier_depth = find_quantifier_depth(&encoded_body);
    let mut qvar_replacements = vec![];
    let mut fixed_qvars = vec![];
    for (arg_idx, qvar) in encoded_qvars.iter().enumerate() {
        let qvar_rep = vir_crate::polymorphic::LocalVar::new(
            format!("_{arg_idx}_quant_{quantifier_depth}"),
            qvar.typ.clone(),
        );
        qvar_replacements.push((
            vir_crate::polymorphic::Expr::local(qvar.clone()),
            vir_crate::polymorphic::Expr::local(qvar_rep.clone()),
        ));
        fixed_qvars.push(qvar_rep);
    }
    let bounds = bounds
        .into_iter()
        .map(|bound| bound.replace_multiple_places(&qvar_replacements))
        .collect::<Vec<_>>();
    let encoded_body = encoded_body.replace_multiple_places(&qvar_replacements);
    let encoded_trigger_sets = encoded_trigger_sets
        .into_iter()
        .map(|set| set.replace_multiple_places(&qvar_replacements))
        .collect::<Vec<_>>();

    let final_body = if bounds.is_empty() {
        encoded_body
    } else if is_exists {
        vir_crate::polymorphic::Expr::and(bounds.into_iter().conjoin(), encoded_body)
    } else {
        vir_crate::polymorphic::Expr::implies(bounds.into_iter().conjoin(), encoded_body)
    };
    if is_exists {
        Ok(vir_crate::polymorphic::Expr::exists(
            fixed_qvars,
            encoded_trigger_sets,
            final_body,
        ))
    } else {
        Ok(vir_crate::polymorphic::Expr::forall(
            fixed_qvars,
            encoded_trigger_sets,
            final_body,
        ))
    }
}

fn find_quantifier_depth(expr: &vir_crate::polymorphic::Expr) -> usize {
    use vir_crate::polymorphic::ExprWalker;
    struct DepthChecker {
        current_depth: usize,
        max_depth: usize,
    }
    impl ExprWalker for DepthChecker {
        fn walk_forall(&mut self, statement: &vir_crate::polymorphic::ForAll) {
            self.current_depth += 1;
            if self.current_depth >= self.max_depth {
                self.max_depth = self.current_depth;
            }
            self.walk(&statement.body);
            self.current_depth -= 1;
        }
        fn walk_exists(&mut self, statement: &vir_crate::polymorphic::Exists) {
            self.current_depth += 1;
            if self.current_depth >= self.max_depth {
                self.max_depth = self.current_depth;
            }
            self.walk(&statement.body);
            self.current_depth -= 1;
        }
    }
    let mut checker = DepthChecker {
        current_depth: 0,
        max_depth: 0,
    };
    checker.walk(expr);
    checker.max_depth
}

fn check_trigger(trigger: &vir_crate::polymorphic::Expr) -> EncodingResult<()> {
    use vir_crate::polymorphic::FallibleExprFolder;
    struct TriggerChecker {}
    impl FallibleExprFolder for TriggerChecker {
        type Error = EncodingError;
        fn fallible_fold(
            &mut self,
            e: vir_crate::polymorphic::Expr,
        ) -> Result<vir_crate::polymorphic::Expr, Self::Error> {
            match e {
                // legal triggers
                vir_crate::polymorphic::Expr::Local(..)
                | vir_crate::polymorphic::Expr::Const(..)
                | vir_crate::polymorphic::Expr::FuncApp(..)
                | vir_crate::polymorphic::Expr::DomainFuncApp(..) => Ok(e),
                // everything else is illegal in triggers
                _ => Err(EncodingError::incorrect(
                    "only function calls are allowed in triggers",
                )),
            }
        }
    }
    // TODO: more precise span: what is the span of the invalid expression?
    (TriggerChecker {}).fallible_fold(trigger.clone())?;
    Ok(())
}

fn check_trigger_set(
    bound_vars: &[vir_crate::polymorphic::LocalVar],
    trigger_set: &vir_crate::polymorphic::Trigger,
) -> EncodingResult<()> {
    let bound_vars_expr = bound_vars
        .iter()
        .map(|var| var.clone().into())
        .collect::<Vec<_>>();
    let mut found_bounded_vars = FxHashSet::default();
    for term in trigger_set.elements() {
        found_bounded_vars.extend(bound_vars_expr.iter().filter(|var| term.find(var)));
    }
    if bound_vars_expr
        .iter()
        .any(|var| !found_bounded_vars.contains(var))
    {
        // TODO: mention (+ span) the missing qvars in the error
        error_incorrect!("a trigger set must mention all bound variables");
    }
    Ok(())
}
