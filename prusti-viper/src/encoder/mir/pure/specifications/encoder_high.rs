// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::{
    errors::SpannedEncodingResult,
    mir::{
        places::PlacesEncoderInterface,
        pure::{specifications::utils::extract_closure_from_ty, PureFunctionEncoderInterface},
        types::MirTypeEncoderInterface,
    },
    mir_encoder::{MirEncoder, PlaceEncoder},
    Encoder,
};
use prusti_common::config;
use prusti_rustc_interface::{
    hir::def_id::DefId,
    middle::{ty, ty::subst::SubstsRef},
    span::Span,
};
use vir_crate::{
    common::expression::{BinaryOperationHelpers, ExpressionIterator, QuantifierHelpers},
    high as vir_high,
};

fn simplify(expression: vir_high::Expression) -> vir_high::Expression {
    if prusti_common::config::unsafe_core_proof() {
        expression.simplify()
    } else {
        expression
    }
}

pub(super) fn inline_closure_high<'tcx>(
    encoder: &Encoder<'_, 'tcx>,
    def_id: DefId,
    cl_expr: vir_high::Expression,
    args: Vec<vir_high::VariableDecl>,
    parent_def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> SpannedEncodingResult<vir_high::Expression> {
    let mir = encoder.env().local_mir(def_id.expect_local(), substs);
    assert_eq!(mir.arg_count, args.len() + 1);
    let mut body_replacements = vec![];
    for (arg_idx, arg_local) in mir.args_iter().enumerate() {
        let local: vir_high::Expression =
            encoder.encode_local_high(&mir, arg_local).unwrap().into();
        let argument = if arg_idx == 0 {
            cl_expr.clone()
        } else {
            args[arg_idx - 1].clone().into()
        };
        body_replacements.push((local.erase_lifetime(), argument.erase_lifetime()));
    }
    Ok(simplify(
        encoder
            .encode_pure_expression_high(def_id, parent_def_id, substs)?
            .erase_lifetime()
            .replace_multiple_places(&body_replacements),
    ))
}

#[allow(clippy::unnecessary_unwrap)]
pub(super) fn inline_spec_item_high<'tcx>(
    encoder: &Encoder<'_, 'tcx>,
    def_id: DefId,
    target_args: &[vir_high::Expression],
    target_return: Option<&vir_high::Expression>,
    targets_are_values: bool,
    parent_def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> SpannedEncodingResult<vir_high::Expression> {
    let mir = encoder.env().local_mir(def_id.expect_local(), substs);
    assert_eq!(
        mir.arg_count,
        target_args.len() + if target_return.is_some() { 1 } else { 0 },
        "def_id: {:?}",
        def_id
    );
    let mir_encoder = MirEncoder::new(encoder, &mir, def_id);
    let mut body_replacements = vec![];
    for (arg_idx, arg_local) in mir.args_iter().enumerate() {
        let local = mir_encoder.encode_local_high(arg_local).unwrap();
        body_replacements.push((
            if targets_are_values {
                todo!("value_expr_high ?")
                //let local_ty = mir.local_decls[arg_local].ty;
                //let local_span = mir_encoder.get_local_span(arg_local);
                //encoder.encode_value_expr_high(
                //    vir_high::Expression::local_no_pos(local),
                //    local_ty,
                //).with_span(local_span)?
            } else {
                vir_high::Expression::local_no_pos(local)
            },
            if target_return.is_some() && arg_idx == mir.arg_count - 1 {
                target_return.unwrap().clone()
            } else {
                target_args[arg_idx].clone()
            },
        ));
    }
    Ok(simplify(
        encoder
            .encode_pure_expression_high(def_id, parent_def_id, substs)?
            .replace_multiple_places(&body_replacements),
    ))
}

pub(super) fn encode_quantifier_high<'tcx>(
    encoder: &Encoder<'_, 'tcx>,
    _span: Span, // TODO: use span somehow? or remove arg
    encoded_args: Vec<vir_high::Expression>,
    is_exists: bool,
    parent_def_id: DefId,
    substs: ty::subst::SubstsRef<'tcx>,
) -> SpannedEncodingResult<vir_high::Expression> {
    let tcx = encoder.env().tcx();

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
    let (body_def_id, body_substs, _, args, _) = extract_closure_from_ty(tcx, cl_type_body);

    let mut encoded_qvars = vec![];
    let mut bounds = vec![];
    for (arg_idx, arg_ty) in args.into_iter().enumerate() {
        let qvar_ty = encoder.encode_type_high(arg_ty).unwrap();
        let qvar_name = format!("_{}_quant_{}", arg_idx, body_def_id.index.index());
        let encoded_qvar = vir_high::VariableDecl::new(qvar_name, qvar_ty);
        if config::check_overflows() {
            bounds.extend(encoder.encode_type_bounds_high(&encoded_qvar.clone().into(), arg_ty));
        } else if config::encode_unsigned_num_constraint() {
            if let ty::TyKind::Uint(_) = arg_ty.kind() {
                let expr =
                    vir_high::Expression::less_equals(0u32.into(), encoded_qvar.clone().into());
                bounds.push(expr);
            }
        }
        encoded_qvars.push(encoded_qvar);
    }

    // TODO: implement trigger and trigger set checks
    let mut encoded_trigger_sets = vec![];
    for (trigger_set_idx, ty_trigger_set) in
        substs.type_at(0).tuple_fields().into_iter().enumerate()
    {
        let mut encoded_triggers = vec![];
        for (trigger_idx, ty_trigger) in ty_trigger_set.tuple_fields().into_iter().enumerate() {
            let (trigger_def_id, trigger_substs, _, _, _) =
                extract_closure_from_ty(tcx, ty_trigger);
            let set_field = vir_high::FieldDecl::new(
                format!("tuple_{}", trigger_set_idx),
                trigger_set_idx,
                encoder.encode_type_high(ty_trigger_set)?,
            );
            let trigger_field = vir_high::FieldDecl::new(
                format!("tuple_{}", trigger_idx),
                trigger_idx,
                encoder.encode_type_high(ty_trigger)?,
            );
            encoded_triggers.push(inline_closure_high(
                encoder,
                trigger_def_id,
                // FIXME: check whether the closure expression does not need to
                // be wrapped in `addr_of` like in `encode_invariant_high`.
                vir_high::Expression::field_no_pos(
                    vir_high::Expression::field_no_pos(encoded_args[0].clone(), set_field),
                    trigger_field,
                ),
                encoded_qvars.clone(),
                parent_def_id,
                trigger_substs,
            )?);
        }
        encoded_trigger_sets.push(vir_high::Trigger::new(encoded_triggers));
    }

    let encoded_body = inline_closure_high(
        encoder,
        body_def_id,
        encoded_args[1].clone(),
        encoded_qvars.clone(),
        parent_def_id,
        body_substs,
    )?;

    // TODO: implement cache-friendly qvar renaming

    let final_body = if bounds.is_empty() {
        encoded_body
    } else if is_exists {
        vir_high::Expression::and(bounds.into_iter().conjoin(), encoded_body)
    } else {
        vir_high::Expression::implies(bounds.into_iter().conjoin(), encoded_body)
    };
    if is_exists {
        Ok(vir_high::Expression::exists(
            encoded_qvars,
            encoded_trigger_sets,
            simplify(final_body),
        ))
    } else {
        Ok(vir_high::Expression::forall(
            encoded_qvars,
            encoded_trigger_sets,
            simplify(final_body),
        ))
    }
}
