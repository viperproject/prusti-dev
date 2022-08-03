// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::{
    errors::{SpannedEncodingResult, WithSpan},
    mir::{
        places::PlacesEncoderInterface,
        pure::{
            interpreter::ExpressionBackwardInterpreter,
            specifications::{
                encoder_high::{
                    encode_quantifier_high, inline_closure_high, inline_spec_item_high,
                },
                encoder_poly::{encode_quantifier, inline_closure, inline_spec_item},
            },
            PureEncodingContext, PureFunctionBackwardInterpreter,
        },
    },
    mir_encoder::{MirEncoder, PlaceEncoder, PRECONDITION_LABEL},
    mir_interpreter::run_backward_interpretation_point_to_point,
    snapshot::interface::SnapshotEncoderInterface,
};
use prusti_rustc_interface::{
    hir::def_id::{DefId, LocalDefId},
    middle::{mir, ty::subst::SubstsRef},
    span::Span,
};
use vir_crate::{
    high::{self as vir_high, operations::ty::Typed},
    polymorphic as vir_poly,
};

pub(crate) trait SpecificationEncoderInterface<'tcx> {
    fn encode_prusti_operation_high(
        &self,
        fn_name: &str,
        span: Span,
        encoded_args: Vec<vir_high::Expression>,
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;

    #[allow(clippy::too_many_arguments)]
    fn encode_assertion_high(
        &self,
        assertion: &LocalDefId,
        pre_label: Option<&str>,
        target_args: &[vir_high::Expression],
        target_return: Option<&vir_high::Expression>,
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;

    fn encode_invariant_high(
        &self,
        mir: &mir::Body<'tcx>, // body of the method containing the loop
        invariant_block: mir::BasicBlock, // in which the invariant is defined
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;

    fn encode_prusti_operation(
        &self,
        fn_name: &str,
        span: Span,
        encoded_args: Vec<vir_poly::Expr>,
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_poly::Expr>;

    #[allow(clippy::too_many_arguments)]
    fn encode_assertion(
        &self,
        assertion: &LocalDefId,
        pre_label: Option<&str>,
        target_args: &[vir_poly::Expr],
        target_return: Option<&vir_poly::Expr>,
        targets_are_values: bool,
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_poly::Expr>;

    fn encode_invariant(
        &self,
        mir: &mir::Body<'tcx>, // body of the method containing the loop
        invariant_block: mir::BasicBlock, // in which the invariant is defined
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_poly::Expr>;
}

impl<'v, 'tcx: 'v> SpecificationEncoderInterface<'tcx> for crate::encoder::Encoder<'v, 'tcx> {
    fn encode_prusti_operation_high(
        &self,
        fn_name: &str,
        span: Span,
        encoded_args: Vec<vir_high::Expression>,
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        match fn_name {
            "prusti_contracts::forall" | "prusti_contracts::exists" => encode_quantifier_high(
                self,
                span,
                encoded_args,
                fn_name == "prusti_contracts::exists",
                parent_def_id,
                substs,
            ),
            _ => unimplemented!(),
        }
    }

    fn encode_assertion_high(
        &self,
        assertion: &LocalDefId,
        _pre_label: Option<&str>, // TODO: use pre_label (map labels)
        target_args: &[vir_high::Expression],
        target_return: Option<&vir_high::Expression>,
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let encoded_assertion = inline_spec_item_high(
            self,
            assertion.to_def_id(),
            target_args,
            target_return,
            false,
            parent_def_id,
            substs,
        )?;
        let position = self.error_manager().register_span(
            parent_def_id,
            self.env().tcx().def_span(assertion.to_def_id()),
        );
        Ok(encoded_assertion.set_default_position(position.into()))
    }

    fn encode_invariant_high(
        &self,
        mir: &mir::Body<'tcx>, // body of the method containing the loop
        invariant_block: mir::BasicBlock, // in which the invariant is defined
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        // identify previous block: there should only be one
        let predecessors = &mir.basic_blocks.predecessors()[invariant_block];
        assert_eq!(predecessors.len(), 1);
        let predecessor = predecessors[0];

        // identify closure aggregate assign (the invariant body)
        let closure_assigns = mir.basic_blocks()[invariant_block]
            .statements
            .iter()
            .enumerate()
            .filter_map(|(loc, stmt)| {
                if let mir::StatementKind::Assign(box (
                    lhs,
                    mir::Rvalue::Aggregate(box mir::AggregateKind::Closure(cl_def_id, _), _),
                )) = stmt.kind
                {
                    Some((loc, lhs, cl_def_id))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        // extract relevant data
        // again there should only be one such assignment because the invariant
        // spec block should consist *only* of a closure aggregate assign with
        // its upvars initialised before
        assert_eq!(closure_assigns.len(), 1);
        let (inv_loc, inv_cl_expr, inv_def_id) = closure_assigns[0];

        // encode the LHS of closure assign into a VIR expression
        let mir_encoder = MirEncoder::new(self, mir, parent_def_id);
        let span =
            mir_encoder.get_span_of_location(prusti_rustc_interface::middle::mir::Location {
                block: invariant_block,
                statement_index: inv_loc,
            });
        let inv_cl_expr_encoded = self
            .encode_place_high(mir, inv_cl_expr, Some(span))
            .with_span(span)?;
        let closure_borrow_type = vir_high::Type::reference(
            vir_high::ty::LifetimeConst::erased(),
            vir_high::ty::Uniqueness::Shared,
            inv_cl_expr_encoded.get_type().clone(),
        );
        // We need this because the specification closure function takes the
        // itself as a shared argument.
        let closure_expression_borrow = inv_cl_expr_encoded.addr_of_no_pos(closure_borrow_type);

        // inline invariant body
        let encoded_invariant = inline_closure_high(
            self,
            inv_def_id,
            closure_expression_borrow,
            vec![],
            parent_def_id,
            substs,
        )?
        .erase_lifetime();

        // backward interpret the body to get rid of the upvars
        let interpreter = ExpressionBackwardInterpreter::new(
            self,
            mir,
            parent_def_id,
            PureEncodingContext::Code,
            parent_def_id,
            substs,
        );
        let invariant = run_backward_interpretation_point_to_point(
             mir,
             &interpreter,
             predecessor,
             invariant_block,
             inv_loc + 1, // include the closure assign itself
             crate::encoder::mir::pure::interpreter::state::ExprBackwardInterpreterState::new_defined(encoded_invariant),
             crate::encoder::mir::pure::interpreter::state::ExprBackwardInterpreterState::new(None),
         )?;

        let final_invariant = invariant.unwrap().into_expr().unwrap();
        let final_invariant = final_invariant.simplify();
        Ok(final_invariant)
    }

    fn encode_prusti_operation(
        &self,
        fn_name: &str,
        span: Span,
        encoded_args: Vec<vir_poly::Expr>,
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_poly::Expr> {
        match fn_name {
            "prusti_contracts::forall" | "prusti_contracts::exists" => encode_quantifier(
                self,
                span,
                encoded_args,
                fn_name == "prusti_contracts::exists",
                parent_def_id,
                substs,
            ),
            _ => unimplemented!(),
        }
    }

    fn encode_assertion(
        &self,
        assertion: &LocalDefId,
        pre_label: Option<&str>,
        target_args: &[vir_poly::Expr],
        target_return: Option<&vir_poly::Expr>,
        targets_are_values: bool,
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_poly::Expr> {
        let mut encoded_assertion = inline_spec_item(
            self,
            assertion.to_def_id(),
            target_args,
            target_return,
            targets_are_values,
            parent_def_id,
            substs,
        )?;

        // map old labels
        if let Some(pre_label) = pre_label {
            encoded_assertion = encoded_assertion.map_old_expr_label(|label| {
                if label == PRECONDITION_LABEL {
                    pre_label.to_string()
                } else {
                    label
                }
            });
        }

        let span = self.env().tcx().def_span(assertion.to_def_id());
        encoded_assertion = self.patch_snapshots(encoded_assertion).with_span(span)?;

        Ok(encoded_assertion
            .set_default_pos(self.error_manager().register_span(parent_def_id, span)))
    }

    fn encode_invariant(
        &self,
        mir: &mir::Body<'tcx>, // body of the method containing the loop
        invariant_block: mir::BasicBlock, // in which the invariant is defined
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<vir_poly::Expr> {
        // identify previous block: there should only be one
        let predecessors = &mir.basic_blocks.predecessors()[invariant_block];
        assert_eq!(predecessors.len(), 1);
        let predecessor = predecessors[0];

        // identify closure aggregate assign (the invariant body)
        let closure_assigns = mir.basic_blocks()[invariant_block]
            .statements
            .iter()
            .enumerate()
            .filter_map(|(loc, stmt)| {
                if let mir::StatementKind::Assign(box (
                    lhs,
                    mir::Rvalue::Aggregate(box mir::AggregateKind::Closure(cl_def_id, _), _),
                )) = stmt.kind
                {
                    Some((loc, lhs, cl_def_id))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        // extract relevant data
        // again there should only be one such assignment because the invariant
        // spec block should consist *only* of a closure aggregate assign with
        // its upvars initialised before
        assert_eq!(closure_assigns.len(), 1);
        let (inv_loc, inv_cl_expr, inv_def_id) = closure_assigns[0];

        // encode the LHS of closure assign into a VIR expression
        let mir_encoder = MirEncoder::new(self, mir, parent_def_id);
        let span =
            mir_encoder.get_span_of_location(prusti_rustc_interface::middle::mir::Location {
                block: invariant_block,
                statement_index: inv_loc,
            });
        let (inv_cl_expr_encoded, _, _) = mir_encoder.encode_place(inv_cl_expr).with_span(span)?;

        // inline invariant body
        let encoded_invariant = inline_closure(
            self,
            inv_def_id,
            inv_cl_expr_encoded.try_into_expr().unwrap(),
            vec![],
            parent_def_id,
            substs,
        )?;

        // backward interpret the body to get rid of the upvars
        let interpreter = PureFunctionBackwardInterpreter::new(
            self,
            mir,
            parent_def_id,
            PureEncodingContext::Code,
            parent_def_id,
        );
        let invariant = run_backward_interpretation_point_to_point(
            mir,
            &interpreter,
            predecessor,
            invariant_block,
            inv_loc + 1, // include the closure assign itself
            crate::encoder::mir_interpreter::ExprBackwardInterpreterState::new_defined(
                encoded_invariant,
            ),
            crate::encoder::mir_interpreter::ExprBackwardInterpreterState::new(None),
        )?;

        // TODO: deal with old(...) ?
        let final_invariant = invariant.unwrap().into_expr().unwrap();
        Ok(final_invariant)
    }
}
