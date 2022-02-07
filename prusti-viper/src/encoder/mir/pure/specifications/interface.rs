// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::{
    encoder::SubstMap,
    errors::{ErrorCtxt, SpannedEncodingResult, WithSpan},
    mir::pure::{
        specifications::{
            encoder_high::{encode_quantifier_high, inline_spec_item_high},
            encoder_poly::{encode_quantifier, inline_closure, inline_spec_item},
        },
        PureFunctionBackwardInterpreter,
    },
    mir_encoder::{MirEncoder, PlaceEncoder, PRECONDITION_LABEL},
    mir_interpreter::{run_backward_interpretation_point_to_point, ExprBackwardInterpreterState},
    snapshot::interface::SnapshotEncoderInterface,
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{mir, ty::subst::SubstsRef};
use rustc_span::Span;
use vir_crate::high::Expression;

pub(crate) trait SpecificationEncoderInterface<'tcx> {
    fn encode_prusti_operation_high(
        &self,
        fn_name: &str,
        span: Span,
        substs: SubstsRef<'tcx>,
        encoded_args: Vec<Expression>,
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<Expression>;

    #[allow(clippy::too_many_arguments)]
    fn encode_assertion_high(
        &self,
        assertion: &LocalDefId,
        pre_label: Option<&str>,
        target_args: &[Expression],
        target_return: Option<&Expression>,
        error: ErrorCtxt,
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<Expression>;

    fn encode_prusti_operation(
        &self,
        fn_name: &str,
        span: Span,
        substs: SubstsRef<'tcx>,
        encoded_args: Vec<vir_crate::polymorphic::Expr>,
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_crate::polymorphic::Expr>;

    #[allow(clippy::too_many_arguments)]
    fn encode_assertion(
        &self,
        assertion: &LocalDefId,
        pre_label: Option<&str>,
        target_args: &[vir_crate::polymorphic::Expr],
        target_return: Option<&vir_crate::polymorphic::Expr>,
        targets_are_values: bool,
        error: ErrorCtxt,
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_crate::polymorphic::Expr>;

    fn encode_invariant(
        &self,
        mir: &mir::Body<'tcx>, // body of the method containing the loop
        invariant_block: mir::BasicBlock, // in which the invariant is defined
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_crate::polymorphic::Expr>;
}

impl<'v, 'tcx: 'v> SpecificationEncoderInterface<'tcx> for crate::encoder::Encoder<'v, 'tcx> {
    fn encode_prusti_operation_high(
        &self,
        fn_name: &str,
        span: Span,
        substs: SubstsRef<'tcx>,
        encoded_args: Vec<Expression>,
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<Expression> {
        match fn_name {
            "prusti_contracts::forall" | "prusti_contracts::exists" => encode_quantifier_high(
                self,
                span,
                substs,
                encoded_args,
                fn_name == "prusti_contracts::exists",
                parent_def_id,
                tymap,
            ),
            _ => unimplemented!(),
        }
    }

    fn encode_assertion_high(
        &self,
        assertion: &LocalDefId,
        _pre_label: Option<&str>, // TODO: use pre_label (map labels)
        target_args: &[Expression],
        target_return: Option<&Expression>,
        error: ErrorCtxt,
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<Expression> {
        let encoded_assertion = inline_spec_item_high(
            self,
            assertion.to_def_id(),
            target_args,
            target_return,
            false,
            parent_def_id,
            tymap,
        )?;
        let position = self.error_manager().register(
            self.env().tcx().def_span(assertion.to_def_id()),
            error,
            parent_def_id,
        );
        Ok(encoded_assertion.set_default_position(position.into()))
    }

    fn encode_prusti_operation(
        &self,
        fn_name: &str,
        span: Span,
        substs: SubstsRef<'tcx>,
        encoded_args: Vec<vir_crate::polymorphic::Expr>,
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_crate::polymorphic::Expr> {
        match fn_name {
            "prusti_contracts::forall" | "prusti_contracts::exists" => encode_quantifier(
                self,
                span,
                substs,
                encoded_args,
                fn_name == "prusti_contracts::exists",
                parent_def_id,
                tymap,
            ),
            _ => unimplemented!(),
        }
    }

    fn encode_assertion(
        &self,
        assertion: &LocalDefId,
        pre_label: Option<&str>,
        target_args: &[vir_crate::polymorphic::Expr],
        target_return: Option<&vir_crate::polymorphic::Expr>,
        targets_are_values: bool,
        error: ErrorCtxt,
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_crate::polymorphic::Expr> {
        let mut encoded_assertion = inline_spec_item(
            self,
            assertion.to_def_id(),
            target_args,
            target_return,
            targets_are_values,
            parent_def_id,
            tymap,
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
        encoded_assertion = self
            .patch_snapshots(encoded_assertion, tymap)
            .with_span(span)?;
        Ok(
            encoded_assertion.set_default_pos(self.error_manager().register(
                span,
                error,
                parent_def_id,
            )),
        )
    }

    fn encode_invariant(
        &self,
        mir: &mir::Body<'tcx>, // body of the method containing the loop
        invariant_block: mir::BasicBlock, // in which the invariant is defined
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_crate::polymorphic::Expr> {
        // identify previous block: there should only be one
        let predecessors = &mir.predecessors()[invariant_block];
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
        let span = mir_encoder.get_span_of_location(rustc_middle::mir::Location {
            block: invariant_block,
            statement_index: inv_loc,
        });
        let (inv_cl_expr_encoded, _, _) = mir_encoder.encode_place(&inv_cl_expr).with_span(span)?;

        // inline invariant body
        let encoded_invariant = inline_closure(
            self,
            inv_def_id,
            inv_cl_expr_encoded.try_into_expr().unwrap(),
            vec![],
            parent_def_id,
            tymap,
        )?;

        // backward interpret the body to get rid of the upvars
        let interpreter = PureFunctionBackwardInterpreter::new(
            self,
            mir,
            parent_def_id,
            false,
            parent_def_id,
            tymap.clone(),
        );
        let invariant = run_backward_interpretation_point_to_point(
            mir,
            &interpreter,
            predecessor,
            invariant_block,
            inv_loc + 1, // include the closure assign itself
            ExprBackwardInterpreterState::new_defined(encoded_invariant),
            ExprBackwardInterpreterState::new(None),
        )?;

        // TODO: deal with old(...) ?

        Ok(invariant.unwrap().into_expr().unwrap())
    }
}
