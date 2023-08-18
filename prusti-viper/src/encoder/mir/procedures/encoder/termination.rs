use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingError, SpannedEncodingResult, WithSpan},
    mir::{
        contracts::{ContractsEncoderInterface, ProcedureContractMirDef},
        errors::ErrorInterface,
        pure::SpecificationEncoderInterface,
        specifications::SpecificationsInterface,
    },
};
use prusti_rustc_interface::{
    middle::{mir::BasicBlock, ty::GenericArgsRef},
    span::Span,
};
use vir_crate::{
    common::{check_mode::CheckMode, expression::BinaryOperationHelpers},
    high::{self as vir_high, builders::procedure::BasicBlockBuilder},
};

pub(super) enum TerminationMeasure {
    /// A termination measure of type Int.
    Int(vir_high::Expression),
    /// The annotated item is trusted to always terminate.
    Trusted,
}

impl<'p, 'v: 'p, 'tcx: 'v> super::ProcedureEncoder<'p, 'v, 'tcx> {
    pub(super) fn needs_termination(&self, bb: BasicBlock) -> bool {
        let function_termination = self.encoder.terminates(self.def_id, None);
        let ghost_block = self.specification_blocks.is_ghost_block(bb);
        function_termination || ghost_block
    }

    pub(super) fn encode_termination_expression(
        &mut self,
        procedure_contract: &ProcedureContractMirDef<'tcx>,
        span: Span,
        call_substs: GenericArgsRef<'tcx>,
        arguments: &[vir_high::Expression],
    ) -> SpannedEncodingResult<TerminationMeasure> {
        assert!(self.encoder.terminates(self.def_id, None));

        let (expr, expr_substs) = procedure_contract
            .functional_termination_measure(self.encoder.env(), call_substs)
            .ok_or_else(|| {
                SpannedEncodingError::incorrect(
                    "Terminating function calls nonterminating function",
                    span,
                )
            })?;

        let expression = self.encoder.encode_assertion_high(
            expr.to_def_id(),
            None,
            arguments,
            None,
            self.def_id,
            expr_substs,
        )?;
        if let vir_high::Expression::FuncApp(vir_high::FuncApp { function_name, .. }) = &expression
        {
            if function_name == "m_prusti_contracts$$prusti_terminates_trusted" {
                return Ok(TerminationMeasure::Trusted);
            }
        }
        Ok(TerminationMeasure::Int(expression))
    }

    pub(super) fn encode_termination_initialization(
        &mut self,
    ) -> SpannedEncodingResult<Vec<vir_high::Statement>> {
        let mir_span = self.mir.span;
        let substs = self.encoder.env().query.identity_substs(self.def_id);
        // Retrieve the contract
        let procedure_contract = self
            .encoder
            .get_mir_procedure_contract_for_def(self.def_id, substs)
            .with_span(mir_span)?;
        let mut arguments: Vec<vir_high::Expression> = Vec::new();
        for local in self.mir.args_iter() {
            arguments.push(self.encode_local(local)?.into());
        }

        if self.encoder.terminates(self.def_id, None) && self.check_mode != CheckMode::CoreProof {
            let termination_expr = self.encode_termination_expression(
                &procedure_contract,
                mir_span,
                substs,
                &arguments,
            )?;
            if let TerminationMeasure::Int(termination_expr) = termination_expr {
                let term_var = self.fresh_ghost_variable(
                    "termination_var",
                    vir_high::Type::Int(vir_high::ty::Int::Unbounded),
                );
                self.termination_variable = Some(term_var.clone());
                let assign_stmt =
                    vir_high::Statement::ghost_assign_no_pos(term_var.into(), termination_expr);
                let assign_stmt = self.encoder.set_statement_error_ctxt(
                    assign_stmt,
                    mir_span,
                    ErrorCtxt::UnexpectedAssignMethodTerminationMeasure,
                    self.def_id,
                )?;
                Ok(vec![assign_stmt])
            } else {
                Ok(vec![])
            }
        } else {
            Ok(vec![])
        }
    }

    pub(super) fn encode_termination_measure_call_assertion(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        span: Span,
        procedure_contract: &ProcedureContractMirDef<'tcx>,
        call_substs: GenericArgsRef<'tcx>,
        arguments: &[vir_high::Expression],
    ) -> SpannedEncodingResult<()> {
        let called_fun = procedure_contract.def_id;

        if !self.encoder.terminates(called_fun, Some(call_substs)) {
            block_builder.add_statement(self.encoder.set_statement_error_ctxt(
                vir_high::Statement::assert_no_pos(false.into()),
                span,
                ErrorCtxt::UnexpectedReachableCall,
                self.def_id,
            )?);
        }

        if !self
            .encoder
            .env()
            .callee_reaches_caller(self.def_id, called_fun, call_substs)
        {
            return Ok(());
        }

        let Some(term_var) = self.termination_variable.clone() else {
            return Ok(());
        };
        let term_ty = vir_high::Type::Int(vir_high::ty::Int::Unbounded);

        // called termination measure is lower
        let call_expr =
            self.encode_termination_expression(procedure_contract, span, call_substs, arguments)?;
        if let TerminationMeasure::Int(call_expr) = call_expr {
            let cond = vir_high::Expression::greater_than(term_var.clone().into(), call_expr);
            let assert_statement = self.encoder.set_statement_error_ctxt(
                vir_high::Statement::assert_no_pos(cond),
                span,
                ErrorCtxt::CallTerminationMeasureLower,
                self.def_id,
            )?;
            block_builder.add_statement(assert_statement);
        }

        // called termination measure should be non-negative
        let zero = vir_high::Expression::constant_no_pos(0.into(), term_ty);
        let cond = vir_high::Expression::greater_equals(term_var.into(), zero);
        let assert_statement = self.encoder.set_statement_error_ctxt(
            vir_high::Statement::assert_no_pos(cond),
            span,
            ErrorCtxt::CallTerminationMeasureNonNegative,
            self.def_id,
        )?;
        block_builder.add_statement(assert_statement);

        Ok(())
    }
}
