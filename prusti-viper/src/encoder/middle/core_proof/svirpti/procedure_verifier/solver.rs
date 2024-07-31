use super::{
    super::{
        super::transformations::encoder_context::EncoderContext,
        smt::{Info, Sort2SmtWrap},
        VerificationError,
    },
    manual_triggering::TriggerTermCollector,
    ProcedureExecutor,
};
use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::{common::expression::UnaryOperationHelpers, low as vir_low};

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn comment(&mut self, comment: &str) -> SpannedEncodingResult<()> {
        self.smt_solver.comment(comment).unwrap(); // TODO: handle error
        Ok(())
    }

    pub(super) fn assume_axiom(
        &mut self,
        expression: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        let info = Info {
            program_context: self.program_context,
        };
        self.smt_solver.assert(expression, info).unwrap(); // TODO: handle error
        Ok(())
    }

    pub(super) fn assume(&mut self, expression: &vir_low::Expression) -> SpannedEncodingResult<()> {
        let info = Info {
            program_context: self.program_context,
        };
        let mut collector = TriggerTermCollector::new(self.program_context);
        collector.analyse_expression(&expression);
        collector.emit_triggering_terms(&mut self.smt_solver, &mut self.trigger_wrappers)?;
        self.smt_solver.assert(expression, info).unwrap(); // TODO: handle error
        Ok(())
    }

    pub(super) fn smoke_check(&mut self) -> SpannedEncodingResult<()> {
        let result = self.smt_solver.check_sat().unwrap(); // TODO: handle error
        assert!(!result.is_unsat(), "Smoke check failed");
        Ok(())
    }

    pub(super) fn assert(
        &mut self,
        expression: vir_low::Expression,
        error: VerificationError,
    ) -> SpannedEncodingResult<()> {
        self.assert_with_assumptions(&[], expression, error)
        // self.smt_solver.push().unwrap(); // TODO: handle error
        // let negated_expression = vir_low::Expression::not(expression);
        // let info = Info {
        //     program_context: self.program_context,
        // };
        // self.smt_solver.assert(&negated_expression, info).unwrap(); // TODO: handle error
        // let result = self.smt_solver.check_sat().unwrap(); // TODO: handle error
        // if result.is_sat_or_unknown() {
        //     self.verifier.report_error(error);
        // }
        // self.smt_solver.pop().unwrap(); // TODO: handle error
        // Ok(())
    }

    pub(super) fn assert_with_assumptions(
        &mut self,
        assumptions: &[vir_low::Expression],
        expression: vir_low::Expression,
        error: VerificationError,
    ) -> SpannedEncodingResult<()> {
        self.smt_solver.push().unwrap(); // TODO: handle error
        let info = Info {
            program_context: self.program_context,
        };
        let mut collector = TriggerTermCollector::new(self.program_context);
        collector.analyse_expression(&expression);
        for assumption in assumptions {
            collector.analyse_expression(assumption);
        }
        collector.emit_triggering_terms(&mut self.smt_solver, &mut self.trigger_wrappers)?;
        let negated_expression = vir_low::Expression::not(expression);
        for assumption in assumptions {
            self.smt_solver.assert(assumption, info).unwrap(); // TODO: handle error
        }
        self.smt_solver.assert(&negated_expression, info).unwrap(); // TODO: handle error
        let result = self.smt_solver.check_sat().unwrap(); // TODO: handle error
        if result.is_sat_or_unknown() {
            self.verifier.report_error(error);
        }
        self.smt_solver.pop().unwrap(); // TODO: handle error
        Ok(())
    }

    pub(super) fn declare_variable(
        &mut self,
        variable: &vir_low::VariableDecl,
    ) -> SpannedEncodingResult<()> {
        self.smt_solver
            .declare_variable(&variable.name, variable.ty.wrap())
            .unwrap(); // TODO: handle error
        Ok(())
    }
}
