use super::HeapEncoder;
use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::low::{self as vir_low};

impl<'p, 'v: 'p, 'tcx: 'v> HeapEncoder<'p, 'v, 'tcx> {
    pub(super) fn encode_statement_internal(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        statement: vir_low::Statement,
    ) -> SpannedEncodingResult<()> {
        match statement {
            vir_low::Statement::Comment(_)
            | vir_low::Statement::LogEvent(_)
            | vir_low::Statement::Assign(_) => {
                statements.push(statement);
            }
            vir_low::Statement::Label(statement) => {
                self.ssa_state.save_state_at_label(statement.label.clone());
                statements.push(vir_low::Statement::Label(statement));
            }
            vir_low::Statement::Assume(statement) => {
                assert!(statement.expression.is_pure());
                let expression = self.encode_pure_expression(
                    statements,
                    statement.expression,
                    None,
                    statement.position,
                )?;
                statements.push(vir_low::Statement::assume(expression, statement.position));
            }
            vir_low::Statement::Assert(statement) => {
                self.encode_expression_assert(
                    statements,
                    statement.expression,
                    statement.position,
                    None,
                )?;
            }
            vir_low::Statement::Inhale(statement) => {
                statements.push(vir_low::Statement::comment(format!("{statement}")));
                self.encode_expression_inhale(
                    statements,
                    statement.expression,
                    statement.position,
                    None,
                )?;
            }
            vir_low::Statement::Exhale(statement) => {
                statements.push(vir_low::Statement::comment(format!("{statement}")));
                let evaluation_state = self.fresh_label();
                self.ssa_state.save_state_at_label(evaluation_state.clone());
                self.encode_expression_exhale(
                    statements,
                    statement.expression,
                    statement.position,
                    &evaluation_state,
                )?;
            }
            vir_low::Statement::Fold(_) => todo!(),
            vir_low::Statement::Unfold(_) => todo!(),
            vir_low::Statement::ApplyMagicWand(_) => {
                unimplemented!("magic wands are not supported yet");
            }
            vir_low::Statement::MethodCall(statement) => {
                unreachable!("method call: {}", statement);
            }
            vir_low::Statement::Conditional(conditional) => {
                unreachable!("conditional: {}", conditional);
            }
            vir_low::Statement::MaterializePredicate(statement) => {
                unreachable!("materialize predicate: {statement}");
            }
        }
        Ok(())
    }
}
