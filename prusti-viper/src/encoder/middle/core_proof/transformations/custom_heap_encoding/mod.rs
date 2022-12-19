use crate::encoder::{errors::SpannedEncodingResult, middle::core_proof::lowerer::LoweringResult};
use vir_crate::{
    common::{cfg::Cfg, check_mode::CheckMode, graphviz::ToGraphviz},
    low::{self as vir_low, operations::ty::Typed},
    middle as vir_mid,
};

pub(in super::super) fn custom_heap_encoding(
    result: &mut LoweringResult,
) -> SpannedEncodingResult<()> {
    let mut procedures = Vec::new();
    for mut procedure in std::mem::take(&mut result.procedures) {
        let mut heap_encoder = HeapEncoder {};
        for block in &mut procedure.basic_blocks {
            let mut statements = Vec::new();
            for statement in std::mem::take(&mut block.statements) {
                heap_encoder.encode_statement(&mut statements, statement)?;
            }
        }
        procedures.push(procedure);
    }
    Ok(())
}

struct HeapEncoder {}

impl HeapEncoder {
    fn encode_statement(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        statement: vir_low::Statement,
    ) -> SpannedEncodingResult<()> {
        match statement {
            vir_low::Statement::Comment(_)
            | vir_low::Statement::Label(_)
            | vir_low::Statement::LogEvent(_)
            | vir_low::Statement::Assume(_)
            | vir_low::Statement::Assert(_)
            | vir_low::Statement::Assign(_) => {
                statements.push(statement);
            }
            vir_low::Statement::Inhale(inhale) => {
                self.encode_expression_inhale(statements, inhale.expression, inhale.position)?;
            }
            vir_low::Statement::Exhale(_) => todo!(),
            vir_low::Statement::Fold(_) => todo!(),
            vir_low::Statement::Unfold(_) => todo!(),
            vir_low::Statement::ApplyMagicWand(_) => {
                unimplemented!("magic wands are not supported yet");
            }
            vir_low::Statement::MethodCall(_) => todo!(),
            vir_low::Statement::Conditional(mut conditional) => {
                let mut then_statements = Vec::new();
                for statement in std::mem::take(&mut conditional.then_branch) {
                    self.encode_statement(&mut then_statements, statement)?;
                }
                let mut else_statements = Vec::new();
                for statement in std::mem::take(&mut conditional.else_branch) {
                    self.encode_statement(&mut else_statements, statement)?;
                }
                statements.push(vir_low::Statement::Conditional(
                    vir_low::ast::statement::Conditional {
                        then_branch: then_statements,
                        else_branch: else_statements,
                        ..conditional
                    },
                ));
            }
        }
        Ok(())
    }

    fn encode_expression_inhale(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        expression: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }
}
