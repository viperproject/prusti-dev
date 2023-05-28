use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::low::{self as vir_low};

pub(super) struct BlockBuilder {
    pub(super) statements: Vec<vir_low::Statement>,
    pub(super) successors: Vec<vir_low::Label>,
    pub(super) current_materialization_point: usize,
}

impl BlockBuilder {
    pub(super) fn new(successors: Vec<vir_low::Label>) -> SpannedEncodingResult<Self> {
        let builder = Self {
            statements: Vec::new(),
            successors,
            current_materialization_point: 0,
        };
        Ok(builder)
    }

    pub(super) fn add_statement(
        &mut self,
        statement: vir_low::Statement,
    ) -> SpannedEncodingResult<()> {
        self.statements.push(statement);
        Ok(())
    }

    pub(super) fn add_statements(
        &mut self,
        statements: Vec<vir_low::Statement>,
    ) -> SpannedEncodingResult<()> {
        self.statements.extend(statements);
        Ok(())
    }

    pub(super) fn set_materialization_point(&mut self) -> SpannedEncodingResult<()> {
        self.current_materialization_point = self.statements.len();
        Ok(())
    }

    pub(super) fn add_statements_at_materialization_point(
        &mut self,
        statements: Vec<vir_low::Statement>,
    ) -> SpannedEncodingResult<()> {
        self.statements.splice(
            self.current_materialization_point..self.current_materialization_point,
            statements,
        );
        Ok(())
    }
}

pub trait StatementsBuilder {
    fn add_statement(&mut self, statement: vir_low::Statement) -> SpannedEncodingResult<()>;
}

impl StatementsBuilder for BlockBuilder {
    fn add_statement(&mut self, statement: vir_low::Statement) -> SpannedEncodingResult<()> {
        BlockBuilder::add_statement(self, statement)
    }
}

impl StatementsBuilder for Vec<vir_low::Statement> {
    fn add_statement(&mut self, statement: vir_low::Statement) -> SpannedEncodingResult<()> {
        self.push(statement);
        Ok(())
    }
}
