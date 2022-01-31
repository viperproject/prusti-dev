use super::super::{ast, cfg};
use std::collections::BTreeMap;

#[must_use]
pub struct ProcedureBuilder {
    name: String,
    parameters: Vec<ast::expression::Local>,
    returns: Vec<ast::expression::Local>,
    entry: Option<cfg::BasicBlockId>,
    basic_blocks: BTreeMap<cfg::BasicBlockId, cfg::BasicBlock>,
}

#[must_use]
pub struct BasicBlockBuilder<'a> {
    procedure_builder: &'a mut ProcedureBuilder,
    id: cfg::BasicBlockId,
    statements: Vec<ast::Statement>,
    successor: Option<cfg::Successor>,
}

impl ProcedureBuilder {
    pub fn new(
        name: String,
        parameters: Vec<ast::expression::Local>,
        returns: Vec<ast::expression::Local>,
    ) -> Self {
        Self {
            name,
            parameters,
            returns,
            entry: None,
            basic_blocks: Default::default(),
        }
    }
    pub fn build(self) -> cfg::ProcedureDecl {
        cfg::ProcedureDecl {
            name: self.name,
            parameters: self.parameters,
            returns: self.returns,
            entry: self.entry.unwrap(),
            basic_blocks: self.basic_blocks,
        }
    }
    pub fn set_entry(&mut self, entry: cfg::BasicBlockId) {
        assert!(self.entry.is_none());
        self.entry = Some(entry);
    }
    pub fn create_basic_block_builder(&mut self, id: cfg::BasicBlockId) -> BasicBlockBuilder {
        BasicBlockBuilder {
            procedure_builder: self,
            id,
            statements: Vec::new(),
            successor: None,
        }
    }
}

impl<'a> BasicBlockBuilder<'a> {
    pub fn build(self) {
        eprintln!("Building: {:?}", self.id);
        let block = cfg::BasicBlock {
            statements: self.statements,
            successor: self.successor.unwrap(),
        };
        assert!(self
            .procedure_builder
            .basic_blocks
            .insert(self.id, block)
            .is_none());
    }
    pub fn add_comment(&mut self, comment: String) {
        self.statements.push(ast::Statement::comment(comment));
    }
    pub fn add_statement(&mut self, statement: ast::Statement) {
        self.statements.push(statement);
    }
    pub fn set_successor(&mut self, successor: cfg::Successor) {
        assert!(self.successor.is_none());
        self.successor = Some(successor);
    }
}
