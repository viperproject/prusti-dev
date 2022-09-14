use log::debug;

use crate::{common::check_mode::CheckMode, high as vir_high};
use std::collections::BTreeMap;

#[must_use]
pub struct ProcedureBuilder {
    name: String,
    check_mode: CheckMode,
    position: vir_high::Position,
    non_aliased_places: Vec<vir_high::Expression>,
    pre_statements: Vec<vir_high::Statement>,
    post_success_statements: Vec<vir_high::Statement>,
    post_statements: Vec<vir_high::Statement>,
    start_label: vir_high::BasicBlockId,
    entry_label: Option<vir_high::BasicBlockId>,
    return_label: vir_high::BasicBlockId,
    is_return_label_used: bool,
    resume_panic_label: vir_high::BasicBlockId,
    is_resume_panic_label_used: bool,
    /// Note: this statements are emitted only if resume panic label is used.
    resume_panic_statements: Vec<vir_high::Statement>,
    end_label: vir_high::BasicBlockId,
    basic_blocks: BTreeMap<vir_high::BasicBlockId, vir_high::BasicBlock>,
}

#[must_use]
pub struct BasicBlockBuilder<'a> {
    procedure_builder: &'a mut ProcedureBuilder,
    id: vir_high::BasicBlockId,
    statements: Vec<vir_high::Statement>,
    successor: SuccessorBuilder,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SuccessorExitKind {
    Return,
    ResumePanic,
}

#[must_use]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SuccessorBuilder {
    Exit(SuccessorExitKind),
    Jump(vir_high::Successor),
    Undefined,
}

impl ProcedureBuilder {
    pub fn new(
        name: String,
        check_mode: CheckMode,
        position: vir_high::Position,
        pre_statements: Vec<vir_high::Statement>,
        post_success_statements: Vec<vir_high::Statement>,
        post_statements: Vec<vir_high::Statement>,
        resume_panic_statements: Vec<vir_high::Statement>,
    ) -> Self {
        Self {
            name,
            check_mode,
            position,
            non_aliased_places: Vec::new(),
            pre_statements,
            post_success_statements,
            post_statements,
            start_label: vir_high::BasicBlockId::new("start_label".to_string()),
            entry_label: None,
            return_label: vir_high::BasicBlockId::new("return_label".to_string()),
            is_return_label_used: false,
            resume_panic_label: vir_high::BasicBlockId::new("resume_panic_label".to_string()),
            is_resume_panic_label_used: false,
            resume_panic_statements,
            end_label: vir_high::BasicBlockId::new("end_label".to_string()),
            basic_blocks: Default::default(),
        }
    }
    pub fn build(self) -> vir_high::ProcedureDecl {
        let mut basic_blocks = self.basic_blocks;
        let allocate = vir_high::BasicBlock {
            statements: self.pre_statements,
            successor: vir_high::Successor::Goto(self.entry_label.unwrap()),
        };
        assert!(basic_blocks
            .insert(self.start_label.clone(), allocate)
            .is_none());
        let deallocate = vir_high::BasicBlock {
            statements: self.post_success_statements,
            successor: vir_high::Successor::Goto(self.end_label.clone()),
        };
        if self.is_return_label_used {
            assert!(basic_blocks.insert(self.return_label, deallocate).is_none());
        }
        if self.is_resume_panic_label_used {
            let block = vir_high::BasicBlock {
                statements: self.resume_panic_statements,
                successor: vir_high::Successor::Goto(self.end_label.clone()),
            };
            assert!(basic_blocks
                .insert(self.resume_panic_label, block)
                .is_none());
        }
        let end_block = vir_high::BasicBlock {
            statements: self.post_statements,
            successor: vir_high::Successor::Exit,
        };
        assert!(basic_blocks
            .insert(self.end_label.clone(), end_block)
            .is_none());
        vir_high::ProcedureDecl {
            name: self.name,
            check_mode: self.check_mode,
            position: self.position,
            non_aliased_places: self.non_aliased_places,
            entry: self.start_label,
            exit: self.end_label,
            basic_blocks,
        }
    }
    pub fn add_non_aliased_place(&mut self, place: vir_high::Expression) {
        self.non_aliased_places.push(place);
    }
    pub fn add_alloc_statement(&mut self, statement: vir_high::Statement) {
        self.pre_statements.push(statement);
    }
    pub fn add_dealloc_statement(&mut self, statement: vir_high::Statement) {
        self.post_success_statements.push(statement);
    }
    pub fn set_entry(&mut self, entry_label: vir_high::BasicBlockId) {
        assert!(self.entry_label.is_none());
        self.entry_label = Some(entry_label);
    }
    pub fn create_basic_block_builder(&mut self, id: vir_high::BasicBlockId) -> BasicBlockBuilder {
        BasicBlockBuilder {
            procedure_builder: self,
            id,
            statements: Vec::new(),
            successor: SuccessorBuilder::Undefined,
        }
    }
    pub fn name(&self) -> &str {
        &self.name
    }
}

impl<'a> BasicBlockBuilder<'a> {
    #[tracing::instrument(level = "debug", skip(self), fields(block_id = ?self.id))]
    pub fn build(self) {
        let successor = match self.successor {
            SuccessorBuilder::Exit(SuccessorExitKind::Return) => {
                self.procedure_builder.is_return_label_used = true;
                vir_high::Successor::Goto(self.procedure_builder.return_label.clone())
            }
            SuccessorBuilder::Exit(SuccessorExitKind::ResumePanic) => {
                self.procedure_builder.is_resume_panic_label_used = true;
                vir_high::Successor::Goto(self.procedure_builder.resume_panic_label.clone())
            }
            SuccessorBuilder::Jump(successor) => successor,
            SuccessorBuilder::Undefined => unreachable!(),
        };
        let block = vir_high::BasicBlock {
            statements: self.statements,
            successor,
        };
        assert!(self
            .procedure_builder
            .basic_blocks
            .insert(self.id, block)
            .is_none());
    }
    pub fn add_comment(&mut self, comment: String) {
        self.statements.push(vir_high::Statement::comment(comment));
    }
    pub fn set_successor(&mut self, successor: SuccessorBuilder) {
        assert!(self.successor == SuccessorBuilder::Undefined);
        self.successor = successor;
    }
    pub fn set_successor_jump(&mut self, successor: vir_high::Successor) {
        self.set_successor(SuccessorBuilder::Jump(successor));
    }
    pub fn set_successor_exit(&mut self, successor: SuccessorExitKind) {
        self.set_successor(SuccessorBuilder::Exit(successor));
    }
    pub fn create_basic_block_builder(&mut self, id: vir_high::BasicBlockId) -> BasicBlockBuilder {
        BasicBlockBuilder {
            procedure_builder: self.procedure_builder,
            id,
            statements: Vec::new(),
            successor: SuccessorBuilder::Undefined,
        }
    }
}

impl SuccessorBuilder {
    pub fn exit_return() -> Self {
        Self::Exit(SuccessorExitKind::Return)
    }
    pub fn exit_resume_panic() -> Self {
        Self::Exit(SuccessorExitKind::ResumePanic)
    }
    pub fn jump(successor: vir_high::Successor) -> Self {
        Self::Jump(successor)
    }
}

pub trait StatementSequenceBuilder {
    fn add_statement(&mut self, statement: vir_high::Statement);
    fn add_statements(&mut self, statements: Vec<vir_high::Statement>) {
        for statement in statements {
            self.add_statement(statement);
        }
    }
}

impl<'a> StatementSequenceBuilder for BasicBlockBuilder<'a> {
    fn add_statement(&mut self, statement: vir_high::Statement) {
        statement.check_no_default_position();
        self.statements.push(statement);
    }
}

impl StatementSequenceBuilder for Vec<vir_high::Statement> {
    fn add_statement(&mut self, statement: vir_high::Statement) {
        statement.check_no_default_position();
        self.push(statement);
    }
}
