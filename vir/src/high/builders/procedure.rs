use crate::high as vir_high;
use std::collections::BTreeMap;

#[must_use]
pub struct ProcedureBuilder {
    name: String,
    pre_statements: Vec<vir_high::Statement>,
    post_statements: Vec<vir_high::Statement>,
    start_label: vir_high::BasicBlockId,
    entry_label: Option<vir_high::BasicBlockId>,
    return_label: vir_high::BasicBlockId,
    resume_panic_label: vir_high::BasicBlockId,
    is_resume_panic_label_used: bool,
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
        allocate_parameters: Vec<vir_high::Statement>,
        allocate_returns: Vec<vir_high::Statement>,
        assume_preconditions: Vec<vir_high::Statement>,
        deallocate_parameters: Vec<vir_high::Statement>,
        deallocate_returns: Vec<vir_high::Statement>,
        assert_postconditions: Vec<vir_high::Statement>,
    ) -> Self {
        let mut pre_statements = allocate_parameters;
        pre_statements.extend(assume_preconditions);
        pre_statements.extend(allocate_returns);
        let mut post_statements = assert_postconditions;
        post_statements.extend(deallocate_parameters);
        post_statements.extend(deallocate_returns);
        Self {
            name,
            pre_statements,
            post_statements,
            start_label: vir_high::BasicBlockId::new("start_label".to_string()),
            entry_label: None,
            return_label: vir_high::BasicBlockId::new("return_label".to_string()),
            resume_panic_label: vir_high::BasicBlockId::new("resume_panic_label".to_string()),
            is_resume_panic_label_used: false,
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
            statements: self.post_statements,
            successor: vir_high::Successor::Goto(self.end_label.clone()),
        };
        assert!(basic_blocks.insert(self.return_label, deallocate).is_none());
        if self.is_resume_panic_label_used {
            let leak = vir_high::BasicBlock {
                statements: vec![vir_high::Statement::leak_all()],
                successor: vir_high::Successor::Goto(self.end_label.clone()),
            };
            assert!(basic_blocks.insert(self.resume_panic_label, leak).is_none());
        }
        let end_block = vir_high::BasicBlock {
            statements: Vec::new(),
            successor: vir_high::Successor::Exit,
        };
        assert!(basic_blocks.insert(self.end_label, end_block).is_none());
        vir_high::ProcedureDecl {
            name: self.name,
            entry: self.start_label,
            basic_blocks,
        }
    }
    pub fn add_alloc_statement(&mut self, statement: vir_high::Statement) {
        self.pre_statements.push(statement);
    }
    pub fn add_dealloc_statement(&mut self, statement: vir_high::Statement) {
        self.post_statements.push(statement);
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
}

impl<'a> BasicBlockBuilder<'a> {
    pub fn build(self) {
        debug!("Building: {:?}", self.id);
        let successor = match self.successor {
            SuccessorBuilder::Exit(SuccessorExitKind::Return) => {
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
    pub fn add_statement(&mut self, statement: vir_high::Statement) {
        statement.check_no_default_position();
        self.statements.push(statement);
    }
    pub fn add_statements(&mut self, statements: Vec<vir_high::Statement>) {
        for statement in statements {
            self.add_statement(statement);
        }
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
