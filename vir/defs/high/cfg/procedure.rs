use super::super::ast::{
    expression::{Expression, Local},
    statement::Statement,
};
use crate::common::display;
use std::collections::BTreeMap;

#[display(
    fmt = "procedure {}({})\n    returns ({})\n{{\n{}}}",
    name,
    "display::cjoin(parameters)",
    "display::cjoin(returns)",
    "display::foreach2!(\"    label {}\n{}\", basic_blocks.keys(), basic_blocks.values())"
)]
pub struct ProcedureDecl {
    pub name: String,
    /// We use `Local` instead of `VariableDecl` because we need to know
    /// positions.
    pub parameters: Vec<Local>,
    /// We use `Local` instead of `VariableDecl` because we need to know
    /// positions.
    pub returns: Vec<Local>,
    pub entry: BasicBlockId,
    pub basic_blocks: BTreeMap<BasicBlockId, BasicBlock>,
}

#[derive(PartialOrd, Ord, derive_more::Constructor, derive_more::AsRef)]
pub struct BasicBlockId {
    pub name: String,
}

#[display(
    fmt = "{}\n    {}\n",
    "display::foreach!(\"    {}\n\", statements)",
    successor
)]
pub struct BasicBlock {
    pub statements: Vec<Statement>,
    pub successor: Successor,
}

pub enum Successor {
    Return,
    Goto(BasicBlockId),
    #[display(fmt = "switch")]
    GotoSwitch(Vec<(Expression, BasicBlockId)>),
}
