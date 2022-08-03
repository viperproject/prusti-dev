use super::super::ast::{
    expression::{Expression, Local},
    statement::Statement,
};
use crate::common::{check_mode::CheckMode, display};
use std::collections::BTreeMap;

#[display(
    fmt = "procedure({}) {}\n{{\n{}}}",
    check_mode,
    name,
    "display::foreach2!(\"    label {}\n{}\", basic_blocks.keys(), basic_blocks.values())"
)]
pub struct ProcedureDecl {
    pub name: String,
    pub check_mode: CheckMode,
    pub entry: BasicBlockId,
    pub exit: BasicBlockId,
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
    Exit,
    Goto(BasicBlockId),
    #[display(fmt = "switch")]
    GotoSwitch(Vec<(Expression, BasicBlockId)>),
    #[display(fmt = "non-det-switch")]
    NonDetChoice(BasicBlockId, BasicBlockId),
}
