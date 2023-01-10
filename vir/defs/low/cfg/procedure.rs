use crate::{
    common::display,
    low::ast::{
        expression::Expression, position::Position, statement::Statement, variable::VariableDecl,
    },
};
use std::collections::BTreeMap;

#[display(
    fmt = "procedure {} {{\n{}\n{}}}\n",
    name,
    "display::foreach!(\"  var {};\n\", locals)",
    "display::foreach2!(\"    label {}\n{}\", basic_blocks.keys(), basic_blocks.values())"
)]
pub struct ProcedureDecl {
    pub name: String,
    pub locals: Vec<VariableDecl>,
    pub custom_labels: Vec<Label>,
    pub entry: Label,
    pub exit: Label,
    pub basic_blocks: BTreeMap<Label, BasicBlock>,
    pub position: Position,
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

#[display(fmt = "label {}", name)]
#[derive(PartialOrd, Ord)]
pub struct Label {
    pub name: String,
}

pub enum Successor {
    Return,
    Goto(Label),
    #[display(fmt = "switch")]
    GotoSwitch(Vec<(Expression, Label)>),
}
