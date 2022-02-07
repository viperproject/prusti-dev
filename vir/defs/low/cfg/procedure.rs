use crate::{
    common::display,
    low::ast::{expression::Expression, statement::Statement, variable::VariableDecl},
};

#[display(
    fmt = "procedure {} {{\n{}\n{}}}\n",
    name,
    "display::foreach!(\"  var {};\n\", locals)",
    "display::foreach!(\"{}\n\", basic_blocks)"
)]
pub struct ProcedureDecl {
    pub name: String,
    pub locals: Vec<VariableDecl>,
    pub basic_blocks: Vec<BasicBlock>,
}

#[display(
    fmt = "  block {} {{\n{}\n    {}\n  }}\n",
    label,
    "display::foreach!(\"    {};\n\", statements)",
    successor
)]
pub struct BasicBlock {
    pub label: Label,
    pub statements: Vec<Statement>,
    pub successor: Successor,
}

#[display(fmt = "label {}", name)]
pub struct Label {
    pub name: String,
}

pub enum Successor {
    Return,
    Goto(Label),
    #[display(fmt = "switch")]
    GotoSwitch(Vec<(Expression, Label)>),
}
