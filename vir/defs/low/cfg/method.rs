use crate::{
    common::display,
    low::ast::{expression::Expression, statement::Statement, variable::VariableDecl},
};

#[display(
    fmt = "method {} ({})\n  returns ({})\n{}{}{}",
    name,
    "display::cjoin(parameters)",
    "display::cjoin(targets)",
    "display::foreach!(\"  requires {}\n\", pres)",
    "display::foreach!(\"  ensures {}\n\", posts)",
    "display::option_foreach!(body, \"{{\n{}}}\", \"  {}\n\", \"\")"
)]
/// A Viper method that performs a specific action such as havocking the given
/// variable. Its body can have at most one basic block.
pub struct MethodDecl {
    pub name: String,
    pub parameters: Vec<VariableDecl>,
    pub targets: Vec<VariableDecl>,
    pub pres: Vec<Expression>,
    pub posts: Vec<Expression>,
    pub body: Option<Vec<Statement>>,
}
