use super::{expression::Expression, variable::VariableDecl};
use crate::common::display;

#[display(
    fmt = "predicate {}({}){}\n",
    "name",
    "display::cjoin(parameters)",
    "display::option!(body, \" {{\n  {}\n}}\", \";\")"
)]
pub struct PredicateDecl {
    pub name: String,
    pub parameters: Vec<VariableDecl>,
    pub body: Option<Expression>,
}
