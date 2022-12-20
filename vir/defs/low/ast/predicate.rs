use super::{expression::Expression, variable::VariableDecl};
use crate::common::display;

pub enum PredicateKind {
    MemoryBlock,
    Owned,
    WithoutSnapshot,
}

#[display(
    fmt = "predicate<{}> {}({}){}\n",
    kind,
    "name",
    "display::cjoin(parameters)",
    "display::option!(body, \" {{\n  {}\n}}\", \";\")"
)]
pub struct PredicateDecl {
    pub name: String,
    pub kind: PredicateKind,
    pub parameters: Vec<VariableDecl>,
    pub body: Option<Expression>,
}
