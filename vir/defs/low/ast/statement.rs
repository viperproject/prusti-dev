use super::{expression::Expression, position::Position};
use crate::common::display;

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::From, derive_more::IsVariant)]
pub enum Statement {
    Comment(Comment),
    Inhale(Inhale),
    Exhale(Exhale),
    MethodCall(MethodCall),
}

#[display(fmt = "// {}", comment)]
pub struct Comment {
    pub comment: String,
}

#[display(fmt = "inhale {}", expression)]
pub struct Inhale {
    pub expression: Expression,
    pub position: Position,
}

#[display(fmt = "exhale {}", expression)]
pub struct Exhale {
    pub expression: Expression,
    pub position: Position,
}

#[display(
    fmt = "{} := call {}({})",
    "display::cjoin(targets)",
    method_name,
    "display::cjoin(arguments)"
)]
pub struct MethodCall {
    pub method_name: String,
    pub arguments: Vec<Expression>,
    pub targets: Vec<Expression>,
}
