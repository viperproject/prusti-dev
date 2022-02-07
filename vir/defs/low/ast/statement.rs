use super::{expression::Expression, position::Position};
use crate::common::display;

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::From, derive_more::IsVariant)]
pub enum Statement {
    Comment(Comment),
    Assume(Assume),
    Assert(Assert),
    Inhale(Inhale),
    Exhale(Exhale),
    Fold(Fold),
    Unfold(Unfold),
    MethodCall(MethodCall),
}

#[display(fmt = "// {}", comment)]
pub struct Comment {
    pub comment: String,
}

#[display(fmt = "assume {}", expression)]
/// Assume a **pure** assertion.
pub struct Assume {
    pub expression: Expression,
    pub position: Position,
}

#[display(fmt = "assert {}", expression)]
/// Assert a **pure** assertion.
pub struct Assert {
    pub expression: Expression,
    pub position: Position,
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

#[display(fmt = "fold {}", expression)]
pub struct Fold {
    pub expression: Expression,
    pub position: Position,
}

#[display(fmt = "unfold {}", expression)]
pub struct Unfold {
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
    pub position: Position,
}
