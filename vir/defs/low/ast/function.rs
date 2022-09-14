use super::{expression::Expression, ty::Type, variable::VariableDecl};
use crate::common::display;

pub enum FunctionKind {
    MemoryBlockBytes,
    CallerFor,
    Snap,
    SnapRange,
}

#[display(
    fmt = "function<{}> {}({}): {}\n{}{}{}\n",
    kind,
    name,
    "display::cjoin(parameters)",
    return_type,
    "display::foreach!(\"  requires {}\n\", pres)",
    "display::foreach!(\"  ensures {}\n\", posts)",
    "display::option!(body, \"{{ {} }}\n\", \"\")"
)]
pub struct FunctionDecl {
    pub name: String,
    pub kind: FunctionKind,
    pub parameters: Vec<VariableDecl>,
    pub return_type: Type,
    pub pres: Vec<Expression>,
    pub posts: Vec<Expression>,
    pub body: Option<Expression>,
}
