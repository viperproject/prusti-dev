use super::{expression::Expression, ty::Type, variable::VariableDecl};
use crate::common::display;

#[display(
    fmt = "function {}<{}>({}): {}\n{}{}{{ {} }}\n",
    name,
    "display::cjoin(type_arguments)",
    "display::cjoin(parameters)",
    return_type,
    "display::foreach!(\"  requires {}\n\", pres)",
    "display::foreach!(\"  ensures {}\n\", pres)",
    "display::option!(body, \"{{ {} }}\n\", \"\")"
)]
pub struct FunctionDecl {
    pub name: String,
    pub type_arguments: Vec<Type>,
    pub parameters: Vec<VariableDecl>,
    pub return_type: Type,
    pub pres: Vec<Expression>,
    pub posts: Vec<Expression>,
    pub body: Option<Expression>,
}
