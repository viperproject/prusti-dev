use super::{expression::Expression, typ::Type, variable::VariableDecl};

pub struct FunctionDecl {
    pub name: String,
    pub parameters: Vec<VariableDecl>,
    pub return_type: Type,
    pub pres: Vec<Expression>,
    pub posts: Vec<Expression>,
    pub body: Option<Expression>,
}
