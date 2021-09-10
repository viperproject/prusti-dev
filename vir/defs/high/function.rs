use super::variable::VariableDecl;
use super::expression::Expression;
use super::typ::Type;

pub struct FunctionDecl {
    pub name: String,
    pub parameters: Vec<VariableDecl>,
    pub return_type: Type,
    pub pres: Vec<Expression>,
    pub posts: Vec<Expression>,
    pub body: Option<Expression>,
}