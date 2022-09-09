mod common;
mod ty;

pub trait WithConstArguments {
    fn get_const_arguments(&self) -> Vec<super::super::ast::expression::Expression>;
}
