mod common;
mod ty;

pub trait WithLifetimes {
    fn get_lifetimes(&self) -> Vec<super::super::ast::ty::LifetimeConst>;
}
