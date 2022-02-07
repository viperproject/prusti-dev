use viper::AstFactory;

mod ast;
mod cfg;
mod domain;
mod program;

pub trait ToViper<'v, T> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> T;
}

pub trait ToViperDecl<'v, T> {
    fn to_viper_decl(&self, ast: &AstFactory<'v>) -> T;
}
