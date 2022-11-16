use viper::AstFactory;

mod ast;
mod cfg;
mod domain;
mod program;

#[derive(Clone, Copy, Default, Debug)]
pub struct Context {
    inside_trigger: bool,
}

impl Context {
    pub fn set_inside_trigger(mut self) -> Self {
        self.inside_trigger = true;
        self
    }
}

pub trait ToViper<'v, T> {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> T;
}

pub trait ToViperDecl<'v, T> {
    fn to_viper_decl(&self, context: Context, ast: &AstFactory<'v>) -> T;
}
