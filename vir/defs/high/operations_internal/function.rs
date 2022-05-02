use super::super::ast::{
    expression::visitors::ExpressionFallibleWalker, function::FunctionDecl, ty::Type,
};

impl FunctionDecl {
    pub fn walk_types<Error, F>(&self, mut callback: F) -> Result<(), Error>
    where
        F: for<'a> FnMut(&'a Type) -> Result<(), Error>,
    {
        for parameter in &self.parameters {
            callback(&parameter.ty)?
        }
        callback(&self.return_type)?;
        struct Walker<F, Error>
        where
            F: for<'a> FnMut(&'a Type) -> Result<(), Error>,
        {
            callback: F,
        }
        impl<F, Error> ExpressionFallibleWalker for Walker<F, Error>
        where
            F: for<'a> FnMut(&'a Type) -> Result<(), Error>,
        {
            type Error = Error;
            fn fallible_walk_type(&mut self, ty: &Type) -> Result<(), Error> {
                (self.callback)(ty)
            }
        }
        let mut walker = Walker { callback };
        for expression in self.pres.iter().chain(&self.posts).chain(&self.body) {
            walker.fallible_walk_expression(expression)?;
        }
        Ok(())
    }
}
