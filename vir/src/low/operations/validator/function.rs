use crate::{
    common::validator::{ValidationError, Validator},
    low::ast::function::*,
};

impl Validator for FunctionDecl {
    fn validate(&self) -> Result<(), ValidationError> {
        for pre in &self.pres {
            pre.validate()?;
        }
        for post in &self.posts {
            post.validate()?;
        }
        if let Some(body) = &self.body {
            body.validate()?;
        }
        Ok(())
    }
}
