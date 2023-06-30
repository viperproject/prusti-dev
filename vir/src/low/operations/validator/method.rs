use crate::{
    common::validator::{ValidationError, Validator},
    low::cfg::method::*,
};

impl Validator for MethodDecl {
    fn validate(&self) -> Result<(), ValidationError> {
        for pre in &self.pres {
            pre.validate()?;
        }
        for post in &self.posts {
            post.validate()?;
        }
        if let Some(body) = &self.body {
            for statement in body {
                statement.validate()?;
            }
        }
        Ok(())
    }
}
