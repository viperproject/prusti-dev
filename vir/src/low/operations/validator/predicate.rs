use crate::{
    common::validator::{ValidationError, Validator},
    low::ast::predicate::*,
};

impl Validator for PredicateDecl {
    fn validate(&self) -> Result<(), ValidationError> {
        if let Some(body) = &self.body {
            body.validate()?;
        }
        Ok(())
    }
}
