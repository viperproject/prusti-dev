use crate::{
    common::validator::{ValidationError, Validator},
    low::program::Program,
};

impl Validator for Program {
    fn validate(&self) -> Result<(), ValidationError> {
        for domain in &self.domains {
            domain.validate()?;
        }
        for predicate in &self.predicates {
            predicate.validate()?;
        }
        for function in &self.functions {
            function.validate()?;
        }
        for method in &self.methods {
            method.validate()?;
        }
        for procedure in &self.procedures {
            procedure.validate()?;
        }
        Ok(())
    }
}
