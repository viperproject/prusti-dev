use crate::{
    common::validator::{ValidationError, Validator},
    low::domain::*,
};

impl Validator for DomainDecl {
    fn validate(&self) -> Result<(), ValidationError> {
        for function in &self.functions {
            function.validate()?;
        }
        for axiom in &self.axioms {
            axiom.validate()?;
        }
        for rule in &self.rewrite_rules {
            rule.validate()?;
        }
        Ok(())
    }
}

impl Validator for DomainFunctionDecl {
    fn validate(&self) -> Result<(), ValidationError> {
        Ok(())
    }
}

impl Validator for DomainAxiomDecl {
    fn validate(&self) -> Result<(), ValidationError> {
        self.body.validate()?;
        Ok(())
    }
}

impl Validator for DomainRewriteRuleDecl {
    fn validate(&self) -> Result<(), ValidationError> {
        if let Some(triggers) = &self.triggers {
            for trigger in triggers {
                trigger.validate()?;
            }
        }
        self.source.validate()?;
        self.target.validate()?;
        Ok(())
    }
}
