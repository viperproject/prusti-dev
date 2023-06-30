use crate::{
    common::validator::{ValidationError, Validator},
    low::ast::statement::*,
};

impl Validator for Statement {
    fn validate(&self) -> Result<(), ValidationError> {
        match self {
            Statement::Comment(statement) => statement.validate(),
            Statement::Label(statement) => statement.validate(),
            Statement::LogEvent(statement) => statement.validate(),
            Statement::Assume(statement) => statement.validate(),
            Statement::Assert(statement) => statement.validate(),
            Statement::Inhale(statement) => statement.validate(),
            Statement::Exhale(statement) => statement.validate(),
            Statement::Fold(statement) => statement.validate(),
            Statement::Unfold(statement) => statement.validate(),
            Statement::ApplyMagicWand(statement) => statement.validate(),
            Statement::MethodCall(statement) => statement.validate(),
            Statement::Assign(statement) => statement.validate(),
            Statement::Conditional(statement) => statement.validate(),
            Statement::MaterializePredicate(statement) => statement.validate(),
            Statement::CaseSplit(statement) => statement.validate(),
        }
    }
}

impl Validator for Comment {
    fn validate(&self) -> Result<(), ValidationError> {
        Ok(())
    }
}

impl Validator for Label {
    fn validate(&self) -> Result<(), ValidationError> {
        Ok(())
    }
}

impl Validator for LogEvent {
    fn validate(&self) -> Result<(), ValidationError> {
        Ok(())
    }
}

impl Validator for Assume {
    fn validate(&self) -> Result<(), ValidationError> {
        self.expression.validate()?;
        Ok(())
    }
}

impl Validator for Assert {
    fn validate(&self) -> Result<(), ValidationError> {
        self.expression.validate()?;
        Ok(())
    }
}

impl Validator for Inhale {
    fn validate(&self) -> Result<(), ValidationError> {
        self.expression.validate()?;
        Ok(())
    }
}

impl Validator for Exhale {
    fn validate(&self) -> Result<(), ValidationError> {
        self.expression.validate()?;
        Ok(())
    }
}

impl Validator for Fold {
    fn validate(&self) -> Result<(), ValidationError> {
        self.expression.validate()?;
        Ok(())
    }
}

impl Validator for Unfold {
    fn validate(&self) -> Result<(), ValidationError> {
        self.expression.validate()?;
        Ok(())
    }
}

impl Validator for ApplyMagicWand {
    fn validate(&self) -> Result<(), ValidationError> {
        self.expression.validate()?;
        Ok(())
    }
}

impl Validator for MethodCall {
    fn validate(&self) -> Result<(), ValidationError> {
        for argument in &self.arguments {
            argument.validate()?;
        }
        for target in &self.targets {
            target.validate()?;
        }
        Ok(())
    }
}

impl Validator for Assign {
    fn validate(&self) -> Result<(), ValidationError> {
        self.value.validate()?;
        Ok(())
    }
}

impl Validator for Conditional {
    fn validate(&self) -> Result<(), ValidationError> {
        self.guard.validate()?;
        for statement in &self.then_branch {
            statement.validate()?;
        }
        for statement in &self.else_branch {
            statement.validate()?;
        }
        Ok(())
    }
}

impl Validator for MaterializePredicate {
    fn validate(&self) -> Result<(), ValidationError> {
        self.predicate.validate()?;
        Ok(())
    }
}

impl Validator for CaseSplit {
    fn validate(&self) -> Result<(), ValidationError> {
        self.expression.validate()?;
        Ok(())
    }
}
