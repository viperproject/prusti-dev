use crate::{
    common::validator::{ValidationError, Validator},
    low::cfg::procedure::*,
};

impl Validator for ProcedureDecl {
    fn validate(&self) -> Result<(), ValidationError> {
        for (label, block) in &self.basic_blocks {
            match block.validate() {
                Ok(_) => {}
                Err(mut e) => {
                    e.add_context(format!("in block {}", label));
                    e.add_context(format!("in procedure {}", self.name));
                    return Err(e);
                }
            }
        }
        Ok(())
    }
}

impl Validator for BasicBlock {
    fn validate(&self) -> Result<(), ValidationError> {
        for statement in &self.statements {
            match statement.validate() {
                Ok(_) => {}
                Err(mut e) => {
                    e.add_context(format!("in statement {}", statement));
                    return Err(e);
                }
            }
        }
        self.successor.validate()?;
        Ok(())
    }
}

impl Validator for Successor {
    fn validate(&self) -> Result<(), ValidationError> {
        match self {
            Successor::Return => {}
            Successor::Goto(_) => {}
            Successor::GotoSwitch(guarded_targets) => {
                for (guard, _) in guarded_targets {
                    guard.validate()?;
                }
            }
        }
        Ok(())
    }
}
