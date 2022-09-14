use super::low_to_viper::{Context, ToViper};
use viper::{self, AstFactory};

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, Hash, Eq, PartialEq)]
pub enum Program {
    Legacy(vir::legacy::Program),
    Low(vir::low::Program),
}

impl Program {
    pub fn get_name(&self) -> &str {
        match self {
            Program::Legacy(program) => &program.name,
            Program::Low(program) => &program.name,
        }
    }
    pub fn set_name(&mut self, name: String) {
        match self {
            Program::Legacy(program) => program.name = name,
            Program::Low(program) => program.name = name,
        }
    }
    pub fn get_check_mode(&self) -> vir::common::check_mode::CheckMode {
        // FIXME: Remove because this is not needed anymore.
        match self {
            Program::Legacy(_) => vir::common::check_mode::CheckMode::MemorySafetyWithFunctional,
            Program::Low(program) => program.check_mode,
        }
    }
    pub fn get_name_with_check_mode(&self) -> String {
        // FIXME: Remove because this is not needed anymore.
        format!("{}-{}", self.get_name(), self.get_check_mode())
    }
}

impl<'v> ToViper<'v, viper::Program<'v>> for Program {
    fn to_viper(&self, context: &mut Context<'v>, ast: &AstFactory<'v>) -> viper::Program<'v> {
        match self {
            Program::Legacy(program) => program.to_viper(context, ast),
            Program::Low(program) => program.to_viper(context, ast),
        }
    }
}
