use super::low_to_viper::{ToViper, Context};
use viper::{self, AstFactory};

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, Hash)]
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
}

impl<'v> ToViper<'v, viper::Program<'v>> for Program {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Program<'v> {
        match self {
            Program::Legacy(program) => program.to_viper(context, ast),
            Program::Low(program) => program.to_viper(context, ast),
        }
    }
}
