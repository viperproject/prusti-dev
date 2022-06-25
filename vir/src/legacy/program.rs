use crate::legacy::{ast::*, cfg::CfgMethod};

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, Hash)]
pub struct Program {
    pub name: String,
    pub domains: Vec<Domain>,
    pub fields: Vec<Field>,
    pub builtin_methods: Vec<BodylessMethod>,
    pub methods: Vec<CfgMethod>,
    pub functions: Vec<Function>,
    pub viper_predicates: Vec<Predicate>,
}
