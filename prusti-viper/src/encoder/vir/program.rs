use encoder::vir::ast::*;
use encoder::vir::cfg::CfgMethod;

#[derive(Debug, Serialize, Deserialize)]
pub struct Program {
    pub fields: Vec<Field>,
    pub builtin_methods: Vec<BodylessMethod>,
    pub methods: Vec<CfgMethod>,
    pub functions: Vec<Function>,
    pub viper_predicates: Vec<Predicate>,
}
