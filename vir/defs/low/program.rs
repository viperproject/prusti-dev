use super::{
    ast::{function::FunctionDecl, predicate::PredicateDecl},
    cfg::method::ProcedureDecl,
};

#[derive(Debug, Clone, Serialize, Deserialize, Hash)]
pub struct Program {
    pub name: String,
    pub procedures: Vec<ProcedureDecl>,
    pub predicates: Vec<PredicateDecl>,
    pub functions: Vec<FunctionDecl>,
}
