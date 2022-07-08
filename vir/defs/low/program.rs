#![derive_for_all(
    Debug,
    derive_more::Display,
    Clone,
    serde::Serialize,
    serde::Deserialize,
    PartialEq(ignore=[position]),
    Eq,
    Hash(ignore=[position])
)]
#![derive_for_all_structs(new, new_with_pos)]

use super::{
    ast::{function::FunctionDecl, predicate::PredicateDecl},
    cfg::{method::MethodDecl, procedure::ProcedureDecl},
    domain::DomainDecl,
};
use crate::common::{check_mode::CheckMode, display};

#[display(
    fmt = "program_name: {}\n{}\n{}\n{}\n{}\n{}\n",
    name,
    "display::foreach!(\"{}\n\", domains)",
    "display::foreach!(\"{}\n\", predicates)",
    "display::foreach!(\"{}\n\", functions)",
    "display::foreach!(\"{}\n\", methods)",
    "display::foreach!(\"{}\n\", procedures)"
)]
pub struct Program {
    pub name: String,
    pub check_mode: CheckMode,
    pub domains: Vec<DomainDecl>,
    pub predicates: Vec<PredicateDecl>,
    pub functions: Vec<FunctionDecl>,
    pub methods: Vec<MethodDecl>,
    pub procedures: Vec<ProcedureDecl>,
}
