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

use crate::{
    common::display,
    low::ast::{expression::Expression, ty::Type, variable::VariableDecl},
};

#[display(
    fmt = "domain {} {{\n{}{} }}\n",
    name,
    "display::foreach!(\"  {}\n\", functions)",
    "display::foreach!(\"  {}\n\", axioms)"
)]
pub struct DomainDecl {
    pub name: String,
    pub functions: Vec<DomainFunctionDecl>,
    pub axioms: Vec<DomainAxiomDecl>,
}

#[display(
    fmt = "function {}({}): {}",
    name,
    "display::cjoin(parameters)",
    return_type
)]
pub struct DomainFunctionDecl {
    pub name: String,
    pub is_unique: bool,
    pub parameters: Vec<VariableDecl>,
    pub return_type: Type,
}

#[display(fmt = "axiom {} {{\n  {}\n}}", name, body)]
pub struct DomainAxiomDecl {
    pub name: String,
    pub body: Expression,
}
