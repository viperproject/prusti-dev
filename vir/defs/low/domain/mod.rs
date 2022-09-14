#![derive_for_all(
    Debug,
    derive_more::Display,
    Clone,
    serde::Serialize,
    serde::Deserialize,
    PartialEq(trait_type=std::cmp::PartialEq,ignore=[position]),
    Eq,
    Hash(trait_type=core::hash::Hash,ignore=[position])
)]
#![derive_for_all_structs(new, new_with_pos)]

use crate::{
    common::display,
    low::ast::{
        expression::{Expression, Trigger},
        ty::Type,
        variable::VariableDecl,
    },
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
    pub rewrite_rules: Vec<DomainRewriteRuleDecl>,
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
    pub comment: Option<String>,
    pub name: String,
    pub body: Expression,
}

/// A rewrite rule is a special form of axiom that can be used not only by the
/// SMT solver, but also by the e-graph based rewriting enging.
#[display(
    fmt = "rewrite-rule {} {{\n  forall {} :: [{}] {} → {}\n}}",
    name,
    "display::cjoin(variables)",
    "display::option_cjoin!(triggers, \"\")",
    source,
    target
)]
pub struct DomainRewriteRuleDecl {
    pub comment: Option<String>,
    pub name: String,
    /// Whether the rule should be only given to egg, or also to the SMT solver.
    pub egg_only: bool,
    pub variables: Vec<VariableDecl>,
    /// If None, use `target` as the trigger. This allows more efficient
    /// application of rules in egg.
    pub triggers: Option<Vec<Trigger>>,
    pub source: Expression,
    pub target: Expression,
}
