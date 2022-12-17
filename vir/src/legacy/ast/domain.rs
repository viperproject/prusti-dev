// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{common::identifier::WithIdentifier, legacy::ast::*};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Domain {
    pub name: String,
    pub functions: Vec<DomainFunc>,
    pub axioms: Vec<DomainAxiom>,
    pub type_vars: Vec<Type>,
}

impl Domain {
    pub fn get_identifier(&self) -> String {
        self.name.clone()
    }
}

impl fmt::Display for Domain {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "domain {}", self.name)?;
        if self.type_vars.is_empty() {
            writeln!(f, "{{")?;
        } else {
            write!(f, "[")?;
            let mut first = true;
            for type_var in &self.type_vars {
                if !first {
                    write!(f, ", ")?;
                }
                write!(f, "{}", type_var)?;
                first = false;
            }
            writeln!(f, "] {{")?;
        }
        for function in &self.functions {
            writeln!(f, "\t{}", function)?;
        }
        writeln!(f)?;
        for axiom in &self.axioms {
            writeln!(f, "\t{}", axiom)?;
        }
        write!(f, "}}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct DomainFunc {
    pub name: String,
    pub formal_args: Vec<LocalVar>,
    pub return_type: Type,
    pub unique: bool,
    pub domain_name: String,
}

impl DomainFunc {
    pub fn apply(&self, args: Vec<Expr>) -> Expr {
        Expr::DomainFuncApp(self.clone(), args, Position::default())
    }
}

impl fmt::Display for DomainFunc {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.unique {
            write!(f, "unique ")?;
        }
        write!(f, "function {}(", self.name)?;
        let mut first = true;
        for arg in &self.formal_args {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", arg)?;
            first = false
        }
        writeln!(f, "): {}", self.return_type)
    }
}

impl WithIdentifier for DomainFunc {
    fn get_identifier(&self) -> String {
        // The functions in `low` should be already monomorphised.
        self.name.clone()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct DomainAxiom {
    pub comment: Option<String>,
    pub name: String,
    pub expr: Expr,
    pub domain_name: String,
}

impl fmt::Display for DomainAxiom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(comment) = &self.comment {
            writeln!(
                f,
                "/* {} */ axiom {} {{ {} }}",
                comment, self.name, self.expr
            )
        } else {
            writeln!(f, "axiom {} {{ {} }}", self.name, self.expr)
        }
    }
}
