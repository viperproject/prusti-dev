// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    common::{display, identifier::WithIdentifier},
    polymorphic::ast::*,
};
use rustc_hash::FxHashMap;
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

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord,
)]
pub struct DomainFunc {
    pub name: String,
    pub type_arguments: Vec<Type>,
    pub formal_args: Vec<LocalVar>,
    pub return_type: Type,
    pub unique: bool,
    pub domain_name: String,
}

impl DomainFunc {
    pub fn new(
        domain_name: impl ToString,
        fn_name: impl ToString,
        args: Vec<LocalVar>,
        return_type: Type,
    ) -> Self {
        Self {
            name: fn_name.to_string(),
            type_arguments: vec![],
            formal_args: args,
            return_type,
            unique: false,
            domain_name: domain_name.to_string(),
        }
    }

    pub fn apply(&self, args: Vec<Expr>) -> Expr {
        Expr::domain_func_app(self.clone(), args)
    }

    pub fn apply0(&self) -> Expr {
        self.apply(vec![])
    }

    pub fn apply1(&self, arg1: impl Into<Expr>) -> Expr {
        self.apply(vec![arg1.into()])
    }

    pub fn apply2(&self, arg1: impl Into<Expr>, arg2: impl Into<Expr>) -> Expr {
        self.apply(vec![arg1.into(), arg2.into()])
    }

    pub fn apply3(
        &self,
        arg1: impl Into<Expr>,
        arg2: impl Into<Expr>,
        arg3: impl Into<Expr>,
    ) -> Expr {
        self.apply(vec![arg1.into(), arg2.into(), arg3.into()])
    }
}

impl fmt::Display for DomainFunc {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.unique {
            write!(f, "unique ")?;
        }
        write!(
            f,
            "function {}<{}>(",
            self.name,
            display::cjoin(&self.type_arguments)
        )?;
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
        compute_identifier(
            &self.name,
            &self.type_arguments,
            &self.formal_args,
            &self.return_type,
        )
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
