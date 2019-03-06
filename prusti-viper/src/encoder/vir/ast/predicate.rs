// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt;
use encoder::vir::ast::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Predicate {
    pub name: String,
    pub args: Vec<LocalVar>,
    pub body: Option<Expr>,
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "predicate {}(", self.name)?;
        let mut first = true;
        for arg in &self.args {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", arg)?;
            first = false
        }
        match self.body {
            None => {
                writeln!(f, ");")
            },
            Some(ref body) => {
                writeln!(f, "){{")?;
                writeln!(f, "  {}", body)?;
                writeln!(f, "}}")
            }
        }
    }
}

impl Predicate {
    pub fn new<S: Into<String>>(name: S, args: Vec<LocalVar>, body: Option<Expr>) -> Self {
        Predicate {
            name: name.into(),
            args,
            body
        }
    }
}

impl WithIdentifier for Predicate {
    fn get_identifier(&self) -> String {
        self.name.clone()
    }
}
