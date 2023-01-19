// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{common::identifier::WithIdentifier, legacy::ast::*};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct BodylessMethod {
    pub name: String,
    pub formal_args: Vec<LocalVar>,
    pub formal_returns: Vec<LocalVar>,
    pub pres: Vec<Expr>,
    pub posts: Vec<Expr>,
}

impl WithIdentifier for BodylessMethod {
    fn get_identifier(&self) -> String {
        self.name.clone()
    }
}

impl fmt::Display for BodylessMethod {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "method {}(", self.name)?;
        let mut first = true;
        for arg in &self.formal_args {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{arg:?}")?;
            first = false
        }
        write!(f, ") returns (")?;
        for arg in &self.formal_returns {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{arg:?}")?;
            first = false
        }
        write!(f, ")")?;
        for pre in &self.pres {
            write!(f, "\n    requires {pre}")?;
        }
        for post in &self.posts {
            write!(f, "\n    ensures {post}")?;
        }
        write!(f, ";")
    }
}
