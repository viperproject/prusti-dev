// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{common::identifier::WithIdentifier, legacy::ast::*};
use rustc_hash::FxHashMap;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Function {
    pub name: String,
    pub formal_args: Vec<LocalVar>,
    pub return_type: Type,
    pub pres: Vec<Expr>,
    pub posts: Vec<Expr>,
    pub body: Option<Expr>,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "function {}(", self.name)?;
        let mut first = true;
        for arg in &self.formal_args {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{arg:?}")?;
            first = false
        }
        writeln!(f, "): {}", self.return_type)?;
        for pre in &self.pres {
            writeln!(f, "  requires {pre}")?;
        }
        for post in &self.posts {
            writeln!(f, "  ensures {post}")?;
        }
        if let Some(ref body) = self.body {
            writeln!(f, "{{")?;
            writeln!(f, "\t{body}")?;
            write!(f, "}}")?;
        }
        write!(f, "")
    }
}

impl Function {
    pub fn inline_body(&self, args: Vec<Expr>) -> Expr {
        let subst: FxHashMap<LocalVar, Expr> = self.formal_args.iter().cloned().zip(args).collect();
        // TODO: this does not handle let expressions, quantifiers, and so on
        self.body.clone().unwrap().fold_expr(|orig_expr| {
            if let Expr::Local(ref local, ref _pos) = orig_expr {
                subst[local].clone()
            } else {
                orig_expr
            }
        })
    }

    pub fn apply(&self, args: Vec<Expr>) -> Expr {
        Expr::FuncApp(
            self.name.to_string(),
            args,
            self.formal_args.clone(),
            self.return_type.clone(),
            Position::default(),
        )
    }

    /// Does the function have a body that depends neither on
    /// function parameters nor on the heap?
    pub fn has_constant_body(&self) -> bool {
        match self.body {
            Some(ref expr) => expr.is_constant(),
            None => false,
        }
    }

    pub fn visit_expressions<F: FnMut(&Expr)>(&self, mut visitor: F) {
        self.pres.iter().for_each(&mut visitor);
        self.posts.iter().for_each(&mut visitor);
        self.body.iter().for_each(visitor);
    }

    pub fn visit_expressions_mut<F: FnMut(&mut Expr)>(&mut self, mut visitor: F) {
        self.pres.iter_mut().for_each(&mut visitor);
        self.posts.iter_mut().for_each(&mut visitor);
        self.body.iter_mut().for_each(visitor);
    }
}

impl WithIdentifier for Function {
    fn get_identifier(&self) -> String {
        // The functions in `low` should be already monomorphised.
        self.name.clone()
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct FunctionIdentifier(pub(crate) String);

impl From<String> for FunctionIdentifier {
    fn from(string: String) -> Self {
        Self(string)
    }
}
