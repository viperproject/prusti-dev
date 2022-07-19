// © 2019, ETH Zurich
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
pub struct Function {
    pub name: String,
    /// Type arguments with which this function was instantiated. These are
    /// needed to distinguish `std::mem::size_of::<u32>()` from
    /// `std::mem::size_of::<u8>()`, which have the same parameters and return
    /// types, but different implementations.
    pub type_arguments: Vec<Type>,
    pub formal_args: Vec<LocalVar>,
    pub return_type: Type,
    pub pres: Vec<Expr>,
    pub posts: Vec<Expr>,
    pub body: Option<Expr>,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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
        writeln!(f, "): {}", self.return_type)?;
        for pre in &self.pres {
            writeln!(f, "  requires {}", pre)?;
        }
        for post in &self.posts {
            writeln!(f, "  ensures {}", post)?;
        }
        if let Some(ref body) = self.body {
            writeln!(f, "{{")?;
            writeln!(f, "\t{}", body)?;
            write!(f, "}}")?;
        }
        write!(f, "")
    }
}

impl Function {
    pub fn inline_body(&self, args: Vec<Expr>) -> Expr {
        let subst: FxHashMap<LocalVar, Expr> = self
            .formal_args
            .iter()
            .cloned()
            .zip(args.into_iter())
            .collect();
        // TODO: this does not handle let expressions, quantifiers, and so on
        self.body.clone().unwrap().fold_expr(|orig_expr| {
            if let Expr::Local(Local { ref variable, .. }) = orig_expr {
                subst[variable].clone()
            } else {
                orig_expr
            }
        })
    }

    pub fn apply(&self, args: Vec<Expr>) -> Expr {
        Expr::func_app(
            self.name.to_string(),
            self.type_arguments.clone(),
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
}

pub fn compute_identifier(
    name: &str,
    type_arguments: &[Type],
    _formal_args: &[LocalVar],
    _return_type: &Type,
) -> String {
    let mut identifier = name.to_string();
    // Include the signature of the function in the function name
    if !type_arguments.is_empty() {
        identifier.push_str("__$TY$__");
    }
    fn type_name(typ: &Type) -> String {
        match typ {
            Type::Int => "$int$".to_string(),
            Type::Bool => "$bool$".to_string(),
            Type::Float(Float::F32) => "$f32$".to_string(),
            Type::Float(Float::F64) => "$f64$".to_string(),
            Type::BitVector(value) => format!("${}$", value),
            Type::TypedRef(_) | Type::TypeVar(_) => typ.encode_as_string(),
            Type::Domain(_) => typ.name(),
            Type::Snapshot(_) => format!("Snap${}", typ.name()),
            Type::Seq(seq_type) => format!("Seq${}", type_name(&seq_type.typ)),
            Type::Map(map) => format!(
                "Map${}${}",
                type_name(&map.key_type),
                type_name(&map.val_type)
            ),
        }
    }
    for arg in type_arguments {
        identifier.push_str(&type_name(arg));
        identifier.push('$');
    }
    identifier
}

impl WithIdentifier for Function {
    fn get_identifier(&self) -> String {
        compute_identifier(
            &self.name,
            &self.type_arguments,
            &self.formal_args,
            &self.return_type,
        )
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct FunctionIdentifier(pub(crate) String);

impl From<String> for FunctionIdentifier {
    fn from(string: String) -> Self {
        Self(string)
    }
}
