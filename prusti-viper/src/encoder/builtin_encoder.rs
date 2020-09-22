// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::vir;

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub enum BuiltinMethodKind {
    HavocBool,
    HavocInt,
    HavocRef,
    HavocSet,
    HavocSeq,
    HavocMultiSet,
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum BuiltinFunctionKind {
    /// type
    Unreachable(vir::Type),
    /// type
    Undefined(vir::Type),
}

pub struct BuiltinEncoder {}

impl BuiltinEncoder {
    pub fn new() -> Self {
        Self {}
    }

    pub fn encode_builtin_method_name(&self, method: BuiltinMethodKind) -> String {
        match method {
            BuiltinMethodKind::HavocBool => "builtin$havoc_bool".to_string(),
            BuiltinMethodKind::HavocInt => "builtin$havoc_int".to_string(),
            BuiltinMethodKind::HavocRef => "builtin$havoc_ref".to_string(),
            BuiltinMethodKind::HavocSet => "builtin$havoc_set".to_string(),
            BuiltinMethodKind::HavocSeq => "builtin$havoc_seq".to_string(),
            BuiltinMethodKind::HavocMultiSet => "builtin$havoc_multiset".to_string(),
        }
    }

    pub fn encode_builtin_method_def(&self, method: BuiltinMethodKind) -> vir::BodylessMethod {
        let return_type = match method {
            BuiltinMethodKind::HavocBool => vir::Type::Bool,
            BuiltinMethodKind::HavocInt => vir::Type::Int,
            BuiltinMethodKind::HavocRef => vir::Type::TypedRef("".to_string()),
            BuiltinMethodKind::HavocSet => vir::Type::Set,
            BuiltinMethodKind::HavocSeq => vir::Type::Seq,
            BuiltinMethodKind::HavocMultiSet => vir::Type::MultiSet,
        };
        vir::BodylessMethod {
            name: self.encode_builtin_method_name(method),
            formal_args: vec![],
            formal_returns: vec![vir::LocalVar::new("ret", return_type)],
        }
    }

    pub fn encode_builtin_function_name(&self, function: &BuiltinFunctionKind) -> String {
        match function {
            BuiltinFunctionKind::Unreachable(vir::Type::Int) => format!("builtin$unreach_int"),
            BuiltinFunctionKind::Unreachable(vir::Type::Bool) => format!("builtin$unreach_bool"),
            BuiltinFunctionKind::Unreachable(vir::Type::TypedRef(_)) => {
                format!("builtin$unreach_ref")
            }
            BuiltinFunctionKind::Unreachable(vir::Type::Domain(_)) => {
                format!("builtin$unreach_domain")
            }
            BuiltinFunctionKind::Unreachable(vir::Type::Seq) => format!("builtin$unreach_seq"),
            BuiltinFunctionKind::Unreachable(vir::Type::Set) => format!("builtin$unreach_set"),
            BuiltinFunctionKind::Unreachable(vir::Type::MultiSet) => format!("builtin$unreach_multiset"),
            BuiltinFunctionKind::Undefined(vir::Type::Int) => format!("builtin$undef_int"),
            BuiltinFunctionKind::Undefined(vir::Type::Bool) => format!("builtin$undef_bool"),
            BuiltinFunctionKind::Undefined(vir::Type::TypedRef(_)) => format!("builtin$undef_ref"),
            BuiltinFunctionKind::Undefined(vir::Type::Domain(_)) => format!("builtin$undef_doman"),
            BuiltinFunctionKind::Undefined(vir::Type::Seq) => format!("builtin$undef_seq"),
            BuiltinFunctionKind::Undefined(vir::Type::Set) => format!("builtin$undef_set"),
            BuiltinFunctionKind::Undefined(vir::Type::MultiSet) => format!("builtin$undef_multiset"),
        }
    }

    pub fn encode_builtin_function_def(&self, function: BuiltinFunctionKind) -> vir::Function {
        let fn_name = self.encode_builtin_function_name(&function);
        match function {
            BuiltinFunctionKind::Unreachable(typ) => vir::Function {
                name: fn_name,
                formal_args: vec![],
                return_type: typ,
                // Precondition is false, because we want to be sure that this function is never used
                pres: vec![false.into()],
                posts: vec![],
                body: None,
            },
            BuiltinFunctionKind::Undefined(typ) => vir::Function {
                name: fn_name,
                formal_args: vec![],
                return_type: typ,
                pres: vec![],
                posts: vec![],
                body: None,
            },
        }
    }
}
