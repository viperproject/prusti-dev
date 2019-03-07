// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::Encoder;
use encoder::vir;
use encoder::vir::ExprIterator;
use rustc::middle::const_val::ConstVal;
use rustc::ty;
use syntax_pos::DUMMY_SP;
use encoder::error_manager::ErrorCtxt;

#[derive(Clone,Copy,Debug,Hash,Eq,PartialEq)]
pub enum BuiltinMethodKind {
    HavocRef
}

#[derive(Clone,Debug,Hash,Eq,PartialEq)]
pub enum BuiltinFunctionKind {
    /// type
    Undefined(vir::Type),
}

pub struct BuiltinEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>
}

impl<'p, 'v, 'r: 'v, 'a: 'r, 'tcx: 'a> BuiltinEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>) -> Self {
        BuiltinEncoder {
            encoder
        }
    }

    pub fn encode_builtin_method_name(&self, method: BuiltinMethodKind) -> String {
        match method {
            BuiltinMethodKind::HavocRef => "builtin$havoc_ref".to_string(),
        }
    }

    pub fn encode_builtin_method_def(&self, method: BuiltinMethodKind) -> vir::BodylessMethod {
        match method {
            BuiltinMethodKind::HavocRef => vir::BodylessMethod{
                name: self.encode_builtin_method_name(method),
                formal_args: vec![],
                formal_returns: vec![vir::LocalVar::new("ret", vir::Type::TypedRef("".to_string()))],
            }
        }
    }

    pub fn encode_builtin_function_name(&self, function: &BuiltinFunctionKind) -> String {
        match function {
            BuiltinFunctionKind::Undefined(vir::Type::Int) => format!("builtin$undef_int"),
            BuiltinFunctionKind::Undefined(vir::Type::Bool) => format!("builtin$undef_bool"),
            BuiltinFunctionKind::Undefined(vir::Type::TypedRef(_)) => format!("builtin$undef_ref")
        }
    }

    pub fn encode_builtin_function_def(&self, function: BuiltinFunctionKind) -> vir::Function {
        let fn_name = self.encode_builtin_function_name(&function);
        match function {
            BuiltinFunctionKind::Undefined(typ) => vir::Function {
                name: fn_name,
                formal_args: vec![],
                return_type: typ,
                // Precondition is false, because we want to be sure that this function is never used
                pres: vec![ false.into() ],
                posts: vec![],
                body: None,
                pos: self.encoder.error_manager().register(DUMMY_SP, ErrorCtxt::Unexpected),
            },
        }
    }
}
