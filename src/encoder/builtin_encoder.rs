// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::Encoder;
use encoder::vir;
use encoder::vir::utils::ExprIterator;
use rustc::middle::const_val::ConstVal;
use rustc::ty;

#[derive(Clone,Copy,Debug,Hash,Eq,PartialEq)]
pub enum BuiltinMethodKind {
    HavocRef
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
                formal_returns: vec![vir::LocalVar::new("ret", vir::Type::TypedRef("".to_string()))]
            }
        }
    }
}
