// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::super::builtin_encoder::BuiltinMethodKind;
use vir_crate::polymorphic as vir;

pub trait ResourcesEncoderInterface {
    fn get_tick_call(&self, amount: usize) -> vir::Stmt;
}

impl<'v, 'tcx> ResourcesEncoderInterface for super::super::Encoder<'v, 'tcx> {
    fn get_tick_call(&self, amount: usize) -> vir::Stmt {
        vir::Stmt::MethodCall(vir::MethodCall {
            method_name: self.encode_builtin_method_use(BuiltinMethodKind::Tick),
            arguments: vec![amount.into()],
            targets: vec![],
        })
    }
}
