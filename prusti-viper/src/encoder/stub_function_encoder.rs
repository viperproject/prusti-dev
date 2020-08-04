// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::mir_encoder::{MirEncoder, PlaceEncoder};
use crate::encoder::Encoder;
use prusti_common::vir;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use log::{trace, debug};

pub struct StubFunctionEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    mir: &'p mir::Body<'tcx>,
    mir_encoder: MirEncoder<'p, 'v, 'tcx>,
    proc_def_id: DefId,
}

impl<'p, 'v: 'p, 'tcx: 'v> StubFunctionEncoder<'p, 'v, 'tcx> {
    pub fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        proc_def_id: DefId,
        mir: &'p mir::Body<'tcx>,
    ) -> Self {
        trace!("StubFunctionEncoder constructor: {:?}", proc_def_id);
        StubFunctionEncoder {
            encoder,
            mir,
            mir_encoder: MirEncoder::new(encoder, mir, proc_def_id),
            proc_def_id,
        }
    }

    pub fn encode_function(&self) -> vir::Function {
        let function_name = self.encode_function_name();
        debug!("Encode stub function {}", function_name);
        let subst_strings = self.encoder.type_substitution_strings();

        let formal_args: Vec<_> = self
            .mir
            .args_iter()
            .map(|local| {
                let var_name = self.mir_encoder.encode_local_var_name(local);
                let mir_type = self.mir_encoder.get_local_ty(local);
                let var_type = self
                    .encoder
                    .encode_value_type(self.encoder.resolve_typaram(mir_type));
                let var_type = var_type.patch(&subst_strings);
                vir::LocalVar::new(var_name, var_type)
            })
            .collect();

        let return_type = self.encode_function_return_type();

        let function = vir::Function {
            name: function_name,
            formal_args,
            return_type,
            pres: vec![false.into()],
            // Note: Silicon is currently unsound when declaring a function that ensures `false`
            // See: https://github.com/viperproject/silicon/issues/376
            posts: vec![],
            body: None,
        };

        self.encoder
            .log_vir_program_before_foldunfold(function.to_string());

        // No need to fold/unfold, as this function is body-less and the contract is trivial
        function
    }

    pub fn encode_function_name(&self) -> String {
        let mut base_name = self.encoder.encode_item_name(self.proc_def_id);
        base_name.push_str("_stub");

        base_name
    }

    pub fn encode_function_return_type(&self) -> vir::Type {
        let ty = self.encoder.resolve_typaram(self.mir.return_ty());
        self.encoder.encode_value_type(ty)
    }
}
