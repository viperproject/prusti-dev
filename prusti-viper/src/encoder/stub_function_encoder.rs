// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::{
    errors::{SpannedEncodingResult, WithSpan},
    high::generics::HighGenericsEncoderInterface,
    interface::PureFunctionFormalArgsEncoderInterface,
    mir_encoder::{MirEncoder, PlaceEncoder},
    snapshot::interface::SnapshotEncoderInterface,
    Encoder,
};
use log::debug;
use prusti_rustc_interface::{
    hir::def_id::DefId,
    middle::{
        mir,
        mir::Local,
        ty,
        ty::{Binder, GenericArgsRef},
    },
    span::Span,
};
use vir_crate::polymorphic as vir;

use super::mir::specifications::SpecificationsInterface;

pub struct StubFunctionEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    mir: Option<&'p mir::Body<'tcx>>,
    mir_encoder: Option<MirEncoder<'p, 'v, 'tcx>>,
    proc_def_id: DefId,
    substs: GenericArgsRef<'tcx>,
    sig: ty::PolyFnSig<'tcx>,
}

impl<'p, 'v, 'tcx> PureFunctionFormalArgsEncoderInterface<'p, 'v, 'tcx>
    for StubFunctionEncoder<'p, 'v, 'tcx>
{
    fn check_type(&self, _span: Span, _ty: Binder<ty::Ty<'tcx>>) -> SpannedEncodingResult<()> {
        Ok(())
    }

    fn encoder(&self) -> &'p Encoder<'v, 'tcx> {
        self.encoder
    }

    fn get_span(&self, _local: mir::Local) -> Span {
        self.encoder.get_spec_span(self.proc_def_id)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> StubFunctionEncoder<'p, 'v, 'tcx> {
    #[tracing::instrument(name = "StubFunctionEncoder::new", level = "trace", skip(encoder, mir))]
    pub fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        proc_def_id: DefId,
        mir: Option<&'p mir::Body<'tcx>>,
        substs: GenericArgsRef<'tcx>,
        sig: ty::PolyFnSig<'tcx>,
    ) -> Self {
        StubFunctionEncoder {
            encoder,
            mir,
            mir_encoder: mir.map(|m| MirEncoder::new(encoder, m, proc_def_id)),
            proc_def_id,
            substs,
            sig,
        }
    }

    fn default_span(&self) -> Span {
        self.mir
            .map(|m| m.span)
            .unwrap_or_else(|| self.encoder.get_spec_span(self.proc_def_id))
    }

    #[tracing::instrument(level = "debug", skip(self))]
    pub fn encode_function(&self) -> SpannedEncodingResult<vir::Function> {
        let function_name = self.encode_function_name();
        debug!("Encode stub function {}", function_name);

        let formal_args = self.encode_formal_args(self.sig)?;

        let type_arguments = self
            .encoder
            .encode_generic_arguments(self.proc_def_id, self.substs)
            .with_span(self.default_span())?;

        let return_type = self.encode_function_return_type()?;

        let function = vir::Function {
            name: function_name,
            type_arguments,
            formal_args,
            return_type,
            pres: vec![false.into()],
            posts: vec![],
            body: None,
        };

        self.encoder
            .log_vir_program_before_foldunfold(function.to_string());

        // No need to fold/unfold, as this function is body-less and the contract is trivial
        Ok(function)
    }

    pub fn encode_function_name(&self) -> String {
        // TODO: It would be nice to somehow mark that this function is a stub
        // in the encoding.
        self.encoder.encode_pure_item_name(self.proc_def_id)
    }

    pub fn encode_function_return_type(&self) -> SpannedEncodingResult<vir::Type> {
        let ty = self.sig.output();

        self.encoder
            .encode_snapshot_type(ty.skip_binder())
            .with_span(self.encoder.get_spec_span(self.proc_def_id))
    }
}
