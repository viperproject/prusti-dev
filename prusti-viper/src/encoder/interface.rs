use crate::encoder::{
    errors::{SpannedEncodingResult, WithSpan},
    mir::specifications::SpecificationsInterface,
    snapshot::interface::SnapshotEncoderInterface,
    stub_function_encoder::StubFunctionEncoder,
    Encoder,
};
use log::{debug, trace};
use prusti_common::config;
use prusti_interface::data::ProcedureDefId;
use prusti_rustc_interface::{
    middle::{
        mir, ty,
        ty::{Binder, GenericArgsRef},
    },
    span::Span,
};
use rustc_hash::{FxHashMap, FxHashSet};

use prusti_interface::specs::typed::ProcedureSpecificationKind;
use std::cell::RefCell;
use vir_crate::{common::identifier::WithIdentifier, high as vir_high, polymorphic as vir_poly};

pub(crate) trait PureFunctionFormalArgsEncoderInterface<'p, 'v: 'p, 'tcx: 'v> {
    fn encoder(&self) -> &'p Encoder<'v, 'tcx>;

    fn check_type(
        &self,
        var_span: Span,
        ty: Binder<'tcx, ty::Ty<'tcx>>,
    ) -> SpannedEncodingResult<()>;

    fn get_span(&self, local: mir::Local) -> Span;

    fn encode_formal_args(
        &self,
        sig: ty::PolyFnSig<'tcx>,
    ) -> SpannedEncodingResult<Vec<vir_poly::LocalVar>> {
        let mut formal_args = vec![];
        for local_idx in 0..sig.skip_binder().inputs().len() {
            let local_ty = sig.input(local_idx);
            let local = mir::Local::from_usize(local_idx + 1);
            let var_name = format!("{local:?}");
            let var_span = self.get_span(local);

            self.check_type(var_span, local_ty)?;

            let var_type = self
                .encoder()
                .encode_snapshot_type(local_ty.skip_binder())
                .with_span(var_span)?;
            formal_args.push(vir_poly::LocalVar::new(var_name, var_type))
        }
        Ok(formal_args)
    }
}
