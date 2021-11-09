use crate::encoder::{
    encoder::SubstMap,
    errors::{EncodingError, EncodingResult, ErrorCtxt, SpannedEncodingResult, WithSpan},
    mir::{pure::specifications::encoder::SpecificationEncoder, types::MirTypeEncoderInterface},
};
use log::{debug, trace};
use prusti_interface::specs::typed;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, span_bug, ty};
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    high::{self as vir_high, operations::ty::Typed},
};

trait SpecificationEncoderInterfacePrivate<'tcx> {
    #[allow(clippy::too_many_arguments)]
    fn do_encode_assertion(
        &self,
        assertion: &typed::Assertion<'tcx>,
        pre_label: Option<&str>,
        target_args: &[vir_high::Expression],
        target_return: Option<&vir_high::Expression>,
        assertion_location: Option<mir::BasicBlock>,
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;
}

impl<'v, 'tcx: 'v> SpecificationEncoderInterfacePrivate<'tcx>
    for super::super::super::super::Encoder<'v, 'tcx>
{
    /// FIXME: The documentation is likely to be outdated.
    ///
    /// Encode an assertion coming from a specification to a `vir::Expr`.
    ///
    /// In this documentation, we distinguish the encoding of a _value_ of a Rust expression from
    /// the encoding of its _memory location_. For example, when encoding non-pure code:
    /// * given an argument `x: u32` the Viper encoding will use `x: Ref` to encode the memory
    ///   location and `x.val_int: Int` to encode the value;
    /// * given an argument `y: &u32` the Viper encoding will use `y: Ref` to encode the memory
    ///   location and `y.val_ref: Ref` to encode the value.
    ///
    /// Arguments:
    /// * `encoder`: a reference to the `Encoder`.
    /// * `assertion`: the assertion to be encoded.
    /// * `pre_label`: the label to be used to encode `old(..)` expressions. This should be `None` iff
    ///   the assertion cannot have old expressions (e.g. a precondition).
    /// * `target_args`: the expression to be used to encode arguments.
    /// * `target_return`: the expression to be used to encode `return` expressions. This should be
    ///   `None` iff the assertion cannot mention `return` (e.g. a loop invariant).
    /// * `targets_are_values`: if `true`, the elements of `target_args` and `target_return` encode
    ///   _values_ and not _memory locations_. This is typically used to encode pure functions.
    /// * `assertion_location`: the basic block at which the assertion should be encoded. This should
    ///   be `Some(..)` iff the assertion is a loop invariant.
    fn do_encode_assertion(
        &self,
        assertion: &typed::Assertion<'tcx>,
        pre_label: Option<&str>,
        target_args: &[vir_high::Expression],
        target_return: Option<&vir_high::Expression>,
        assertion_location: Option<mir::BasicBlock>,
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        trace!("encode_assertion {:?}", assertion);
        let spec_encoder = SpecificationEncoder::new(
            self,
            pre_label.unwrap_or(""),
            target_args,
            target_return,
            assertion_location,
            parent_def_id,
            tymap,
        );
        spec_encoder.encode_assertion(assertion)
    }
}

pub(crate) trait SpecificationEncoderInterface<'tcx> {
    #[allow(clippy::too_many_arguments)]
    fn encode_assertion_high(
        &self,
        assertion: &typed::Assertion<'tcx>,
        mir: &mir::Body<'tcx>,
        pre_label: Option<&str>,
        target_args: &[vir_high::Expression],
        target_return: Option<&vir_high::Expression>,
        assertion_location: Option<mir::BasicBlock>,
        error: ErrorCtxt,
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;
}

impl<'v, 'tcx: 'v> SpecificationEncoderInterface<'tcx>
    for crate::encoder::encoder::Encoder<'v, 'tcx>
{
    #[allow(clippy::too_many_arguments)]
    fn encode_assertion_high(
        &self,
        assertion: &typed::Assertion<'tcx>,
        mir: &mir::Body<'tcx>,
        pre_label: Option<&str>,
        target_args: &[vir_high::Expression],
        target_return: Option<&vir_high::Expression>,
        assertion_location: Option<mir::BasicBlock>,
        error: ErrorCtxt,
        parent_def_id: DefId,
        tymap: &SubstMap<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        trace!("encode_assertion {:?}", assertion);
        let encoded_assertion = self.do_encode_assertion(
            assertion,
            pre_label,
            target_args,
            target_return,
            assertion_location,
            parent_def_id,
            tymap,
        )?;
        Ok(encoded_assertion.set_default_pos(
            self.error_manager()
                .register(
                    typed::Spanned::get_spans(assertion, mir, self.env().tcx()),
                    error,
                    parent_def_id,
                )
                .into(),
        ))
    }
}
