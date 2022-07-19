use crate::encoder::errors::SpannedEncodingResult;
use prusti_rustc_interface::{
    errors::MultiSpan,
    hir::def_id::DefId,
    middle::{mir, ty},
    span::Span,
};

pub(crate) trait SpanInterface<'tcx> {
    fn get_definition_span(&self, def_id: DefId) -> Span;
    fn get_type_definition_span(&self, ty: ty::Ty<'tcx>) -> MultiSpan;
    fn get_mir_body_span(&self, mir: &mir::Body<'tcx>) -> Span;
    fn get_mir_local_span(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<Span>;
    fn get_mir_location_span(&self, mir: &mir::Body<'tcx>, location: mir::Location) -> Span;
    fn get_mir_terminator_span(&self, terminator: &mir::Terminator<'tcx>) -> Span;
}

impl<'v, 'tcx: 'v> SpanInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn get_definition_span(&self, def_id: DefId) -> Span {
        self.env().get_def_span(def_id)
    }
    fn get_type_definition_span(&self, ty: ty::Ty<'tcx>) -> MultiSpan {
        crate::encoder::mir::types::MirTypeEncoderInterface::get_type_definition_span(self, ty)
    }
    fn get_mir_body_span(&self, mir: &mir::Body<'tcx>) -> Span {
        mir.span
    }
    fn get_mir_local_span(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<Span> {
        crate::encoder::mir::places::PlacesEncoderInterface::get_local_span(self, mir, local)
    }
    fn get_mir_terminator_span(&self, terminator: &mir::Terminator<'tcx>) -> Span {
        terminator.source_info.span
    }
    fn get_mir_location_span(&self, mir: &mir::Body<'tcx>, location: mir::Location) -> Span {
        mir.source_info(location).span
    }
}
