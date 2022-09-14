use crate::encoder::{errors::ErrorCtxt, mir::errors::ErrorInterface, Encoder};
use prusti_rustc_interface::errors::MultiSpan;
use vir_crate::low::{self as vir_low};

pub(in super::super) trait EncoderContext {
    fn get_span(&mut self, position: vir_low::Position) -> Option<MultiSpan>;
    fn change_error_context(
        &mut self,
        position: vir_low::Position,
        error_ctxt: ErrorCtxt,
    ) -> vir_low::Position;
    fn get_error_context(&mut self, position: vir_low::Position) -> ErrorCtxt;
}

impl<'v, 'tcx: 'v> EncoderContext for Encoder<'v, 'tcx> {
    fn get_span(&mut self, position: vir_low::Position) -> Option<MultiSpan> {
        self.error_manager()
            .position_manager()
            .get_span(position.into())
            .cloned()
    }
    fn change_error_context(
        &mut self,
        position: vir_low::Position,
        error_ctxt: ErrorCtxt,
    ) -> vir_low::Position {
        ErrorInterface::change_error_context(self, position, error_ctxt)
    }
    fn get_error_context(&mut self, position: vir_low::Position) -> ErrorCtxt {
        ErrorInterface::get_error_context(self, position)
    }
}
