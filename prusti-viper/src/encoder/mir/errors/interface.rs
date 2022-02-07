use crate::encoder::errors::ErrorCtxt;
use prusti_interface::data::ProcedureDefId;
use rustc_span::MultiSpan;
use vir_crate::high as vir_high;

pub(crate) trait ErrorInterface {
    fn register_error<T: Into<MultiSpan>>(
        &mut self,
        span: T,
        error_ctxt: ErrorCtxt,
        def_id: ProcedureDefId,
    ) -> vir_high::Position;
    /// Takes a position of an already registered error and registers a new
    /// error with the same span, but different error context.
    fn change_error_context(
        &mut self,
        position: vir_high::Position,
        error_ctxt: ErrorCtxt,
    ) -> vir_high::Position;
}

impl<'v, 'tcx: 'v> ErrorInterface for super::super::super::Encoder<'v, 'tcx> {
    fn register_error<T: Into<MultiSpan>>(
        &mut self,
        span: T,
        error_ctxt: ErrorCtxt,
        def_id: ProcedureDefId,
    ) -> vir_high::Position {
        self.error_manager()
            .register(span, error_ctxt, def_id)
            .into()
    }
    fn change_error_context(
        &mut self,
        position: vir_high::Position,
        error_ctxt: ErrorCtxt,
    ) -> vir_high::Position {
        self.error_manager()
            .change_error_context(position.into(), error_ctxt)
            .into()
    }
}
