use crate::encoder::{
    errors::{ErrorCtxt, MultiSpan},
    middle::core_proof::lowerer::Lowerer,
    mir::procedures::MirProcedureEncoderInterface,
};
use vir_crate::low as vir_low;

pub(in super::super) trait ErrorsInterface {
    fn register_error<T: Into<MultiSpan>>(
        &mut self,
        span: T,
        error_ctxt: ErrorCtxt,
    ) -> vir_low::Position;
}

impl<'p, 'v: 'p, 'tcx: 'v> ErrorsInterface for Lowerer<'p, 'v, 'tcx> {
    fn register_error<T: Into<MultiSpan>>(
        &mut self,
        span: T,
        error_ctxt: ErrorCtxt,
    ) -> vir_low::Position {
        self.encoder
            .error_manager()
            .register_error(
                span,
                error_ctxt,
                self.encoder
                    .decode_procedure_def_id(self.procedure_name.as_ref().unwrap()),
            )
            .into()
    }
}
