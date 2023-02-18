use std::fmt::Debug;

use crate::encoder::{
    errors::{ErrorCtxt, MultiSpan},
    middle::core_proof::lowerer::Lowerer,
};
use vir_crate::low as vir_low;

pub(in super::super) trait ErrorsInterface {
    fn register_error<T: Into<MultiSpan> + Debug>(
        &mut self,
        span: T,
        error_ctxt: ErrorCtxt,
    ) -> vir_low::Position;
}

impl<'p, 'v: 'p, 'tcx: 'v> ErrorsInterface for Lowerer<'p, 'v, 'tcx> {
    fn register_error<T: Into<MultiSpan> + Debug>(
        &mut self,
        span: T,
        error_ctxt: ErrorCtxt,
    ) -> vir_low::Position {
        if let Some(def_id) = self.def_id {
            self.encoder
                .error_manager()
                .register_error(span, error_ctxt, def_id)
                .into()
        } else {
            Default::default()
        }
    }
}
