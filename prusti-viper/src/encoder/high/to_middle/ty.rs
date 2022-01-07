use crate::encoder::errors::SpannedEncodingError;
use vir_crate::middle::operations::ToMiddleTypeLowerer;

impl<'v, 'tcx> ToMiddleTypeLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;
}
