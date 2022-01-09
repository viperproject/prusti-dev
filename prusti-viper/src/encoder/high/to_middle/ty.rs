use crate::encoder::errors::SpannedEncodingError;
use vir_crate::middle::operations::{ToHighTypeUpperer, ToMiddleTypeLowerer};

impl<'v, 'tcx> ToMiddleTypeLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;
}

impl<'v, 'tcx> ToHighTypeUpperer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;
}
