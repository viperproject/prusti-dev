use crate::encoder::errors::SpannedEncodingError;
use vir_crate::middle::operations::{MiddleToTypedTypeUpperer, TypedToMiddleTypeLowerer};

impl<'v, 'tcx> TypedToMiddleTypeLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;
}

impl<'v, 'tcx> MiddleToTypedTypeUpperer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;
}
