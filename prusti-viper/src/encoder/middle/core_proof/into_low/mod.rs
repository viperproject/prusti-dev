use super::{lowerer::Lowerer, MidCoreProofEncoderInterface};
use crate::encoder::{errors::SpannedEncodingResult, Encoder};
use vir_crate::{low as vir_low, middle as vir_mid};

mod cfg;
mod expression;
mod interface;

pub(super) use self::interface::IntoLowInterface;

pub(super) trait IntoLow {
    type Target;
    fn into_low<'p, 'v: 'p, 'tcx: 'v>(
        self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target>;
}
