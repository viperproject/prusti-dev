use super::lowerer::Lowerer;
use crate::encoder::errors::SpannedEncodingResult;

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
