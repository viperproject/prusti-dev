//! The trait `IntoSnapshot` and its implementations.

mod expression;
mod ty;
mod variable;

use super::super::lowerer::Lowerer;
use crate::encoder::errors::SpannedEncodingResult;

pub(in super::super) trait IntoSnapshot {
    type Target;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target>;
}
