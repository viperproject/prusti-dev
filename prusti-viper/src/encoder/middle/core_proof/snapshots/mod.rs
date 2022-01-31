use super::lowerer::Lowerer;
use crate::encoder::errors::SpannedEncodingResult;

mod expression;
mod interface;
mod ty;
mod variable;

pub(super) use self::interface::{SnapshotsInterface, SnapshotsState};

pub(super) trait IntoSnapshot {
    type Target;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target>;
}
