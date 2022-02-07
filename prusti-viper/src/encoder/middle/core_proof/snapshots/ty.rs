use super::{IntoSnapshot, SnapshotsInterface};
use crate::encoder::{errors::SpannedEncodingResult, middle::core_proof::lowerer::Lowerer};
use vir_crate::{
    low as vir_low,
    middle::{self as vir_mid},
};

impl IntoSnapshot for vir_mid::Type {
    type Target = vir_low::Type;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        // This ensures that the domain is included into the program.
        lowerer.encode_snapshot_domain(self)
    }
}
