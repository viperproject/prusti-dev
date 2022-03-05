use super::IntoSnapshot;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{lowerer::Lowerer, snapshots::SnapshotVariablesInterface},
};
use vir_crate::{
    low::{self as vir_low},
    middle::{self as vir_mid},
};

impl IntoSnapshot for vir_mid::VariableDecl {
    type Target = vir_low::VariableDecl;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        lowerer.current_snapshot_variable_version(self)
    }
}
