use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::{DomainsLowererInterface, Lowerer},
        predicates_memory_block::PredicatesMemoryBlockInterface,
        snapshots::SnapshotDomainsInterface,
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle::{self as vir_mid},
};

pub(in super::super::super) trait SnapshotBytesInterface {
    fn encode_snapshot_to_bytes_function(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> SnapshotBytesInterface for Lowerer<'p, 'v, 'tcx> {
    fn encode_snapshot_to_bytes_function(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        if !self.snapshots_state.encoded_to_bytes.contains(ty) {
            self.snapshots_state.encoded_to_bytes.insert(ty.clone());
            let domain_name = self.encode_snapshot_domain_name(ty)?;
            let domain_type = self.encode_snapshot_domain_type(ty)?;
            let return_type = self.bytes_type()?;
            self.declare_domain_function(
                &domain_name,
                std::borrow::Cow::Owned(format!("to_bytes${}", ty.get_identifier())),
                std::borrow::Cow::Owned(vec![vir_low::VariableDecl::new("snapshot", domain_type)]),
                std::borrow::Cow::Owned(return_type),
            )?;
        }
        Ok(())
    }
}
