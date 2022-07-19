use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::{DomainsLowererInterface, Lowerer},
        predicates::PredicatesMemoryBlockInterface,
        snapshots::SnapshotDomainsInterface,
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle::{self as vir_mid},
};

pub(in super::super::super) trait SnapshotBytesInterface {
    /// Encodes the `to_bytes` function. For types without pointers and
    /// references `to_bytes` is a bijection from the snapshot into byte
    /// representation of the value (simply speaking a snapshot is just “typed
    /// bytes”). However, for types with references and pointers, `to_bytes` is
    /// not a bijection because it maps only the values of the main memory
    /// block. Simply speaking, for a value allocated on a stack, `to_bytes`
    /// maps only the part of the memory that is on the stack.
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
        // Before editing this, please read the documentation on the trait
        // method.
        if !self.snapshots_state.encoded_to_bytes.contains(ty) {
            self.snapshots_state.encoded_to_bytes.insert(ty.clone());
            let domain_name = self.encode_snapshot_domain_name(ty)?;
            let domain_type = self.encode_snapshot_domain_type(ty)?;
            let return_type = self.bytes_type()?;
            self.declare_domain_function(
                &domain_name,
                std::borrow::Cow::Owned(format!("to_bytes${}", ty.get_identifier())),
                false,
                std::borrow::Cow::Owned(vec![vir_low::VariableDecl::new("snapshot", domain_type)]),
                std::borrow::Cow::Owned(return_type),
            )?;
        }
        Ok(())
    }
}
