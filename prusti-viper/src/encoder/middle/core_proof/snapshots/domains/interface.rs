use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lifetimes::LifetimesInterface,
        lowerer::{DomainsLowererInterface, Lowerer},
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle::{self as vir_mid},
};

pub(in super::super::super) trait SnapshotDomainsInterface {
    fn encode_snapshot_domain_name(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<String>;
    fn encode_snapshot_domain_type(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Type>;
    fn try_decoding_snapshot_type(
        &self,
        domain_name: &str,
    ) -> SpannedEncodingResult<Option<vir_mid::Type>>;
}

impl<'p, 'v: 'p, 'tcx: 'v> SnapshotDomainsInterface for Lowerer<'p, 'v, 'tcx> {
    /// Note: Even though we directly use Viper maps and sequences as snapshots
    /// for `vir_mid::Type::Map(_)` and `vir_mid::Type::Sequence(_)`
    /// respectively, we still need a domain in which we put their custom
    /// `validity` and `to_bytes` functions.
    fn encode_snapshot_domain_name(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<String> {
        assert!(
            !matches!(
                ty,
                vir_mid::Type::MBool | vir_mid::Type::MInt | vir_mid::Type::MPerm
            ),
            "ty: {}",
            ty
        );
        let domain_name = if ty == &vir_mid::Type::Lifetime {
            self.lifetime_domain_name()?
        } else {
            format!("Snap${}", ty.get_identifier())
        };
        if !self.snapshots_state.domain_types.contains_key(&domain_name) {
            self.snapshots_state
                .domain_types
                .insert(domain_name.clone(), ty.clone());
        }
        Ok(domain_name)
    }
    fn try_decoding_snapshot_type(
        &self,
        domain_name: &str,
    ) -> SpannedEncodingResult<Option<vir_mid::Type>> {
        Ok(self.snapshots_state.domain_types.get(domain_name).cloned())
    }
    fn encode_snapshot_domain_type(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Type> {
        match ty {
            vir_mid::Type::MBool => Ok(vir_low::Type::Bool),
            vir_mid::Type::MInt => Ok(vir_low::Type::Int),
            vir_mid::Type::MPerm => Ok(vir_low::Type::Perm),
            vir_mid::Type::Sequence(seq) => {
                let enc_elem = self.encode_snapshot_domain_type(&seq.element_type)?;
                Ok(vir_low::Type::seq(enc_elem))
            }
            vir_mid::Type::Map(map) => {
                let enc_key = self.encode_snapshot_domain_type(&map.key_type)?;
                let enc_val = self.encode_snapshot_domain_type(&map.val_type)?;

                Ok(vir_low::Type::map(enc_key, enc_val))
            }
            _ => {
                let domain_name = self.encode_snapshot_domain_name(ty)?;
                self.domain_type(domain_name)
            }
        }
    }
}
