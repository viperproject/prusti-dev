use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lifetimes::LifetimesInterface,
        lowerer::{DomainsLowererInterface, Lowerer},
    },
};
use std::collections::hash_map::Entry;
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle::{self as vir_mid},
};

trait Private {
    fn register_type_domain(
        &mut self,
        ty: &vir_mid::Type,
        low_ty: &vir_low::Type,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn register_type_domain(
        &mut self,
        ty: &vir_mid::Type,
        low_ty: &vir_low::Type,
    ) -> SpannedEncodingResult<()> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let entry = self.snapshots_state.type_domains.entry(low_ty.clone());
        match entry {
            Entry::Occupied(value) => {
                assert_eq!(value.get(), &domain_name);
            }
            Entry::Vacant(vacant) => {
                vacant.insert(domain_name);
            }
        }
        Ok(())
    }
}

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
    fn get_non_primitive_domain(&mut self, ty: &vir_low::Type) -> Option<&str>;
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
                let low_ty = vir_low::Type::seq(enc_elem);
                self.register_type_domain(ty, &low_ty)?;
                Ok(low_ty)
            }
            vir_mid::Type::Map(map) => {
                let enc_key = self.encode_snapshot_domain_type(&map.key_type)?;
                let enc_val = self.encode_snapshot_domain_type(&map.val_type)?;
                let low_ty = vir_low::Type::map(enc_key, enc_val);
                self.register_type_domain(ty, &low_ty)?;
                Ok(low_ty)
            }
            vir_mid::Type::Array(array) => {
                let enc_elem = self.encode_snapshot_domain_type(&array.element_type)?;
                let low_ty = vir_low::Type::seq(enc_elem);
                self.register_type_domain(ty, &low_ty)?;
                Ok(low_ty)
            }
            _ => {
                let domain_name = self.encode_snapshot_domain_name(ty)?;
                let low_ty = self.domain_type(domain_name)?;
                self.register_type_domain(ty, &low_ty)?;
                Ok(low_ty)
            }
        }
    }
    fn get_non_primitive_domain(&mut self, ty: &vir_low::Type) -> Option<&str> {
        self.snapshots_state
            .type_domains
            .get(ty)
            .map(String::as_str)
    }
}
