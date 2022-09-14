use crate::encoder::errors::SpannedEncodingResult;
use rustc_hash::FxHashMap;
use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

#[derive(Default, Clone)]
pub(in super::super::super) struct SnapshotDomainsInfo {
    /// A map from a snapshot domain name to information about the snapshot domain.
    pub(in super::super::super) snapshot_domains: BTreeMap<String, SnapshotDomainInfo>,
    /// A map from a type to the name of the snapshot domain that represents the type.
    pub(in super::super::super) type_domains: FxHashMap<vir_low::Type, String>,
    pub(in super::super::super) bool_type: Option<vir_low::Type>,
}

#[derive(Default, Clone)]
pub(in super::super::super) struct SnapshotDomainInfo {
    /// The name of the domain function used to create constant values.
    pub(in super::super::super) constant_constructor_name: Option<String>,
    /// The name of the domain function used to destruct constant values.
    pub(in super::super::super) constant_destructor_name: Option<String>,
    /// The binary operators that correspond to the given domain functions.
    pub(in super::super::super) binary_operators: BTreeMap<String, vir_low::BinaryOpKind>,
    /// The unary operators that correspond to the given domain functions.
    pub(in super::super::super) unary_operators: BTreeMap<String, vir_low::UnaryOpKind>,
    /// The snapshot extensionality triggering functions.
    pub(in super::super::super) snapshot_equality: Option<String>,
}

impl SnapshotDomainsInfo {
    pub(in super::super) fn register_constant_constructor(
        &mut self,
        domain_name: &str,
        function_name: &str,
    ) -> SpannedEncodingResult<()> {
        let snapshot_domain = self.get_snapshot_domain(domain_name)?;
        if snapshot_domain.constant_constructor_name.is_none() {
            snapshot_domain.constant_constructor_name = Some(function_name.to_string());
        }
        Ok(())
    }

    pub(in super::super) fn register_constant_destructor(
        &mut self,
        domain_name: &str,
        function_name: &str,
    ) -> SpannedEncodingResult<()> {
        let snapshot_domain = self.get_snapshot_domain(domain_name)?;
        if snapshot_domain.constant_destructor_name.is_none() {
            snapshot_domain.constant_destructor_name = Some(function_name.to_string());
        }
        Ok(())
    }

    pub(in super::super) fn register_unary_operation(
        &mut self,
        domain_name: &str,
        op: vir_low::UnaryOpKind,
        function_name: String,
    ) -> SpannedEncodingResult<()> {
        let snapshot_domain = self.get_snapshot_domain(domain_name)?;
        assert!(snapshot_domain
            .unary_operators
            .insert(function_name, op)
            .is_none());
        Ok(())
    }

    pub(in super::super) fn register_binary_operation(
        &mut self,
        domain_name: &str,
        op: vir_low::BinaryOpKind,
        function_name: String,
    ) -> SpannedEncodingResult<()> {
        let snapshot_domain = self.get_snapshot_domain(domain_name)?;
        assert!(snapshot_domain
            .binary_operators
            .insert(function_name, op)
            .is_none());
        Ok(())
    }

    // FIXME: The visibility should be `pub(in super::super)`.
    pub(in super::super::super) fn register_snapshot_equality(
        &mut self,
        domain_name: &str,
        function_name: &str,
    ) -> SpannedEncodingResult<()> {
        let snapshot_domain = self.get_snapshot_domain(domain_name)?;
        if snapshot_domain.snapshot_equality.is_none() {
            snapshot_domain.snapshot_equality = Some(function_name.to_string());
            self.type_domains.insert(
                vir_low::Type::domain(domain_name.to_string()),
                domain_name.to_string(),
            );
        }
        Ok(())
    }

    fn get_snapshot_domain(
        &mut self,
        domain_name: &str,
    ) -> SpannedEncodingResult<&mut SnapshotDomainInfo> {
        Ok(self
            .snapshot_domains
            .entry(domain_name.to_string())
            .or_default())
    }
}
