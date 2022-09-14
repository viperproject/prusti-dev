use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::{DomainsLowererInterface, Lowerer},
        predicates::PredicatesMemoryBlockInterface,
        snapshots::SnapshotDomainsInterface,
    },
};
use prusti_common::config;
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
            let to_bytes = format!("to_bytes${}", ty.get_identifier());
            let snapshot = vir_low::VariableDecl::new("snapshot", domain_type.clone());
            self.declare_domain_function(
                &domain_name,
                std::borrow::Cow::Owned(to_bytes.clone()),
                false,
                std::borrow::Cow::Owned(vec![snapshot.clone()]),
                std::borrow::Cow::Owned(return_type.clone()),
            )?;
            if !config::use_snapshot_parameters_in_predicates()
                && matches!(
                    ty,
                    vir_mid::Type::Bool
                        | vir_mid::Type::Int(_)
                        | vir_mid::Type::Float(_)
                        | vir_mid::Type::Pointer(_)
                        | vir_mid::Type::Sequence(_)
                        | vir_mid::Type::Map(_)
                )
            {
                // This is sound only for primitive types.
                let from_bytes = format!("from_bytes${}", ty.get_identifier());
                self.declare_domain_function(
                    &domain_name,
                    std::borrow::Cow::Owned(from_bytes.clone()),
                    false,
                    std::borrow::Cow::Owned(vec![vir_low::VariableDecl::new(
                        "bytes",
                        return_type.clone(),
                    )]),
                    std::borrow::Cow::Owned(domain_type.clone()),
                )?;

                let to_bytes_call = vir_low::Expression::domain_function_call(
                    domain_name.clone(),
                    to_bytes,
                    vec![snapshot.clone().into()],
                    return_type,
                );
                let from_bytes_call = vir_low::Expression::domain_function_call(
                    domain_name.clone(),
                    from_bytes,
                    vec![to_bytes_call.clone()],
                    domain_type,
                );
                // let body = vir_low::Expression::forall(
                //     vec![snapshot.clone()],
                //     vec![vir_low::Trigger::new(vec![to_bytes_call])],
                //     expr! {
                //         snapshot == [ from_bytes_call ]
                //     },
                // );
                let axiom = vir_low::DomainRewriteRuleDecl {
                    // We use ty identifier to distinguish sequences from arrays.
                    name: format!("{}${}$to_bytes_injective", domain_name, ty.get_identifier()),
                    comment: None,
                    egg_only: false,
                    variables: vec![snapshot.clone()],
                    triggers: Some(vec![vir_low::Trigger::new(vec![to_bytes_call])]),
                    source: snapshot.into(),
                    target: from_bytes_call,
                };
                self.declare_rewrite_rule(&domain_name, axiom)?;
            }
        }
        Ok(())
    }
}
