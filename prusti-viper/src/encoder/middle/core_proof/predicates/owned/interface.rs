use super::encoder::PredicateEncoder;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lifetimes::LifetimesInterface, lowerer::Lowerer, snapshots::SnapshotValidityInterface,
        type_layouts::TypeLayoutsInterface, types::TypesInterface,
    },
};
use rustc_hash::FxHashSet;
use vir_crate::{
    low::{self as vir_low},
    middle as vir_mid,
    middle::operations::lifetimes::WithLifetimes,
};

#[derive(Default)]
pub(in super::super) struct PredicatesOwnedState {
    unfolded_owned_non_aliased_predicates: FxHashSet<vir_mid::Type>,
}

pub(in super::super::super) trait PredicatesOwnedInterface {
    /// Marks that `OwnedNonAliased<ty>` was unfolded in the program and we need
    /// to provide its body.
    fn mark_owned_non_aliased_as_unfolded(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    fn collect_owned_predicate_decls(
        &mut self,
    ) -> SpannedEncodingResult<Vec<vir_low::PredicateDecl>>;
    fn acc_owned_non_aliased(
        &mut self,
        ty: &vir_mid::Type,
        place: impl Into<vir_low::Expression>,
        root_address: impl Into<vir_low::Expression>,
        snapshot: impl Into<vir_low::Expression>,
        lifetimes: Vec<impl Into<vir_low::Expression>>,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn extract_lifetime_arguments_from_rvalue(
        &mut self,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>>;
    fn extract_lifetime_arguments_from_rvalue_as_expr(
        &mut self,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>>;
    fn extract_non_type_arguments_from_type(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>>;
    fn extract_non_type_arguments_from_type_excluding_lifetimes(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>>;
    fn extract_non_type_parameters_from_type(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>>;
    fn extract_non_type_parameters_from_type_as_exprs(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>>;
    fn extract_non_type_parameters_from_type_validity(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>>;
    /// FIXME: Array length should be per operand/target, and not just a global value.
    fn array_length_variable(&mut self) -> SpannedEncodingResult<vir_low::VariableDecl>;
}

impl<'p, 'v: 'p, 'tcx: 'v> PredicatesOwnedInterface for Lowerer<'p, 'v, 'tcx> {
    fn mark_owned_non_aliased_as_unfolded(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        if !self
            .predicates_encoding_state
            .owned
            .unfolded_owned_non_aliased_predicates
            .contains(ty)
        {
            self.ensure_type_definition(ty)?;
            self.predicates_encoding_state
                .owned
                .unfolded_owned_non_aliased_predicates
                .insert(ty.clone());
        }
        Ok(())
    }

    fn collect_owned_predicate_decls(
        &mut self,
    ) -> SpannedEncodingResult<Vec<vir_low::PredicateDecl>> {
        if self.only_check_specs() {
            Ok(Vec::new())
        } else {
            let unfolded_predicates = std::mem::take(
                &mut self
                    .predicates_encoding_state
                    .owned
                    .unfolded_owned_non_aliased_predicates,
            );
            let mut predicate_encoder = PredicateEncoder::new(self, &unfolded_predicates);
            for ty in &unfolded_predicates {
                predicate_encoder.encode_owned_non_aliased(ty)?;
            }
            Ok(predicate_encoder.into_predicates())
        }
    }

    fn acc_owned_non_aliased(
        &mut self,
        ty: &vir_mid::Type,
        place: impl Into<vir_low::Expression>,
        root_address: impl Into<vir_low::Expression>,
        snapshot: impl Into<vir_low::Expression>,
        lifetimes: Vec<impl Into<vir_low::Expression>>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        let mut arguments = vec![place.into(), root_address.into(), snapshot.into()];
        arguments.extend(lifetimes.into_iter().map(|lifetime| lifetime.into()));
        Ok(vir_low::Expression::predicate_access_predicate_no_pos(
            predicate_name! { OwnedNonAliased<ty> },
            arguments,
            vir_low::Expression::full_permission(),
        ))
    }

    fn extract_lifetime_arguments_from_rvalue(
        &mut self,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>> {
        let mut lifetimes = Vec::new();
        for lifetime in value.get_lifetimes() {
            lifetimes.push(self.encode_lifetime_const_into_variable(lifetime)?);
        }
        Ok(lifetimes)
    }

    fn extract_lifetime_arguments_from_rvalue_as_expr(
        &mut self,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        let lifetimes = self
            .extract_lifetime_arguments_from_rvalue(value)?
            .iter()
            .cloned()
            .map(|x| x.into())
            .collect();
        Ok(lifetimes)
    }

    fn extract_non_type_arguments_from_type(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        let mut arguments = self.extract_lifetime_variables_as_expr(ty)?;
        if let vir_mid::Type::Array(ty) = ty {
            arguments.push(self.size_constant(ty.length)?);
        }
        Ok(arguments)
    }

    fn extract_non_type_arguments_from_type_excluding_lifetimes(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        if let vir_mid::Type::Array(ty) = ty {
            Ok(vec![self.size_constant(ty.length)?])
        } else {
            Ok(Vec::new())
        }
    }

    fn extract_non_type_parameters_from_type(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>> {
        // FIXME: Figure out how to avoid these magic variable names.
        let parameters = match ty {
            vir_mid::Type::Array(_) => {
                vec![self.array_length_variable()?]
            }
            _ => Vec::new(),
        };
        Ok(parameters)
    }

    fn extract_non_type_parameters_from_type_as_exprs(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        let parameters = self.extract_non_type_parameters_from_type(ty)?;
        Ok(parameters
            .into_iter()
            .map(|parameter| parameter.into())
            .collect())
    }

    fn extract_non_type_parameters_from_type_validity(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        let validity_calls = match ty {
            vir_mid::Type::Array(_) => {
                let variable = self.array_length_variable()?;
                let size_type = &self.size_type_mid()?;
                vec![self.encode_snapshot_valid_call_for_type(variable.into(), size_type)?]
            }
            _ => Vec::new(),
        };
        Ok(validity_calls)
    }

    fn array_length_variable(&mut self) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl::new(
            "array_length",
            self.size_type()?,
        ))
    }
}
