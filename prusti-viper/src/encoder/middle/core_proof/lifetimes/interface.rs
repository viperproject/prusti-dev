use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::{DomainsLowererInterface, Lowerer, PredicatesLowererInterface},
        snapshots::IntoProcedureSnapshot,
    },
};
use vir_crate::{low as vir_low, middle as vir_mid};

#[derive(Default)]
pub(in super::super) struct LifetimesState {
    is_lifetime_token_encoded: bool,
}

pub(in super::super) trait LifetimesInterface {
    fn lifetime_domain_name(&self) -> SpannedEncodingResult<String>;
    fn lifetime_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn encode_lifetime_token_predicate(&mut self) -> SpannedEncodingResult<()>;
    fn encode_lifetime_const_into_variable(
        &mut self,
        lifetime: vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn extract_lifetime_variables(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>>;
    fn extract_lifetime_variables_as_expr(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>>;
}

impl<'p, 'v: 'p, 'tcx: 'v> LifetimesInterface for Lowerer<'p, 'v, 'tcx> {
    fn lifetime_domain_name(&self) -> SpannedEncodingResult<String> {
        Ok("Lifetime".to_string())
    }

    fn lifetime_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type(self.lifetime_domain_name()?)
    }

    fn encode_lifetime_token_predicate(&mut self) -> SpannedEncodingResult<()> {
        if !self.lifetimes_state.is_lifetime_token_encoded {
            self.lifetimes_state.is_lifetime_token_encoded = true;
            let predicate = vir_low::PredicateDecl::new(
                "LifetimeToken",
                vec![vir_low::VariableDecl::new(
                    "lifetime",
                    self.lifetime_type()?,
                )],
                None,
            );
            self.declare_predicate(predicate)?;
            let predicate = vir_low::PredicateDecl::new(
                "DeadLifetimeToken",
                vec![vir_low::VariableDecl::new(
                    "lifetime",
                    self.lifetime_type()?,
                )],
                None,
            );
            self.declare_predicate(predicate)?;
        }
        Ok(())
    }

    fn encode_lifetime_const_into_variable(
        &mut self,
        lifetime: vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let lifetime_variable = vir_mid::VariableDecl::new(lifetime.name, vir_mid::Type::Lifetime);
        lifetime_variable.to_procedure_snapshot(self)
    }

    fn extract_lifetime_variables(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>> {
        let mut lifetimes = Vec::new();
        for lifetime in ty.get_lifetimes() {
            lifetimes.push(self.encode_lifetime_const_into_variable(lifetime)?);
        }
        Ok(lifetimes)
    }

    fn extract_lifetime_variables_as_expr(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        Ok(self
            .extract_lifetime_variables(ty)?
            .into_iter()
            .map(|lifetime| lifetime.into())
            .collect())
    }
}
